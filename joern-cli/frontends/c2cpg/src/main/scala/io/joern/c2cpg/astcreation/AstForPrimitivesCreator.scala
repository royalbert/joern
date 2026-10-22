package io.joern.c2cpg.astcreation

import io.joern.c2cpg.passes.AstCreationPass
import io.joern.x2cpg.Ast
import io.shiftleft.codepropertygraph.generated.nodes.{NewCall, NewMethod, NewMethodRef, NewTypeDecl}
import io.shiftleft.codepropertygraph.generated.{DispatchTypes, EvaluationStrategies, Operators}
import org.apache.commons.lang3.StringUtils
import org.eclipse.cdt.core.dom.ast.*
import org.eclipse.cdt.core.dom.ast.cpp.{
  ICPPASTNamespaceDefinition,
  ICPPBinding,
  ICPPClassType,
  ICPPConstructor,
  ICPPEnumeration,
  ICPPFunction,
  ICPPNamespace,
  ICPPNamespaceAlias,
  ICPPTemplateTypeParameter
}
import org.eclipse.cdt.internal.core.dom.parser.IASTInternalScope
import org.eclipse.cdt.internal.core.dom.parser.c.{CEnumerator, CVariable, ICInternalBinding}
import org.eclipse.cdt.internal.core.dom.parser.cpp.*
import org.eclipse.cdt.internal.core.dom.parser.cpp.semantics.{CPPVisitor, EvalMemberAccess}
import org.eclipse.cdt.internal.core.model.ASTStringUtil

import scala.annotation.tailrec

trait AstForPrimitivesCreator { this: AstCreator =>

  import FullNameProvider.stripTemplateTags

  /** The references to other files' enumerators this file registered, so that a copy of one is registered too. */
  private val enumeratorReferences = new java.util.IdentityHashMap[NewCall, AstCreationPass.EnumeratorReference]()

  protected def astForComment(comment: IASTComment): Ast =
    Ast(commentNode(comment, code(comment), fileName(comment)))

  protected def astForLiteral(lit: IASTLiteralExpression): Ast = {
    val codeString = code(lit)
    val tpe        = registerType(safeGetType(lit.getExpressionType))
    if (codeString == Defines.This) {
      val thisIdentifier = identifierNode(lit, codeString, codeString, tpe)
      scope.addVariableReference(codeString, thisIdentifier, tpe, EvaluationStrategies.BY_SHARING)
      Ast(thisIdentifier)
    } else {
      Ast(literalNode(lit, codeString, tpe))
    }
  }

  private def globalTagFromDefinition(ident: IASTNode): String = {
    @tailrec
    def isGlobal(node: IASTNode): Boolean = {
      node match {
        case _: IASTTranslationUnit        => true
        case n: ICPPASTNamespaceDefinition => isGlobal(n.getParent)
        case _                             => false
      }
    }
    ident match {
      case id: IASTIdExpression =>
        safeGetBinding(id.getName) match {
          case Some(binding: (CPPVariable | CVariable)) =>
            safeCdtCall(binding.getScope)
              .collect {
                case n: IASTInternalScope if isGlobal(n.getPhysicalNode) => s"${Defines.GlobalTag} "
              }
              .getOrElse("")
          case Some(p: IProblemBinding)
              if p.getID == ISemanticProblem.BINDING_NOT_FOUND ||
                p.getID == ISemanticProblem.BINDING_AMBIGUOUS_LOOKUP ||
                p.getID == ISemanticProblem.BINDING_BAD_SCOPE ||
                p.getID == ISemanticProblem.BINDING_MEMBER_DECLARATION_NOT_FOUND ||
                p.getID == ISemanticProblem.BINDING_DEFINITION_NOT_FOUND =>
            s"${Defines.UnknownTag} "
          case _ => ""
        }
      case _ => ""
    }
  }

  protected def astForIdentifier(ident: IASTNode): Ast = {
    maybeMethodRefForIdentifier(ident) match {
      case Some(ref) => Ast(ref)
      case None      =>
        val identifierName = nameForIdentifier(ident)
        maybeAstForEnumMemberAccess(ident, identifierName).orElse(
          maybeAstForIncludedEnumMemberAccess(ident, identifierName)
        ) match {
          case Some(ast) => ast
          case None      =>
            typeNameForIdentifier(ident, identifierName) match {
              case identifierTypeName: String =>
                val tpe       = registerType(identifierTypeName)
                val globalTag = globalTagFromDefinition(ident)
                val node      = identifierNode(ident, identifierName, s"$globalTag${code(ident)}", tpe)
                scope.addVariableReference(identifierName, node, tpe, EvaluationStrategies.BY_REFERENCE)
                Ast(node)
              case ast: Ast => ast
            }
        }
    }
  }

  /** Enum constant references are lowered as field accesses on the enclosing enum type, mirroring how qualified
    * accesses (`X::a`) are represented. The post-frontend `FieldAccessLinkerPass` links the access to the member.
    */
  private def maybeAstForEnumMemberAccess(ident: IASTNode, identifierName: String): Option[Ast] = {
    val binding = ident match {
      case id: IASTIdExpression => safeGetBinding(id)
      case id: IASTName         => safeGetBinding(id)
      case _                    => None
    }
    binding.flatMap(enumMembers.get).map { enumMember =>
      val op     = Operators.fieldAccess
      val base   = typeRefNode(ident, enumMember.typeName, enumMember.typeFullName)
      val field  = fieldIdentifierNode(ident, identifierName, identifierName)
      val access =
        callNode(ident, code(ident), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(enumMember.member.typeFullName))
      callAst(access, List(Ast(base), Ast(field)))
    }
  }

  /** Enum constant references whose enum another file declares (mostly a header the file includes) are lowered as
    * [[maybeAstForEnumMemberAccess]] lowers those of the file's own enums. That file's AST creator makes the enum's
    * member, which this one cannot reach. CDT binds the reference to the enumerator, whose declaration is in the
    * declaring file: the access names the type that file's AST creator gives the enum, read from that declaration, and
    * is registered under the place of the declaration, where `EnumeratorReferenceLinkerPass` finds the member.
    */
  private def maybeAstForIncludedEnumMemberAccess(ident: IASTNode, identifierName: String): Option[Ast] = {
    val binding = ident match {
      case id: IASTIdExpression => safeGetBinding(id)
      case id: IASTName         => safeGetBinding(id)
      case _                    => None
    }
    for {
      enumerator <- binding.flatMap(enumeratorDeclaration)
      if isIncludedNode(enumerator)
      names <- enumMemberNamesFromDeclaration(enumerator)
    } yield {
      val op     = Operators.fieldAccess
      val base   = typeRefNode(ident, names.typeName, names.typeFullName)
      val field  = fieldIdentifierNode(ident, identifierName, identifierName)
      val access =
        callNode(ident, code(ident), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(names.memberTypeFullName))
      enumeratorPlace(enumerator).foreach { place =>
        registerEnumeratorReference(AstCreationPass.EnumeratorReference(access, place, isCppFile))
      }
      callAst(access, List(Ast(base), Ast(field)))
    }
  }

  private def registerEnumeratorReference(reference: AstCreationPass.EnumeratorReference): Unit = {
    enumeratorReferences.put(reference.access, reference)
    accumulator.registerEnumeratorReference(reference)
  }

  /** Registers the copies in `copies` of the references to other files' enumerators in `original`: a macro call's
    * arguments are copies (`Ast.subTreeCopy`) of subtrees of its expansion. A copy keeps the code and the position of
    * its original, and within one expansion a reference with that code at that position is one token of the source, so
    * it refers to the same enumerator.
    */
  protected def registerCopiedEnumeratorReferences(original: Ast, copies: Ast): Unit = {
    if (!enumeratorReferences.isEmpty) {
      val originals = original.nodes
        .collect { case access: NewCall if enumeratorReferences.containsKey(access) => access }
        .groupBy(access => (access.code, access.lineNumber, access.columnNumber))
      if (originals.nonEmpty) {
        copies.nodes.foreach {
          case copy: NewCall if copy.name == Operators.fieldAccess && !enumeratorReferences.containsKey(copy) =>
            originals.get((copy.code, copy.lineNumber, copy.columnNumber)).foreach { sameToken =>
              registerEnumeratorReference(enumeratorReferences.get(sameToken.head).copy(access = copy))
            }
          case _ =>
        }
      }
    }
  }

  private def enumeratorDeclaration(binding: IBinding): Option[IASTEnumerationSpecifier.IASTEnumerator] = {
    val enumeratorName = binding match {
      case enumerator: CEnumerator   => Option(enumerator.getPhysicalNode)
      case enumerator: CPPEnumerator => Option(enumerator.getDefinition)
      case _                         => None
    }
    enumeratorName.map(_.getParent).collect { case declaration: IASTEnumerationSpecifier.IASTEnumerator => declaration }
  }

  private def maybeMethodRefForIdentifier(ident: IASTNode): Option[NewMethodRef] = {
    ident match {
      case id: IASTIdExpression if id.getName != null =>
        val (mayBeFullName, mayBeTypeFullName) = safeGetBinding(id) match {
          case Some(binding: ICInternalBinding) if binding.getDefinition.isInstanceOf[IASTFunctionDeclarator] =>
            namesForBinding(binding)
          case Some(binding: ICInternalBinding)
              if binding.getDeclarations != null &&
                binding.getDeclarations.exists(_.isInstanceOf[IASTFunctionDeclarator]) =>
            namesForBinding(binding)
          case Some(binding: ICPPInternalBinding) if binding.getDefinition.isInstanceOf[IASTFunctionDeclarator] =>
            namesForBinding(binding)
          case Some(binding: ICPPInternalBinding)
              if binding.getDeclarations != null &&
                binding.getDeclarations.exists(_.isInstanceOf[CPPASTFunctionDeclarator]) =>
            namesForBinding(binding)
          case _ => (None, None)
        }
        for {
          fullName     <- mayBeFullName
          typeFullName <- mayBeTypeFullName
        } yield methodRefNode(ident, code(ident), fullName, registerType(typeFullName))
      case _ => None
    }
  }

  private def namesForBinding(binding: ICInternalBinding | ICPPInternalBinding): (Option[String], Option[String]) = {
    val definition = binding match {
      // sadly, there is no common interface
      case b: ICInternalBinding if b.getDefinition.isInstanceOf[IASTFunctionDeclarator] =>
        Some(b.getDefinition.asInstanceOf[IASTFunctionDeclarator])
      case b: ICPPInternalBinding if b.getDefinition.isInstanceOf[IASTFunctionDeclarator] =>
        Some(b.getDefinition.asInstanceOf[IASTFunctionDeclarator])
      case b: ICInternalBinding   => b.getDeclarations.find(_.isInstanceOf[IASTFunctionDeclarator])
      case b: ICPPInternalBinding => b.getDeclarations.find(_.isInstanceOf[IASTFunctionDeclarator])
      case null                   => None
    }
    val typeFullName = definition.map(_.getParent) match {
      case Some(d: IASTFunctionDefinition) => Some(typeForDeclSpecifier(d.getDeclSpecifier))
      case Some(d: IASTSimpleDeclaration)  => Some(typeForDeclSpecifier(d.getDeclSpecifier))
      case _                               => None
    }
    (definition.map(fullName), typeFullName)
  }

  protected def nameForIdentifier(ident: IASTNode): String = {
    ident match {
      case id: IASTElaboratedTypeSpecifier => shortName(id)
      case id: IASTNamedTypeSpecifier      => shortName(id)
      case id: IASTIdExpression            => shortName(id)
      case id: IASTName                    =>
        val name = stripTemplateTags(ASTStringUtil.getSimpleName(id))
        if (name.isEmpty) safeGetBinding(id).map(_.getName).getOrElse(scopeLocalUniqueName(""))
        else name
      case _ => code(ident)
    }
  }

  private def typeNameForIdentifier(ident: IASTNode, identifierName: String): String | Ast = {
    val variableOption = scope.lookupVariable(identifierName)
    variableOption match {
      case Some((_, variableTypeName)) => variableTypeName
      case None if ident.isInstanceOf[IASTName] && safeCdtCall(ident.asInstanceOf[IASTName].getBinding).isDefined =>
        val idBinding = safeCdtCall(ident.asInstanceOf[IASTName].getBinding)
        idBinding match {
          case Some(v: IVariable) =>
            safeCdtCall(v.getType) match {
              case Some(f: IFunctionType) => cleanType(safeGetType(f.getReturnType))
              case Some(other)            => cleanType(safeGetType(other))
              case None                   => Defines.Any
            }
          case Some(other) => cleanType(other.getName)
          case None        => Defines.Any
        }
      case None if ident.isInstanceOf[IASTName] =>
        typeFor(ident.getParent)
      case None if ident.isInstanceOf[CPPASTIdExpression] =>
        syntheticThisAccess(ident.asInstanceOf[CPPASTIdExpression], identifierName)
      case None => typeFor(ident)
    }
  }

  private def syntheticThisAccess(ident: CPPASTIdExpression, identifierName: String): String | Ast = {
    val tpe = safeGetBinding(ident.getName) match {
      case Some(f: CPPField) => safeCdtCall(safeGetType(f.getType)).getOrElse(Defines.Any)
      case _                 => typeFor(ident)
    }
    safeCdtCall(ident.getEvaluation) match {
      case Some(e: EvalMemberAccess) =>
        val ownerTypeRaw = safeGetType(e.getOwnerType)
        val deref        = if (e.isPointerDeref) "*" else ""
        val ownerType    = registerType(s"$ownerTypeRaw$deref")
        if (isInCurrentScope(ident, ownerTypeRaw)) {
          scope.lookupVariable(Defines.This) match {
            case Some(_) =>
              val (op, code) = if (e.isPointerDeref) {
                (Operators.indirectFieldAccess, s"${Defines.This}->$identifierName")
              } else {
                (Operators.fieldAccess, s"${Defines.This}.$identifierName")
              }
              val thisIdentifier = identifierNode(ident, Defines.This, Defines.This, ownerType)
              scope.addVariableReference(Defines.This, thisIdentifier, ownerType, EvaluationStrategies.BY_SHARING)
              val member  = fieldIdentifierNode(ident, identifierName, identifierName)
              val callTpe = Some(registerType(tpe))
              val ma      = callNode(ident, code, op, op, DispatchTypes.STATIC_DISPATCH, None, callTpe)
              callAst(ma, Seq(Ast(thisIdentifier), Ast(member)))
            case None => tpe
          }
        } else tpe
      case _ => tpe
    }
  }

  private def isInCurrentScope(ident: CPPASTIdExpression, owner: String): Boolean = {
    val ownerWithOutTemplateTags = owner.takeWhile(_ != '<')
    val isInMethodScope          =
      safeCdtCall(CPPVisitor.getContainingScope(ident).getScopeName.toString).exists(scopeName =>
        scopeName.startsWith(s"$ownerWithOutTemplateTags::") || scopeName.contains(s"::$ownerWithOutTemplateTags::")
      )
    isInMethodScope || methodAstParentStack.collectFirst {
      case typeDecl: NewTypeDecl if typeDecl.fullName == ownerWithOutTemplateTags    => typeDecl
      case method: NewMethod if method.fullName.startsWith(ownerWithOutTemplateTags) => method
    }.nonEmpty
  }

  protected def astForFieldReference(fieldRef: IASTFieldReference): Ast = {
    val isInConstructor =
      safeCdtCall(CPPVisitor.findEnclosingFunctionOrClass(fieldRef)).exists(_.isInstanceOf[ICPPConstructor])
    val dispatchType = DispatchTypes.STATIC_DISPATCH
    val isDeref      = fieldRef.isPointerDereference && !isInConstructor
    val op           = if (isDeref) Operators.indirectFieldAccess else Operators.fieldAccess
    val ma           = callNode(fieldRef, code(fieldRef), op, op, dispatchType, None, Some(Defines.Any))
    val owner        = astForExpression(fieldRef.getFieldOwner)
    val memberName   = fieldRef.getFieldName.toString
    val member       = fieldIdentifierNode(fieldRef, memberName, memberName)
    callAst(ma, List(owner, Ast(member)))
  }

  protected def astForArrayModifier(arrMod: IASTArrayModifier): Ast = {
    nullSafeAst(arrMod.getConstantExpression)
  }

  private def qualifiedNameOf(binding: ICPPBinding): Option[String] =
    safeCdtCall(binding.getQualifiedName.mkString("."))

  /** Allowlist of binding kinds that may appear as a qualifier and be turned into a TYPE_REF. */
  private def qualifiedNameForBinding(binding: IBinding): Option[String] = binding match {
    case _: IProblemBinding           => None
    case t: ICPPClassType             => qualifiedNameOf(t)
    case t: ICPPEnumeration           => qualifiedNameOf(t)
    case t: (ITypedef & ICPPBinding)  => qualifiedNameOf(t)
    case t: ICPPTemplateTypeParameter => safeCdtCall(t.getName)
    case alias: ICPPNamespaceAlias    => resolveNamespaceAlias(alias).flatMap(qualifiedNameOf)
    case ns: ICPPNamespace            => qualifiedNameOf(ns)
    case _                            => None
  }

  /** CDT's `getBinding` only resolves one hop, so alias chains (`namespace fs2 = fs;`) are followed here. */
  @tailrec
  private def resolveNamespaceAlias(
    alias: ICPPNamespaceAlias,
    seen: Set[ICPPNamespaceAlias] = Set.empty
  ): Option[ICPPNamespace] = {
    if (seen.contains(alias)) None
    else
      safeCdtCall(alias.getBinding) match {
        case Some(target: ICPPNamespaceAlias) => resolveNamespaceAlias(target, seen + alias)
        case Some(target: ICPPNamespace)      => Some(target)
        case _                                => None
      }
  }

  private def typeRefForQualifier(qualId: CPPASTQualifiedName): Option[Ast] = {
    qualId.getQualifier.lastOption.flatMap { lastQualifier =>
      safeCdtCall(lastQualifier.resolveBinding())
        .flatMap(qualifiedNameForBinding)
        .map(typeRefAst(qualId, lastQualifier, _))
    }
  }

  private def typeRefAst(qualId: CPPASTQualifiedName, lastQualifier: IASTNode, qualifiedName: String): Ast = {
    val fullName = stripTemplateTags(replaceQualifiedNameSeparator(qualifiedName))
    val codeStr  = qualId.getQualifier.map(code).mkString("::")
    Ast(typeRefNode(lastQualifier, codeStr, registerType(fullName)))
  }

  protected def astForQualifiedName(qualId: CPPASTQualifiedName): Ast = {
    safeGetBinding(qualId) match {
      case Some(function: ICPPFunction) =>
        val name      = qualId.getLastName.toString
        val signature = if (function.isExternC) "" else functionTypeToSignature(function.getType)
        val fullName  = if (function.isExternC) {
          StringUtils.normalizeSpace(name)
        } else {
          val fullNameNoSig = StringUtils.normalizeSpace(function.getQualifiedName.mkString("."))
          s"$fullNameNoSig:$signature"
        }
        val functionType = cleanType(safeGetType(function.getType))
        Ast(methodRefNode(qualId, name, fullName, registerType(functionType)))
      case _ =>
        val op           = Operators.fieldAccess
        val dispatchType = DispatchTypes.STATIC_DISPATCH
        val ma           = callNode(qualId, code(qualId), op, op, dispatchType, None, Some(Defines.Any))

        def fieldAccesses(names: List[IASTNode]): Ast = names match {
          case Nil          => Ast()
          case head :: Nil  => astForNode(head)
          case head :: tail =>
            val (resultAst, _) = tail.foldLeft((astForNode(head), code(head))) { case ((accAst, accCode), nameNode) =>
              val nameCode  = code(nameNode)
              val newCode   = s"$accCode::$nameCode"
              val callNode_ = callNode(names.head, newCode, op, op, dispatchType, None, Some(Defines.Any))
              val arg2      = Ast(fieldIdentifierNode(nameNode, nameCode, nameCode))
              (callAst(callNode_, List(accAst, arg2)), newCode)
            }
            resultAst
        }
        val qualifier = typeRefForQualifier(qualId).getOrElse(fieldAccesses(qualId.getQualifier.toIndexedSeq.toList))
        val owner     = if (qualifier != Ast()) { qualifier }
        else { Ast(literalNode(qualId.getLastName, "<global>", Defines.Any)) }
        val member = fieldIdentifierNode(
          qualId.getLastName,
          replaceQualifiedNameSeparator(qualId.getLastName.toString),
          qualId.getLastName.toString
        )
        callAst(ma, List(owner, Ast(member)))
    }
  }

}
