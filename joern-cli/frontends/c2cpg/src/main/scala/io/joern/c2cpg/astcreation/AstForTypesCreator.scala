package io.joern.c2cpg.astcreation

import io.joern.c2cpg.passes.AstCreationPass
import io.joern.x2cpg.Ast
import io.joern.x2cpg.datastructures.Stack.*
import io.joern.x2cpg.datastructures.VariableScopeManager
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.codepropertygraph.generated.{DispatchTypes, EdgeTypes, ModifierTypes, Operators}
import org.apache.commons.lang3.StringUtils
import org.eclipse.cdt.core.dom.ast.*
import org.eclipse.cdt.core.dom.ast.cpp.*
import org.eclipse.cdt.internal.core.dom.parser.cpp.{
  CPPASTAliasDeclaration,
  CPPASTQualifiedName,
  CPPASTSimpleDeclaration,
  CPPClosureType
}
import org.eclipse.cdt.internal.core.model.ASTStringUtil

import java.nio.file.Paths
import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.Try

trait AstForTypesCreator { this: AstCreator =>

  import FullNameProvider.*

  /** An enumerator's CPG member node together with the name and full name of the enclosing enum type declaration. */
  protected final case class EnumMemberInfo(member: NewMember, typeName: String, typeFullName: String)

  /** Maps CDT enumerator bindings to their CPG counterpart. References to an enumerator are lowered as field accesses
    * on the enum type; the binding identity (rather than the name) decides which member is referenced, which also
    * resolves shadowing between enums.
    */
  protected val enumMembers: mutable.Map[IBinding, EnumMemberInfo] = mutable.HashMap.empty

  /** The names of an enumerator's CPG member as the AST creator of the file declaring its enum gives them: the name and
    * full name of the enum type declaration, and the member's type full name.
    */
  protected final case class EnumMemberNames(typeName: String, typeFullName: String, memberTypeFullName: String)

  protected def astForDecltypeSpecifier(decl: ICPPASTDecltypeSpecifier): Ast = {
    val op       = Defines.OperatorTypeOf
    val cpgUnary =
      callNode(decl, code(decl), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(Defines.Any))
    val operand = nullSafeAst(decl.getDecltypeExpression)
    callAst(cpgUnary, List(operand))
  }

  protected def astForNamespaceAlias(namespaceAlias: ICPPASTNamespaceAlias): Ast = {
    // Namespace alias does not create any new AST nodes, so we return an empty AST here.
    // Ideally, we would create a namespace block node with an alias property, but that's not in the CPG schema.
    // Anyway, namespace aliases do not affect the AST structure. When used, CDT resolves them to the original namespace.
    Ast()
  }

  private def typeForIASTDeclarator(
    declaration: IASTSimpleDeclaration,
    declarator: IASTDeclarator,
    index: Int
  ): String = {
    declarator match {
      case arrayDecl: IASTArrayDeclarator => registerType(typeFor(arrayDecl))
      case _                              =>
        safeGetBinding(declarator.getName) match {
          case Some(variable: ICPPVariable) if safeCdtCall(variable.getType).exists(_.isInstanceOf[CPPClosureType]) =>
            registerType(Defines.Function)
          case _ =>
            registerType(typeForDeclSpecifier(declaration.getDeclSpecifier, index = index))
        }
    }
  }

  protected def astForDeclarator(declaration: IASTSimpleDeclaration, declarator: IASTDeclarator, index: Int): Ast = {
    val name = shortName(declarator)
    declaration match {
      case d if isTypeDef(d) && shortName(d.getDeclSpecifier).nonEmpty =>
        val filename    = fileName(declaration)
        val typeDefName = if (name.isEmpty) { safeGetBinding(declarator.getName).map(_.getName).getOrElse("") }
        else { name }
        val tpe                = registerType(typeFor(declarator))
        val (name_, fullName_) = scopeLocalUniqueName(cleanType(typeDefName), fullName(declarator), "")
        Ast(typeDeclNode(declarator, name_, registerType(fullName_), filename, code(d), alias = Option(tpe)))
      case d if parentIsClassDef(d) =>
        val tpe = typeForIASTDeclarator(declaration, declarator, index)
        Ast(memberNode(declarator, name, code(declarator), tpe))
      case d if isAssignmentFromBrokenMacro(d, declarator) && scope.lookupVariable(name).nonEmpty =>
        Ast()
      case _ if declarator.getName.isInstanceOf[ICPPASTQualifiedName] =>
        // Out-of-class static member definition (e.g. `int Foo::bar[N]`).
        // The member already exists in the class; creating a local here
        // would pollute the enclosing scope and cause cross-method REF edges.
        Ast()
      case _ =>
        val tpe  = typeForIASTDeclarator(declaration, declarator, index)
        val code = codeForDeclarator(declaration, declarator)
        val node = localNode(declarator, name, code, tpe)
        scope.addVariable(name, node, tpe, VariableScopeManager.ScopeType.BlockScope)
        Ast(node)
    }
  }

  private def astForIASTInitializer(
    init: IASTNode,
    declarator: IASTDeclarator,
    leftAst: Ast,
    args: List[Ast],
    name: String,
    tpe: String,
    signature: String,
    fullNameWithSig: String,
    constructorCallName: String,
    initCode: String
  ): Ast = {
    val constructorCallCode = s"$tpe.$constructorCallName($initCode)"
    val rightAst = constructorInvocationBlockAst(init, tpe, fullNameWithSig, signature, constructorCallCode, args)

    val assignmentCallNode =
      callNode(
        declarator,
        s"$name = $constructorCallCode",
        Operators.assignment,
        Operators.assignment,
        DispatchTypes.STATIC_DISPATCH,
        None,
        Some(registerType(Defines.Void))
      )
    callAst(assignmentCallNode, List(leftAst, rightAst))
  }

  private def astForFundamentalKeyWordInit(
    init: ICPPASTConstructorInitializer,
    declarator: IASTDeclarator,
    leftAst: Ast,
    name: String,
    tpe: String
  ): Ast = {
    val assignmentCallNode =
      callNode(
        declarator,
        s"$name = $tpe${code(init)}",
        Operators.assignment,
        Operators.assignment,
        DispatchTypes.STATIC_DISPATCH,
        None,
        Some(registerType(Defines.Void))
      )
    val args = List(leftAst, astForNode(init))
    callAst(assignmentCallNode, args)
  }

  /** The target of the assignment synthesised for a declarator with an initializer.
    *
    * For an out-of-class definition of a static data member (`int Foo::bar = 1;`) the declarator name is a qualified
    * name. It does not declare a new variable, so it must not be lowered through `astForIdentifier` (which `astForNode`
    * would pick for any `IASTName`): that flattens `Foo::bar` to an unqualified `bar` and registers it as a variable
    * reference in the enclosing namespace scope. We lower it as a field access instead, exactly as a *use* of
    * `Foo::bar` is lowered.
    */
  private def astForDeclaratorName(declarator: IASTDeclarator): Ast = declarator.getName match {
    case qualifiedName: CPPASTQualifiedName => astForQualifiedName(qualifiedName)
    case name                               => astForNode(name)
  }

  protected def astForInitializer(declarator: IASTDeclarator, init: IASTInitializer): Ast = {
    val name = ASTStringUtil.getSimpleName(declarator.getName)
    val tpe  = registerType(
      scope.lookupVariable(name).map(_._2.takeWhile(isValidFullNameChar)).getOrElse(typeFor(declarator))
    )
    val constructorCallName = tpe.split("\\.").lastOption.getOrElse(tpe)
    val initCode            = code(init).stripPrefix("{").stripSuffix("}").stripPrefix("(").stripSuffix(")")
    val signature           = s"${Defines.Void}(${initializerSignature(init)})"
    val fullNameWithSig     = s"$tpe.$constructorCallName:$signature"
    val leftAst             = astForDeclaratorName(declarator)

    init match {
      case i: IASTEqualsInitializer =>
        astForIASTEqualsInitializer(declarator, leftAst, astForNode(i.getInitializerClause))
      case i: ICPPASTConstructorInitializer if isFundamentalTypeKeywords(tpe) =>
        astForFundamentalKeyWordInit(i, declarator, leftAst, name, tpe)
      case i: ICPPASTConstructorInitializer =>
        astForIASTInitializer(
          i,
          declarator,
          leftAst,
          astsForConstructorInitializer(init),
          name,
          tpe,
          signature,
          fullNameWithSig,
          constructorCallName,
          initCode
        )
      case i: IASTInitializerList if isFundamentalTypeKeywords(tpe) =>
        astForIASTEqualsInitializer(declarator, leftAst, astForNode(i))
      case i: IASTInitializerList =>
        astForIASTInitializer(
          i,
          declarator,
          leftAst,
          astsForInitializerClauses(i.getClauses),
          name,
          tpe,
          signature,
          fullNameWithSig,
          constructorCallName,
          initCode
        )
      case _ => astForNode(init)
    }
  }

  protected def astForConstructorCall(declarator: ICPPASTDeclarator): Ast = {
    val leftAst = astForNode(declarator.getName)

    val name = ASTStringUtil.getSimpleName(declarator.getName)
    val tpe  = registerType(scope.lookupVariable(name).map(_._2.takeWhile(isValidFullNameChar)).getOrElse(Defines.Any))
    val constructorCallName = tpe.split("\\.").lastOption.getOrElse(tpe)
    val signature           = s"${Defines.Void}()"
    val fullNameWithSig     = s"$tpe.$constructorCallName:$signature"
    val constructorCallCode = s"$tpe.$constructorCallName()"
    val rightAst            =
      constructorInvocationBlockAst(declarator, tpe, fullNameWithSig, signature, constructorCallCode, List.empty)

    val assignmentCallNode = callNode(
      declarator,
      s"${code(declarator)} = $constructorCallCode",
      Operators.assignment,
      Operators.assignment,
      DispatchTypes.STATIC_DISPATCH,
      None,
      Some(registerType(Defines.Void))
    )
    callAst(assignmentCallNode, List(leftAst, rightAst))
  }

  private def astForIASTEqualsInitializer(declarator: IASTDeclarator, leftAst: Ast, rightAst: Ast) = {
    // Strip leading pointer/reference markers (* or &) from the declarator code since they are part of
    // the type specifier (stored in IASTSimpleDeclaration.getDeclSpecifier), not the variable name.
    // E.g. for `const char* c = read()`, CDT gives declarator code `* c = read()` but the assignment
    // expression should be `c = read()`.
    val assignmentCode     = code(declarator).replaceFirst("^[*&]+\\s*", "")
    val assignmentCallNode = callNode(
      declarator,
      assignmentCode,
      Operators.assignment,
      Operators.assignment,
      DispatchTypes.STATIC_DISPATCH,
      None,
      Some(registerType(Defines.Void))
    )
    callAst(assignmentCallNode, List(leftAst, rightAst))
  }

  private def initializerSignature(init: IASTInitializer): String = {
    val argTypes = init match {
      case c: ICPPASTConstructorInitializer =>
        c.getArguments.collect { case e: IASTExpression => e }.map(expr => cleanType(safeGetExpressionType(expr)))
      case list: IASTInitializerList =>
        list.getClauses.collect { case e: IASTExpression => e }.map(expr => cleanType(safeGetExpressionType(expr)))
      case _ => Array.empty[String]
    }
    StringUtils.normalizeSpace(argTypes.mkString(","))
  }

  protected def astForAliasDeclaration(aliasDeclaration: ICPPASTAliasDeclaration): Ast = {
    val (name, fullName_) = scopeLocalUniqueName(aliasDeclaration.getAlias.toString, fullName(aliasDeclaration), "")
    val mappedName        = registerType(typeFor(aliasDeclaration.getMappingTypeId))
    val typeDeclNode_     =
      typeDeclNode(
        aliasDeclaration,
        name,
        registerType(fullName_),
        fileName(aliasDeclaration),
        code(aliasDeclaration),
        alias = Option(mappedName)
      )
    Ast(typeDeclNode_)
  }

  protected def astForASMDeclaration(asm: IASTASMDeclaration): Ast = Ast(unknownNode(asm, code(asm)))

  protected def isCPPClassLike(decl: IASTSimpleDeclaration): Boolean = {
    decl.getDeclSpecifier match {
      case t: ICPPASTNamedTypeSpecifier =>
        safeGetBinding(t.getName).exists {
          case binding: ICompositeType =>
            true
          case binding: IProblemBinding =>
            binding.getASTNode.isInstanceOf[IASTCompositeTypeSpecifier]
            binding.getASTNode.isInstanceOf[ICPPASTTemplateId]
          case other =>
            false
        }
      case _ => false
    }
  }

  protected def astsForDeclaration(decl: IASTDeclaration, underTypeDecl: Boolean = false): Seq[Ast] = {
    if (isUnsupportedCoroutineKeyword(decl)) {
      return Seq(astForUnsupportedCoroutineNode(decl))
    }

    val declAsts = decl match {
      case sb: ICPPASTStructuredBindingDeclaration => astsForStructuredBindingDeclaration(sb)
      case declStmt: CPPASTSimpleDeclaration if isUnsupportedCoroutineKeyword(declStmt) =>
        Seq(astForUnsupportedCoroutineNode(declStmt))
      case declaration: IASTSimpleDeclaration =>
        val declarators = declaration.getDeclarators
        declaration.getDeclSpecifier match {
          case spec: IASTCompositeTypeSpecifier =>
            astsForCompositeType(spec, declarators.toList)
          case spec: IASTEnumerationSpecifier =>
            astsForEnum(spec, declarators.toList)
          case spec: IASTElaboratedTypeSpecifier =>
            astsForElaboratedType(spec, declarators.toList)
          case spec: IASTNamedTypeSpecifier if declarators.isEmpty =>
            val filename  = fileName(spec)
            val name      = shortName(spec)
            val fullName_ = fullName(spec)
            Seq(Ast(typeDeclNode(spec, name, registerType(fullName_), filename, code(spec), alias = Option(name))))
          case _ if declarators.nonEmpty =>
            declarators.toIndexedSeq.zipWithIndex.map {
              case (d: IASTFunctionDeclarator, _) =>
                astForFunctionDeclarator(d)
              case (d: IASTSimpleDeclaration, _) if d.getInitializer != null =>
                Ast() // we do the AST for this down below with initAsts
              case (d, i) =>
                astForDeclarator(declaration, d, i)
            }
          case _ if code(declaration) == ";" =>
            Seq.empty // dangling decls from unresolved macros; we ignore them
          case _ if declarators.isEmpty && declaration.getParent.isInstanceOf[IASTTranslationUnit] =>
            Seq.empty // dangling decls from unresolved macros; we ignore them
          case _ if declarators.isEmpty => Seq(astForNode(declaration))
        }
      case alias: CPPASTAliasDeclaration                         => Seq(astForAliasDeclaration(alias))
      case functionDefinition: IASTFunctionDefinition            => Seq(astForFunctionDefinition(functionDefinition))
      case namespaceAlias: ICPPASTNamespaceAlias                 => Seq(astForNamespaceAlias(namespaceAlias))
      case namespaceDefinition: ICPPASTNamespaceDefinition       => Seq(astForNamespaceDefinition(namespaceDefinition))
      case a: ICPPASTStaticAssertDeclaration if !underTypeDecl   => Seq(astForStaticAssert(a))
      case a: ICPPASTStaticAssertDeclaration                     => Seq.empty
      case asm: IASTASMDeclaration                               => Seq(astForASMDeclaration(asm))
      case t: ICPPASTTemplateDeclaration                         => astsForDeclaration(t.getDeclaration)
      case l: ICPPASTLinkageSpecification                        => astsForLinkageSpecification(l)
      case _: ICPPASTUsingDeclaration | _: ICPPASTUsingDirective => Seq.empty // handled by CDT itself
      case _: ICPPASTVisibilityLabel                             => Seq.empty
      case _: ICPPASTExplicitTemplateInstantiation               => Seq.empty
      case _                                                     => Seq(astForNode(decl))
    }

    val initAsts = if (underTypeDecl) Seq.empty else astsForDeclarationInit(decl)
    declAsts ++ initAsts
  }

  private def declHasInit(decl: IASTNode): Boolean = {
    decl match {
      case a: ICPPASTStaticAssertDeclaration                                         => true
      case declaration: IASTSimpleDeclaration if declaration.getDeclarators.nonEmpty =>
        declaration.getDeclarators.exists {
          // Out-of-class static member definitions (qualified names like `Foo::bar[N]`) without an
          // initializer carry no value. Processing them would create identifier nodes at namespace
          // scope via astForConstructorCall, polluting the shared scope chain and causing
          // cross-method REF edges (NONLOCAL_REF validation errors). With an initializer they fall
          // through to the cases below; see astsForDeclarationInit.
          case d: IASTDeclarator if d.getName.isInstanceOf[ICPPASTQualifiedName] && d.getInitializer == null =>
            false
          case d: ICPPASTDeclarator if d.getInitializer == null && isCPPClassLike(declaration) => true
          case d: IASTDeclarator if d.getInitializer != null                                   => true
          case arrayDecl: IASTArrayDeclarator                                                  => true
          case _                                                                               => false
        }
      case _ => false
    }
  }

  private def astsForDeclarationInit(decl: IASTDeclaration): Seq[Ast] = {
    if (isUnsupportedCoroutineKeyword(decl)) {
      return Seq(astForUnsupportedCoroutineNode(decl))
    }

    decl match {
      case a: ICPPASTStaticAssertDeclaration                                         => Seq(astForStaticAssert(a))
      case declaration: IASTSimpleDeclaration if declaration.getDeclarators.nonEmpty =>
        declaration.getDeclarators.toList.map {
          // Skip out-of-class static member definitions without an initializer; see comment in declHasInit.
          case d: IASTDeclarator if d.getName.isInstanceOf[ICPPASTQualifiedName] && d.getInitializer == null =>
            Ast()
          case d: ICPPASTDeclarator if d.getInitializer == null && isCPPClassLike(declaration) =>
            astForConstructorCall(d)
          case d: IASTDeclarator if d.getInitializer != null =>
            astForInitializer(d, d.getInitializer)
          case arrayDecl: IASTArrayDeclarator =>
            astForIASTArrayDeclarator(arrayDecl)
          case _ => Ast()
        }
      case _ => Nil
    }
  }

  private def astForIASTArrayDeclarator(arrayDecl: IASTArrayDeclarator): Ast = {
    val op           = Operators.arrayInitializer
    val initCallNode =
      callNode(arrayDecl, code(arrayDecl), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(Defines.Any))
    val initArgs = arrayDecl.getArrayModifiers.toList.filter(m => m.getConstantExpression != null).map(astForNode)
    callAst(initCallNode, initArgs)
  }

  private def parentIsClassDef(node: IASTNode): Boolean = Option(node.getParent) match {
    case Some(_: IASTCompositeTypeSpecifier) => true
    case _                                   => false
  }

  private def isTypeDef(decl: IASTSimpleDeclaration): Boolean = {
    hasStorageClass(
      decl.getDeclSpecifier,
      IASTDeclSpecifier.sc_typedef,
      Try(decl.getRawSignature.startsWith("typedef")).getOrElse(false)
    )
  }

  private def astForNamespaceDefinition(namespaceDefinition: ICPPASTNamespaceDefinition): Ast = {
    val TypeFullNameInfo(name, fullName) = typeFullNameInfo(namespaceDefinition)
    val codeString                       = code(namespaceDefinition)
    val filename                         = fileName(namespaceDefinition)
    val namespaceBlockNode_              =
      namespaceBlockNode(namespaceDefinition, name, s"$filename:$fullName", filename).code(codeString)
    val blockNode_ = blockNode(namespaceDefinition)
    methodAstParentStack.push(blockNode_)
    scope.pushNewMethodScope(fullName, name, namespaceBlockNode_, None)
    scope.pushNewBlockScope(blockNode_)
    val childrenAsts = namespaceDefinition.getDeclarations.flatMap(d => astsForDeclaration(d)).toIndexedSeq
    methodAstParentStack.pop()
    scope.popScope()
    scope.popScope()
    Ast(namespaceBlockNode_).withChild(Ast(blockNode_).withChildren(childrenAsts))
  }

  private def isAssignmentFromBrokenMacro(declaration: IASTSimpleDeclaration, declarator: IASTDeclarator): Boolean = {
    declaration.getParent.isInstanceOf[IASTTranslationUnit] &&
    declarator.getInitializer.isInstanceOf[IASTEqualsInitializer]
  }

  private def codeForDeclarator(declaration: IASTSimpleDeclaration, declarator: IASTDeclarator): String = {
    val specCode    = declaration.getDeclSpecifier.getRawSignature
    val declCodeRaw = declarator.getRawSignature
    val declCode    = declarator.getInitializer match {
      case null => declCodeRaw
      case _    => declCodeRaw.replace(declarator.getInitializer.getRawSignature, "")
    }
    val normalizedCode = StringUtils.normalizeSpace(s"$specCode $declCode")
    normalizedCode.strip()
  }

  private def astsForLinkageSpecification(linkage: ICPPASTLinkageSpecification): Seq[Ast] = {
    linkage.getDeclarations.toIndexedSeq.flatMap(declaration => astsForDeclaration(declaration))
  }

  private def filterNameAlias(nameAlias: Option[String], fullName: String): Option[String] = {
    nameAlias.toList.filter(n => n != fullName).distinct.headOption
  }

  private def astsForCompositeType(typeSpecifier: IASTCompositeTypeSpecifier, decls: List[IASTDeclarator]): Seq[Ast] = {
    val filename                         = fileName(typeSpecifier)
    val TypeFullNameInfo(name, fullName) = typeFullNameInfo(typeSpecifier)
    val codeString                       = code(typeSpecifier)

    val declAsts = decls.zipWithIndex.map { case (d, i) =>
      astForDeclarator(typeSpecifier.getParent.asInstanceOf[IASTSimpleDeclaration], d, i)
    }

    val nameAlias = decls.headOption.map(d => registerType(shortName(d))).filter(_.nonEmpty)
    val alias     = filterNameAlias(nameAlias, fullName)

    val typeDecl = typeSpecifier match {
      case c: ICPPASTCompositeTypeSpecifier =>
        val baseClassList = c.getBaseSpecifiers.map(s => registerType(cleanType(s.getNameSpecifier.toString))).toSeq
        typeDeclNode(c, name, fullName, filename, codeString, inherits = baseClassList, alias = alias)
      case other =>
        typeDeclNode(other, name, fullName, filename, codeString, alias = alias)
    }

    val typeRefNodeMaybe = typeRefIdStack.headOption match {
      case None => Some(typeRefNode(typeSpecifier, codeString, fullName))
      case _    => None
    }

    methodAstParentStack.push(typeDecl)
    typeRefNodeMaybe.foreach(typeRefIdStack.push)
    scope.pushNewMethodScope(typeDecl.fullName, typeDecl.name, typeDecl, None)

    val memberDecls                = typeSpecifier.getDeclarations(true).toList
    val memberAsts                 = memberDecls.flatMap(d => astsForDeclaration(d, true))
    val memberNodesWithInitializer = memberDecls.filter(d => declHasInit(d))

    methodAstParentStack.pop()
    typeRefNodeMaybe.foreach(_ => typeRefIdStack.pop())
    scope.popScope()

    val asts = if (memberNodesWithInitializer.isEmpty) {
      Ast(typeDecl).withChildren(memberAsts) +: declAsts
    } else {
      val initAst = createStaticConstructor(typeSpecifier, memberNodesWithInitializer, typeDecl)
      Ast(typeDecl).withChildren(memberAsts).withChild(initAst) +: declAsts
    }
    asts.foreach { ast =>
      Ast.storeInDiffGraph(ast, diffGraph)
      ast.root.foreach(r => diffGraph.addEdge(methodAstParentStack.head, r, EdgeTypes.AST))
    }
    typeRefNodeMaybe.map(Ast(_)).toSeq
  }

  private def astsForElaboratedType(
    typeSpecifier: IASTElaboratedTypeSpecifier,
    decls: List[IASTDeclarator]
  ): Seq[Ast] = {
    val TypeFullNameInfo(name, fullName) = typeFullNameInfo(typeSpecifier)
    val nameAlias                        = decls.headOption.map(d => registerType(shortName(d))).filter(_.nonEmpty)

    val alias    = filterNameAlias(nameAlias, fullName)
    val declAsts = decls.zipWithIndex.map { case (d, i) =>
      astForDeclarator(typeSpecifier.getParent.asInstanceOf[IASTSimpleDeclaration], d, i)
    }

    if (alias.isEmpty) {
      val filename = fileName(typeSpecifier)
      val typeDecl = typeDeclNode(typeSpecifier, name, fullName, filename, code(typeSpecifier))
      Ast(typeDecl) +: declAsts
    } else {
      declAsts
    }
  }

  /** An enumerator is typed with its enum's type, `enumTypeFullName`, which is how a variable declared with the enum is
    * typed, or with the base type a C++ enum gives.
    */
  private def enumeratorTypeName(
    enumerator: IASTEnumerationSpecifier.IASTEnumerator,
    enumTypeFullName: String
  ): String = {
    enumerator.getParent match {
      case enumeration: ICPPASTEnumerationSpecifier if enumeration.getBaseType != null =>
        enumeration.getBaseType.toString
      case _ => enumTypeFullName
    }
  }

  /** The names of the enum member that the AST creator of another file creates for `enumerator`, for a reference to it
    * from this file: the name and full name [[astsForEnum]] gives the enum's TYPE_DECL there, and the member's type.
    *
    * They are read from the enum's declaration, which CDT's binding of the reference leads to, so they do not depend on
    * where the reference is. `None` where the declaring file's AST creator gives a name that cannot be read from the
    * declaration alone: an enum without a tag and without a declarator is named `<enum>N` by a counter of that file,
    * and the name of an enum without a C++ binding inside a struct or a function depends on that scope.
    */
  protected def enumMemberNamesFromDeclaration(
    enumerator: IASTEnumerationSpecifier.IASTEnumerator
  ): Option[EnumMemberNames] = {
    enumerator.getParent match {
      case enumeration: IASTEnumerationSpecifier =>
        enumTypeNamesFromDeclaration(enumeration).map { case (typeName, typeFullName) =>
          val enumTypeFullName = registerType(typeFullName)
          EnumMemberNames(typeName, enumTypeFullName, registerType(enumeratorTypeName(enumerator, enumTypeFullName)))
        }
      case _ => None
    }
  }

  private def enumTypeNamesFromDeclaration(enumeration: IASTEnumerationSpecifier): Option[(String, String)] = {
    val tag = shortName(enumeration)
    if (tag.nonEmpty) {
      safeGetBinding(enumeration.getName) match {
        case Some(binding: ICPPBinding) if binding.getName.nonEmpty => Option((tag, fullName(enumeration)))
        case _ if isDeclaredAtFileScope(enumeration)                => Option((tag, tag))
        case _                                                      => None
      }
    } else if (isDeclaredAtFileScope(enumeration)) {
      enumeration.getParent match {
        case declaration: IASTSimpleDeclaration =>
          declaration.getDeclarators.headOption
            .map(declarator => registerType(shortName(declarator)))
            .filter(_.nonEmpty)
            .map(alias => (alias, alias))
        case _ => None
      }
    } else {
      None
    }
  }

  private def isDeclaredAtFileScope(enumeration: IASTEnumerationSpecifier): Boolean = {
    @tailrec
    def isFileScope(node: IASTNode): Boolean = {
      node match {
        case _: IASTTranslationUnit               => true
        case linkage: ICPPASTLinkageSpecification => isFileScope(linkage.getParent)
        case _                                    => false
      }
    }
    enumeration.getParent match {
      case declaration: IASTSimpleDeclaration => isFileScope(declaration.getParent)
      case _                                  => false
    }
  }

  private def memberAstForEnumerator(
    enumerator: IASTEnumerationSpecifier.IASTEnumerator,
    enumTypeName: String,
    enumTypeFullName: String
  ): Ast = {
    val tpe    = enumeratorTypeName(enumerator, enumTypeFullName)
    val member =
      memberNode(enumerator, ASTStringUtil.getSimpleName(enumerator.getName), code(enumerator), registerType(tpe))
    safeGetBinding(enumerator.getName).foreach(binding =>
      enumMembers.update(binding, EnumMemberInfo(member, enumTypeName, enumTypeFullName))
    )
    enumeratorPlace(enumerator).foreach { place =>
      accumulator.registerEnumeratorMember(place, AstCreationPass.EnumeratorMember(member, isCppFile))
    }
    Ast(member).withChild(Ast(NewModifier().modifierType(ModifierTypes.FINAL)))
  }

  /** The path [[enumeratorPlace]] takes for each file name CDT gives, so that the places this file registers, which are
    * kept to the end of the parse, share one string per file.
    */
  private val placeFiles: mutable.Map[String, String] = mutable.HashMap.empty

  /** Where `enumerator` is declared: the file CDT read its name from and the name's offset there, the same in every
    * translation unit that includes the file. For an include that does not resolve, c2cpg gives CDT a header of the
    * same name found elsewhere in the code, which CDT reads under the path it tried; that header's own path is taken.
    */
  protected def enumeratorPlace(
    enumerator: IASTEnumerationSpecifier.IASTEnumerator
  ): Option[AstCreationPass.EnumeratorPlace] = {
    val name = enumerator.getName
    for {
      location <- nullSafeFileLocation(name)
      file     <- Option(location.getFileName).filter(_.nonEmpty)
    } yield {
      val path = placeFiles.getOrElseUpdate(
        file,
        Paths.get(headerFileFinder.substitutedFor(file).getOrElse(file)).normalize().toString
      )
      AstCreationPass.EnumeratorPlace(path, location.getNodeOffset, ASTStringUtil.getSimpleName(name))
    }
  }

  protected def isCppFile: Boolean = cdtAst.isInstanceOf[ICPPASTTranslationUnit]

  protected def astForEnumeratorWithInit(enumerator: IASTEnumerationSpecifier.IASTEnumerator): Ast = {
    if (enumerator.getValue != null) {
      val operatorName = Operators.assignment
      val callNode_    = callNode(
        enumerator,
        code(enumerator),
        operatorName,
        operatorName,
        DispatchTypes.STATIC_DISPATCH,
        None,
        Some(registerType(Defines.Void))
      )
      val left  = astForNode(enumerator.getName)
      val right = astForNode(enumerator.getValue)
      callAst(callNode_, List(left, right))
    } else {
      Ast()
    }
  }

  private def createStaticConstructor(node: IASTNode, inits: List[IASTNode], typeDeclNode: NewTypeDecl): Ast = {
    val constructorName = io.joern.x2cpg.Defines.StaticInitMethodName
    val fullName        = s"${typeDeclNode.fullName}.$constructorName:${typeDeclNode.fullName}()"
    val methodNode_     = methodNode(node, constructorName, constructorName, fullName, None, filename)
    val modifiers       =
      Seq(NewModifier().modifierType(ModifierTypes.CONSTRUCTOR), NewModifier().modifierType(ModifierTypes.STATIC))

    val blockNode = NewBlock()
    methodAstParentStack.push(methodNode_)
    scope.pushNewMethodScope(fullName, constructorName, blockNode, typeRefIdStack.headOption, true)

    val initAsts = inits.flatMap {
      case d: IASTDeclaration if declHasInit(d) => astsForDeclarationInit(d)
      case node                                 => Seq(astForNode(node))
    }

    scope.popScope()
    methodAstParentStack.pop()

    val bodyAst           = blockAst(blockNode, initAsts)
    val methodReturnNode_ = methodReturnNode(node, typeDeclNode.fullName)
    val mAst              = methodAst(methodNode_, Nil, bodyAst, methodReturnNode_, modifiers)

    val functionBindingAst = createFunctionBinding(methodNode_)
    Ast.storeInDiffGraph(functionBindingAst, diffGraph)
    mAst
  }

  private def astsForEnum(typeSpecifier: IASTEnumerationSpecifier, decls: List[IASTDeclarator]): Seq[Ast] = {
    val filename                         = fileName(typeSpecifier)
    val codeString                       = code(typeSpecifier)
    val TypeFullNameInfo(name, fullName) = typeFullNameInfo(typeSpecifier)

    val declAsts = decls.zipWithIndex.map { case (d, i) =>
      astForDeclarator(typeSpecifier.getParent.asInstanceOf[IASTSimpleDeclaration], d, i)
    }

    val nameAlias = decls.headOption.map(d => registerType(shortName(d))).filter(_.nonEmpty)
    val alias     = filterNameAlias(nameAlias, fullName)
    val (deAliasedName, deAliasedFullName, newAlias) = if (name.contains("<enum>") && alias.isDefined) {
      (alias.get, fullName.substring(0, fullName.indexOf("<enum>")) + alias.get, None)
    } else { (name, fullName, alias) }

    val enumTypeFullName = registerType(deAliasedFullName)
    val typeDecl         =
      typeDeclNode(typeSpecifier, deAliasedName, enumTypeFullName, filename, codeString, alias = newAlias)
    val typeRefNodeMaybe = typeRefIdStack.headOption match {
      case None => Some(typeRefNode(typeSpecifier, codeString, fullName))
      case _    => None
    }

    methodAstParentStack.push(typeDecl)
    typeRefNodeMaybe.foreach(typeRefIdStack.push)
    scope.pushNewMethodScope(typeDecl.fullName, typeDecl.name, typeDecl, None)

    val enumerators                = typeSpecifier.getEnumerators.toList
    val memberNodesWithInitializer = enumerators.filter(_.getValue != null)
    val memberAsts                 = enumerators.map(memberAstForEnumerator(_, deAliasedName, enumTypeFullName))

    typeRefNodeMaybe.foreach(_ => typeRefIdStack.pop())
    methodAstParentStack.pop()
    scope.popScope()

    val asts = if (memberNodesWithInitializer.isEmpty) {
      Ast(typeDecl).withChildren(memberAsts) +: declAsts
    } else {
      val init = createStaticConstructor(typeSpecifier, memberNodesWithInitializer, typeDecl)
      Ast(typeDecl).withChildren(memberAsts).withChild(init) +: declAsts
    }
    asts.foreach { ast =>
      Ast.storeInDiffGraph(ast, diffGraph)
      ast.root.foreach(r => diffGraph.addEdge(methodAstParentStack.head, r, EdgeTypes.AST))
    }
    typeRefNodeMaybe.map(Ast(_)).toSeq
  }

}
