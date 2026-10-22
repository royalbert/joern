package io.joern.c2cpg.astcreation

import io.joern.c2cpg.passes.AstCreationPass.{DeclarationPlace, PlacedTypeDecl, ResolvedFieldAccess}
import io.joern.x2cpg.Ast
import io.shiftleft.codepropertygraph.generated.nodes.{NewCall, NewNode, NewTypeDecl}
import org.eclipse.cdt.core.dom.ast.*
import org.eclipse.cdt.core.dom.ast.cpp.{ICPPASTQualifiedName, ICPPASTTranslationUnit, ICPPSpecialization}
import org.eclipse.cdt.internal.core.dom.parser.ASTQueries
import org.eclipse.cdt.internal.core.dom.parser.c.ICInternalBinding
import org.eclipse.cdt.internal.core.dom.parser.cpp.ICPPInternalBinding

import java.nio.file.Paths
import scala.annotation.tailrec
import scala.collection.mutable

/** Ties field accesses to the struct, union or class that CDT resolves their field to.
  *
  * A struct is usually defined in a header. Its TYPE_DECL is made by the AST creator of that header, while its fields
  * are accessed from every file that includes the header, and all of these see the same definition at the same place:
  * the file CDT read it from, the position of its specifier there, and the name the specifier gives the struct. The AST
  * creators therefore register each composite type declaration under that place, and each field access under the place
  * of the definition its field's binding belongs to. [[io.joern.c2cpg.passes.FieldAccessMemberLinkerPass]] joins the
  * two once all files are done. Neither side looks a type up by its name, so a use reaches the definition its own
  * translation unit includes, even where other files define a type of the same name.
  */
trait FieldAccessLinking { this: AstCreator =>

  private lazy val isCpp: Boolean = cdtAst.isInstanceOf[ICPPASTTranslationUnit]

  private val normalizedPaths: mutable.Map[String, String] = mutable.HashMap.empty

  /** The access each field access node of this file was registered with, so that copies of the node are registered too.
    */
  private val registeredAccesses = new java.util.IdentityHashMap[NewCall, ResolvedFieldAccess]()

  /** Where each struct, union or class whose fields this file accesses is defined, by its binding; a struct's fields
    * are usually accessed many times.
    */
  private val ownerPlaces = new java.util.IdentityHashMap[IBinding, Option[DeclarationPlace]]()

  /** The line of the declarator that declares each field this file accesses, by its binding. */
  private val fieldLines = new java.util.IdentityHashMap[IField, Option[Int]]()

  /** Registers `typeDecl`, made for the struct, union or class defined by `specifier`. */
  protected def registerCompositeDeclaration(specifier: IASTCompositeTypeSpecifier, typeDecl: NewTypeDecl): Unit = {
    placeOf(specifier).foreach { place =>
      accumulator.registerTypeDecl(place, PlacedTypeDecl(typeDecl, isCpp, fromOwnFile = !isIncludedNode(specifier)))
    }
  }

  /** Registers `access` if CDT resolves `fieldName` to a field of a struct, union or class it has a definition of. */
  protected def registerFieldAccess(access: NewCall, fieldName: IASTName): Unit = {
    safeGetBinding(fieldName).foreach {
      case field: IField if !field.isInstanceOf[IProblemBinding] => registerFieldAccess(access, field)
      case _                                                     =>
    }
  }

  /** Registers `access` as an access of `field`, if CDT has a definition of the field's struct, union or class. */
  protected def registerFieldAccess(access: NewCall, field: IField): Unit = {
    for {
      owner  <- safeCdtCall(field.getCompositeTypeOwner)
      place  <- ownerPlaces.computeIfAbsent(owner, _ => definitionSpecifier(owner).flatMap(placeOf))
      member <- safeCdtCall(field.getName).filter(_.nonEmpty)
    } {
      val line     = fieldLines.computeIfAbsent(field, _ => declarationLine(field))
      val resolved = ResolvedFieldAccess(access, place, member, line, isCpp)
      registeredAccesses.put(access, resolved)
      accumulator.registerFieldAccess(resolved)
    }
  }

  /** Registers the field accesses in `copy`, which `Ast.subTreeCopy` made of the subtree of `original` rooted at `root`
    * (a macro argument), as accesses of the fields their originals access. `subTreeCopy` lists the copied nodes in the
    * order of a pre-order walk along the AST edges of `original`.
    */
  protected def registerCopiedFieldAccesses(original: Ast, root: NewNode, copy: Ast): Unit = {
    if (!registeredAccesses.isEmpty) {
      val children = new java.util.IdentityHashMap[NewNode, mutable.ArrayBuffer[NewNode]]()
      original.edges.foreach { edge =>
        children.computeIfAbsent(edge.src, _ => mutable.ArrayBuffer.empty[NewNode]).addOne(edge.dst)
      }
      def preOrder(node: NewNode): Iterator[NewNode] =
        Iterator.single(node) ++ Option(children.get(node)).iterator.flatMap(_.iterator.flatMap(preOrder))
      preOrder(root).zip(copy.nodes.iterator).foreach {
        case (from: NewCall, to: NewCall) =>
          Option(registeredAccesses.get(from)).foreach { resolved =>
            val copied = resolved.copy(access = to)
            registeredAccesses.put(to, copied)
            accumulator.registerFieldAccess(copied)
          }
        case _ =>
      }
    }
  }

  /** The line of the declarator that declares `field` in the body of its struct, union or class (for a C++ static
    * member, the declaration in the class, not the definition outside it). Where the branches of an `#if` in the body
    * declare members of one name, c2cpg makes a member for each branch, and the line tells which one CDT bound.
    */
  @tailrec
  private def declarationLine(field: IBinding): Option[Int] = {
    field match {
      case specialization: ICPPSpecialization if specialization.getSpecializedBinding != null =>
        declarationLine(specialization.getSpecializedBinding)
      case _ =>
        val names = field match {
          case cField: ICInternalBinding =>
            safeCdtCall(cField.getDefinition).toSeq ++ safeCdtCall(cField.getDeclarations).toSeq.flatten
          case cppField: ICPPInternalBinding =>
            safeCdtCall(cppField.getDefinition).toSeq ++ safeCdtCall(cppField.getDeclarations).toSeq.flatten
          case _ => Seq.empty
        }
        names.iterator
          .collect { case name: IASTName => name.getParent }
          .collect { case declarator: IASTDeclarator => ASTQueries.findOutermostDeclarator(declarator) }
          .find { declarator =>
            declarator.getParent match {
              case declaration: IASTSimpleDeclaration => declaration.getParent.isInstanceOf[IASTCompositeTypeSpecifier]
              case _                                  => false
            }
          }
          .flatMap(line)
    }
  }

  /** The specifier that defines `owner`. A C++ class template specialization that has a definition of its own, an
    * explicit specialization (`template <> struct Box<char> { ... }`), is defined by it; one without, an implicit
    * instantiation, by the template or partial specialization it is made from.
    */
  @tailrec
  private def definitionSpecifier(owner: IBinding): Option[IASTCompositeTypeSpecifier] = {
    ownDefinition(owner) match {
      case Some(definition) => enclosingSpecifier(definition)
      case None             =>
        owner match {
          case specialization: ICPPSpecialization if specialization.getSpecializedBinding != null =>
            definitionSpecifier(specialization.getSpecializedBinding)
          case _ => None
        }
    }
  }

  /** The definition CDT has of `binding` itself; an implicit instantiation of a C++ class template has none. */
  private def ownDefinition(binding: IBinding): Option[IASTNode] = {
    binding match {
      case cBinding: ICInternalBinding     => safeCdtCall(cBinding.getDefinition)
      case cppBinding: ICPPInternalBinding => safeCdtCall(cppBinding.getDefinition)
      case _                               => None
    }
  }

  private def enclosingSpecifier(node: IASTNode): Option[IASTCompositeTypeSpecifier] = {
    node match {
      case specifier: IASTCompositeTypeSpecifier => Some(specifier)
      case name: IASTName                        =>
        name.getParent match {
          case specifier: IASTCompositeTypeSpecifier => Some(specifier)
          case qualified: ICPPASTQualifiedName       => enclosingSpecifier(qualified)
          case _                                     => None
        }
      case _ => None
    }
  }

  /** Where `specifier` is in the code: the file CDT read it from, its offset there, its offset in the macro expansion
    * it starts in, and the name it gives its type (empty for an anonymous struct). All of these are the same in every
    * translation unit that includes the file. A macro call's expansion is placed at the call as a whole, so the
    * definitions one call expands to share the file offset and are told apart by their offsets in the expansion; the
    * name tells apart the definitions of a call whose macro is defined differently for different translation units.
    */
  private def placeOf(specifier: IASTCompositeTypeSpecifier): Option[DeclarationPlace] = {
    for {
      location <- nullSafeFileLocation(specifier)
      file     <- Option(location.getFileName).filter(_.nonEmpty)
      name     <- safeCdtCall(specifier.getName.toString)
    } yield {
      val path = normalizedPaths.getOrElseUpdate(file, Paths.get(file).normalize().toString)
      DeclarationPlace(path, location.getNodeOffset, offsetInMacroExpansion(specifier), name)
    }
  }

  /** The offset of `node` in the macro expansion it starts in, or -1 if it starts in the file itself. */
  private def offsetInMacroExpansion(node: IASTNode): Int = {
    safeCdtCall(node.getNodeLocations)
      .flatMap(_.headOption)
      .collect { case expansion: IASTMacroExpansionLocation => expansion.getNodeOffset }
      .getOrElse(-1)
  }

}
