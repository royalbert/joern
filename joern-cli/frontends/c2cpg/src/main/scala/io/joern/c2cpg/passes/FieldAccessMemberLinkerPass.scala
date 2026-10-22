package io.joern.c2cpg.passes

import io.joern.c2cpg.passes.AstCreationPass.{DeclarationPlace, PlacedTypeDecl, ResolvedFieldAccess}
import io.shiftleft.codepropertygraph.generated.nodes.{Call, Member, TypeDecl}
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes}
import io.shiftleft.passes.CpgPass
import io.shiftleft.semanticcpg.language.*

/** Links each field access whose field CDT resolved to the MEMBER of that field, with a REF edge.
  *
  * The AST creators register every struct, union and class definition under the place it is defined at, and every
  * resolved field access under the place of the definition its field belongs to (see
  * [[io.joern.c2cpg.astcreation.FieldAccessLinking]]). A definition in a header has one TYPE_DECL, made from the
  * header's own parse, while every file including the header may access its fields; the place identifies it in all of
  * these parses, whatever the type names involved: pointers, typedefs, nested accesses, array elements, and other
  * files' definitions of the same name make no difference. The member is the TYPE_DECL's member with the field's name;
  * where the branches of an `#if` in the struct's body declare several members of that name, the one on the line of the
  * declarator CDT bound the field to. A header parsed both as C and as C++ has two TYPE_DECLs at one place; the one of
  * the access's language is taken. A C++ file that includes a C header inside an `extern "C"` block makes another
  * TYPE_DECL for each of the header's structs, at the same place; the one made by the header's own parse is taken. An
  * access with no TYPE_DECL at its place, or with more than one left, is not linked here. A field of an anonymous
  * member (`struct S { union { int a; }; }`) is linked to the member of that name of the struct or union that holds the
  * anonymous member, where it has one, and otherwise to the anonymous member's own.
  *
  * Accesses not linked here are left to x2cpg's `FieldAccessLinkerPass`, which skips calls that have a REF edge.
  */
class FieldAccessMemberLinkerPass(
  cpg: Cpg,
  typeDecls: collection.Map[DeclarationPlace, collection.Seq[PlacedTypeDecl]],
  accesses: collection.Seq[ResolvedFieldAccess]
) extends CpgPass(cpg) {

  override def run(diffGraph: DiffGraphBuilder): Unit = {
    accesses.foreach { resolved =>
      for {
        access <- resolved.access.storedRef.collect { case call: Call => call }
        if !access._refOut.hasNext
        member <- resolved.enclosingPlace.flatMap(memberAt(_, resolved)).orElse(memberAt(resolved.place, resolved))
      } diffGraph.addEdge(access, member, EdgeTypes.REF)
    }
  }

  private def memberAt(place: DeclarationPlace, resolved: ResolvedFieldAccess): Option[Member] = {
    typeDeclAt(place, resolved).flatMap { typeDecl =>
      typeDecl._memberViaAstOut.nameExact(resolved.member).l match {
        case List(member) => Some(member)
        case several      => onlyOne(several.filter(_.lineNumber == resolved.memberLine))
      }
    }
  }

  private def typeDeclAt(place: DeclarationPlace, resolved: ResolvedFieldAccess): Option[TypeDecl] = {
    val candidates   = typeDecls.getOrElse(place, Seq.empty).toList
    val sameLanguage = candidates.filter(_.isCpp == resolved.isCpp)
    val inLanguage   = if (sameLanguage.nonEmpty) sameLanguage else candidates
    val fromOwnFile  = inLanguage.filter(_.fromOwnFile)
    onlyOne((if (fromOwnFile.nonEmpty) fromOwnFile else inLanguage).flatMap { placed =>
      placed.typeDecl.storedRef.collect { case typeDecl: TypeDecl => typeDecl }
    })
  }

  private def onlyOne[T](candidates: List[T]): Option[T] = candidates match {
    case List(candidate) => Some(candidate)
    case _               => None
  }

}
