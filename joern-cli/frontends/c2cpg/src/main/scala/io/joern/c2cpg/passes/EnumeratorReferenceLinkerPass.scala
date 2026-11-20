package io.joern.c2cpg.passes

import io.joern.c2cpg.passes.AstCreationPass.{EnumeratorMember, EnumeratorPlace, EnumeratorReference}
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes}
import io.shiftleft.passes.CpgPass
import org.slf4j.{Logger, LoggerFactory}

/** Links each reference to an enumerator that another file declares to the member made for that enumerator.
  *
  * The reference is a field access on the enum's type (see `AstForPrimitivesCreator`), and the post-frontend
  * `FieldAccessLinkerPass` would link it by the type's full name. Several files may declare an enum of one full name
  * (per-board copies of a header, for instance), and FullNameUniquenessPass leaves that name to the first by file name,
  * so a link by name may reach another file's enum. CDT's binding of the reference names the place the enumerator is
  * declared in, the same place under which the declaring file's AST creator registered the member, so the reference is
  * linked to that member here. A header parsed both as C and as C++ has a member of each; the one parsed in the
  * reference's language is taken. FieldAccessLinkerPass skips calls that already have a REF edge, so it still handles
  * the references whose place has no member (their file was not parsed, or was parsed without the declaration).
  */
class EnumeratorReferenceLinkerPass(
  cpg: Cpg,
  members: collection.Map[EnumeratorPlace, collection.Seq[EnumeratorMember]],
  references: collection.Seq[EnumeratorReference]
) extends CpgPass(cpg) {

  private val logger: Logger = LoggerFactory.getLogger(classOf[EnumeratorReferenceLinkerPass])

  override def run(dstGraph: DiffGraphBuilder): Unit = {
    val linked = references.count { reference =>
      val candidates = members.getOrElse(reference.place, Nil)
      val edge       = for {
        member       <- candidates.find(_.isCpp == reference.isCpp).orElse(candidates.headOption)
        storedMember <- member.member.storedRef
        storedAccess <- reference.access.storedRef
      } yield dstGraph.addEdge(storedAccess, storedMember, EdgeTypes.REF)
      edge.isDefined
    }
    logger.debug(
      s"$linked of ${references.size} references to enumerators of other files linked to their members by place"
    )
  }

}
