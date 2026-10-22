package io.joern.c2cpg.passes.types

import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.shiftleft.codepropertygraph.generated.Operators
import io.shiftleft.semanticcpg.language.*

class FieldAccessMemberLinkMethodTableTests extends C2CpgSuite {

  "Calls through method tables" should {
    val cpg = code("""
        |struct ops { int (*read)(int); int (*write)(int, int); };
        |struct dev { int id; struct ops *ops; };
        |int r(int x) { return x; }
        |int w(int x, int y) { return x + y; }
        |struct ops uart = { .read = r, .write = w };
        |struct ops spi = { r, w };
        |struct tagged { int a; int (*read)(int); } tv = { 1, r };
        |int f(struct dev *d) { return d->ops->read(d->id) + tv.read(tv.a); }
        |struct value { int kind; union { int number; float real; }; };
        |int g(struct value *v) { return v->number; }
        |""".stripMargin)

    def links: List[(String, List[String])] =
      cpg.call
        .name(Operators.fieldAccess, Operators.indirectFieldAccess)
        .map(access => access.code -> access.referencedMember.map(ref => s"${ref.typeDecl.name}.${ref.name}").l)
        .l
        .sortBy(_._1)

    "link each access, the table entries and the members of an anonymous union" in {
      links.filter(_._2.size != 1) shouldBe Nil
      links.filter(_._1.startsWith(".")) shouldBe List(
        ".a"     -> List("tagged.a"),
        ".read"  -> List("ops.read"),
        ".read"  -> List("ops.read"),
        ".read"  -> List("tagged.read"),
        ".write" -> List("ops.write"),
        ".write" -> List("ops.write")
      )
    }

    "reach the function pointer member through a pointer chain" in {
      cpg.call.codeExact("d->ops->read").referencedMember.name.l shouldBe List("read")
      cpg.call.codeExact("tv.read").referencedMember.name.l shouldBe List("read")
    }
  }
}
