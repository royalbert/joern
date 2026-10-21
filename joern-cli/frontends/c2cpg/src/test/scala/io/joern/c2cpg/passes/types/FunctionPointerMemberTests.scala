package io.joern.c2cpg.passes.types

import io.joern.c2cpg.parser.FileDefaults
import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.language.operatorextension.OpNodes

// Object-oriented C: a struct whose function pointer members are its methods.
class FunctionPointerMemberTests extends C2CpgSuite {

  "Function pointer members of a C struct" should {
    val cpg = code("""
        |struct rng_engine {
        |  int (*generate_random_buffer)(struct rng_engine *engine, unsigned long len, unsigned char *buf);
        |  unsigned int state;
        |};
        |static int mbedtls_generate(struct rng_engine *engine, unsigned long len, unsigned char *buf) { return 0; }
        |struct rng_engine engine;
        |void rng_init(void) { engine.generate_random_buffer = mbedtls_generate; }
        |int fill(unsigned char *buf) { return engine.generate_random_buffer(&engine, 16, buf); }
        |""".stripMargin)

    "be members of the struct, not variables" in {
      cpg.typeDecl.nameExact("rng_engine").member.name.l.sorted shouldBe List("generate_random_buffer", "state")
      cpg.local.nameExact("generate_random_buffer") shouldBe empty
    }

    "be reached by a call through the object, and by the assignment that sets the method" in {
      val callee = cpg.call.nameExact("<operator>.pointerCall").receiver.isCall.collectAll[OpNodes.FieldAccess]
      callee.referencedMember.map(member => s"${member.typeDecl.fullName}.${member.name}").l shouldBe List(
        "rng_engine.generate_random_buffer"
      )
      val setter = cpg.assignment.target.isCall.collectAll[OpNodes.FieldAccess]
      setter.referencedMember.name.l shouldBe List("generate_random_buffer")
    }
  }
}

class FunctionPointerMemberCppTests extends C2CpgSuite(FileDefaults.CppExt) {

  "Function pointer members of a C++ class" should {
    val cpg = code("""
        |class A {
        |  public:
        |    void (*foo)(int);
        |};
        |""".stripMargin)

    "be members of the class" in {
      cpg.typeDecl.nameExact("A").member.name.l shouldBe List("foo")
    }
  }

  "A static function pointer member defined outside its class" should {
    val cpg = code("""
        |struct S { static int (*fp)(int); };
        |int (*S::fp)(int) = nullptr;
        |""".stripMargin)

    "be one member, of its class" in {
      cpg.member.nameExact("fp").typeDecl.fullName.l shouldBe List("S")
    }

    "be set by its definition, which declares no variable" in {
      cpg.local.nameExact("fp") shouldBe empty
      cpg.assignment.target.isCall
        .collectAll[OpNodes.FieldAccess]
        .referencedMember
        .map(member => s"${member.typeDecl.fullName}.${member.name}")
        .l shouldBe List("S.fp")
    }
  }
}
