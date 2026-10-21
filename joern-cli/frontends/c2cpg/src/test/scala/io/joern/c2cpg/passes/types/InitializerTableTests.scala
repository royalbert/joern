package io.joern.c2cpg.passes.types

import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.language.operatorextension.OpNodes

// Object-oriented C sets a struct's methods in an initializer table as often as by assignment:
// `static const struct ops uart_ops = { .putc = uart_putc, ... };`. Each entry must reach the member it sets.
class InitializerTableTests extends C2CpgSuite {

  "Entries of initializer tables" should {
    val cpg = code("""
        |struct ops { int (*read)(int); int (*write)(int); int flags; };
        |static int r(int x) { return x; }
        |static int w(int x) { return x; }
        |static const struct ops designated = { .read = r, .write = w };
        |static const struct ops positional = { r, w, 3 };
        |static const struct ops mixed = { .write = w, 7 };
        |struct ops table[2] = { { .read = r }, { r, w } };
        |struct dev { const struct ops *ops; struct ops inline_ops; };
        |static struct dev d = { .ops = &designated, .inline_ops = { .read = r } };
        |union u { int (*f)(int); long l; };
        |static union u un = { r };
        |""".stripMargin)

    /** (member, function) for every initializer entry that sets a member to a function. */
    def entries(variable: String): List[(String, String)] =
      cpg.assignment
        .filter(_.code.startsWith("."))
        .filter(_.inAst.isCall.nameExact("<operator>.assignment").argument(1).code.l.contains(variable))
        .flatMap { assignment =>
          val member = Iterator(assignment.target).isCall
            .collectAll[OpNodes.FieldAccess]
            .referencedMember
            .map(field => s"${field.typeDecl.fullName}.${field.name}")
            .l
          val fn = Iterator(assignment.source).isMethodRef.methodFullName.l
          for { set <- member; function <- fn } yield (set, function)
        }
        .l
        .sortBy(identity)

    /** The name of the member the initializer entry `code` sets. */
    def memberSetBy(code: String): List[String] =
      cpg.assignment.codeExact(code).target.isCall.collectAll[OpNodes.FieldAccess].referencedMember.name.l

    "link a designated entry to its member" in {
      entries("designated") shouldBe List("ops.read" -> "r", "ops.write" -> "w")
    }

    "link a positional entry to the member at its position" in {
      entries("positional") shouldBe List("ops.read" -> "r", "ops.write" -> "w")
      memberSetBy(".flags = 3") shouldBe List("flags")
    }

    "continue the position after a designated entry" in {
      memberSetBy(".flags = 7") shouldBe List("flags")
    }

    "reach every table in an array of tables" in {
      entries("table") shouldBe List("ops.read" -> "r", "ops.read" -> "r", "ops.write" -> "w")
    }

    "reach a table nested in another struct's initializer" in {
      entries("d") shouldBe List("ops.read" -> "r")
    }

    "leave a union's positional entry as it is" in {
      cpg.assignment
        .filter(_.code.contains("= r"))
        .filter(_.inAst.isCall.argument(1).code.l.contains("un")) shouldBe empty
    }
  }

  "The object an initializer table entry sets a member of" should {
    val cpg = code("""
        |struct ops { int (*putc)(int); int (*getc)(void); };
        |struct outer { int x; struct ops o; };
        |int up(int c) { return c; }
        |int ug(void) { return 0; }
        |static const struct ops uart = { up, ug };
        |static const struct ops dbg = { .getc = ug };
        |static const struct ops many[2] = { { up }, { .putc = up } };
        |static struct outer ou = { 1, { up } };
        |""".stripMargin)

    "be the variable the table initializes, or its element or member" in {
      val bases = cpg.assignment.target.isCall.nameExact("<operator>.fieldAccess").argument(1).code.l.sorted
      bases shouldBe List("dbg", "many[0]", "many[1]", "ou", "ou", "ou.o", "uart", "uart")
    }

    "refer to that variable, not to a name made from its type" in {
      cpg.identifier.nameExact("ops", "outer") shouldBe empty
      cpg.identifier
        .nameExact("uart", "dbg", "many", "ou")
        .refsTo
        .collectAll[io.shiftleft.codepropertygraph.generated.nodes.Local]
        .name
        .l
        .distinct
        .sorted shouldBe
        List("dbg", "many", "ou", "uart")
    }
  }

  "A designated entry with several designators" should {
    val cpg = code("""
        |struct ops { int (*read)(int); };
        |struct dev { int id; struct ops ops; };
        |static int r(int x) { return x; }
        |static struct dev d = { .ops.read = r };
        |""".stripMargin)

    "set only the member its last designator names, on the object the others lead to" in {
      val targets = cpg.assignment.target.isCall.collectAll[OpNodes.FieldAccess].l
      targets.flatMap(_.referencedMember.map(member => s"${member.typeDecl.fullName}.${member.name}")) shouldBe List(
        "ops.read"
      )
      targets.map(_.argument(1).code) shouldBe List("d.ops")
    }
  }

  "An entry whose array designator's index is a macro or an enum constant" should {
    val cpg = code("""
        |#define ALT0 0
        |enum { ALT1 = 1 };
        |struct daisy_alt { int offset; int sel; };
        |struct daisy { struct daisy_alt alts[2]; };
        |static const struct daisy g_daisy[] = { { { [ALT0].offset = 1, [ALT0].sel = 2, [ALT1].offset = 3 } } };
        |""".stripMargin)

    "keep the index and set the member of the element it names" in {
      val targets =
        cpg.assignment.target.isCall.collectAll[OpNodes.FieldAccess].filter(_.argument(1).code.startsWith("g_daisy")).l
      // A macro's index shows expanded, as c2cpg shows macro arguments elsewhere.
      targets.map(target => (target.argument(1).code, target.referencedMember.name.l)).sortBy(_._1) shouldBe List(
        ("g_daisy[0]", List("alts")),
        ("g_daisy[0].alts[0]", List("offset")),
        ("g_daisy[0].alts[0]", List("sel")),
        ("g_daisy[0].alts[ALT1]", List("offset"))
      )
      cpg.fieldAccess.fieldIdentifier.canonicalNameExact("ALT1").l should not be empty
    }
  }
}

class InitializerTableUnnamedMemberTests extends C2CpgSuite {

  "A positional entry after an unnamed bit-field" should {
    val cpg = code("""
        |struct regs { int ctrl; int : 3; int status; };
        |struct regs r = { 1, 2 };
        |""".stripMargin)

    "set the next named member" in {
      cpg.assignment
        .filter(_.code.startsWith("."))
        .map(assignment =>
          assignment.code -> Iterator(assignment.target).isCall.collectAll[OpNodes.FieldAccess].referencedMember.name.l
        )
        .l
        .sortBy(_._1) shouldBe List(".ctrl = 1" -> List("ctrl"), ".status = 2" -> List("status"))
    }
  }
}

class InitializerTableElidedBracesTests extends C2CpgSuite {

  "Positional entries whose braces are elided" should {
    val cpg = code("""
        |struct inner { int a; int b; };
        |struct outer { struct inner in; int c; };
        |struct outer elided = { 1, 2, 3 };
        |struct outer resumed = { 1, 2, .c = 3 };
        |struct inner some_inner;
        |struct outer whole = { some_inner, 4 };
        |struct named { char name[8]; int id; };
        |struct named n = { "uart", 5 };
        |""".stripMargin)

    /** (entry, member) of every initializer entry tied to a member, for the variable on `line`. */
    def ties(line: Int): List[(String, String)] =
      cpg.assignment
        .filter(_.code.startsWith("."))
        .lineNumber(line)
        .flatMap(assignment =>
          Iterator(assignment.target).isCall
            .collectAll[OpNodes.FieldAccess]
            .referencedMember
            .map(assignment.code -> _.name)
        )
        .l
        .sorted

    "tie no entry to a member it does not set" in {
      ties(4) shouldBe empty
    }

    "tie the entries again from a designator" in {
      ties(5) shouldBe List(".c = 3" -> "c")
    }

    "tie an entry that sets the member whole" in {
      ties(7) shouldBe List(".c = 4" -> "c", ".in = some_inner" -> "in")
      ties(9) shouldBe List(".id = 5" -> "id", """.name = "uart"""" -> "name")
    }
  }
}

class InitializerTableArrayDesignatorTests extends C2CpgSuite {

  "Positional entries of a table set through an array designator" should {
    val cpg = code("""
        |struct ops { int (*read)(int); int (*write)(int); };
        |static int r(int x) { return x; }
        |static int w(int x) { return x; }
        |struct ops one[3] = { [1] = { r, w } };
        |struct ops range[4] = { [0 ... 1] = { r, w } };
        |struct dev { struct ops ops[2]; };
        |struct dev d = { .ops[1] = { r, w } };
        |""".stripMargin)

    /** The members set to a function by the entries on `line`. */
    def members(line: Int): List[String] =
      cpg.assignment
        .filter(_.code.startsWith("."))
        .lineNumber(line)
        .filter(assignment => Iterator(assignment.source).isMethodRef.nonEmpty)
        .flatMap(assignment => Iterator(assignment.target).isCall.collectAll[OpNodes.FieldAccess].referencedMember.name)
        .l
        .distinct
        .sorted

    "set the members of the element the designator names" in {
      members(5) shouldBe List("read", "write")
      members(6) shouldBe List("read", "write")
      members(8) shouldBe List("read", "write")
    }
  }
}

class InitializerTableArrayDesignatedListTests extends C2CpgSuite {

  "An entry with an array designator whose value is a list" should {
    val cpg = code("""
        |#define SLOT 1
        |enum { IDX_A, IDX_B, IDX_MAX };
        |struct ops { int (*read)(int); int (*write)(int); int flags; };
        |int r(int c) { return c; }
        |static struct ops arr[IDX_MAX] = { [IDX_B] = { r }, [SLOT - 1] = { .write = r } };
        |""".stripMargin)

    "assign to the element it designates, not to its index" in {
      cpg.assignment.code("\\[.*").target.code.l.sorted shouldBe List("arr[IDX_B]", "arr[SLOT - 1]")
    }
  }
}

class InitializerTableNestedPositionTests extends C2CpgSuite {

  "A nested table list" should {
    val cpg = code("""
        |struct rd { int (*read)(int); };
        |struct wr { int (*write)(int); };
        |static int r(int x) { return x; }
        |static int w(int x) { return x; }
        |struct dev { int id; int : 4; struct rd in; struct wr out; };
        |struct dev after_unnamed = { 1, { r }, { w } };
        |struct dev after_designator = { .in = { r }, { w } };
        |""".stripMargin)

    /** (member, function) for each entry on `line` that sets a member to a function. */
    def entries(line: Int): List[(String, String)] =
      cpg.assignment
        .filter(_.code.startsWith("."))
        .lineNumber(line)
        .flatMap { assignment =>
          val member = Iterator(assignment.target).isCall.collectAll[OpNodes.FieldAccess].referencedMember.name.l
          member.flatMap(set => Iterator(assignment.source).isMethodRef.methodFullName.map(set -> _).l)
        }
        .l
        .sorted

    "fill the member at its position, as a positional entry does" in {
      entries(7) shouldBe List("read" -> "r", "write" -> "w")
      entries(8) shouldBe List("read" -> "r", "write" -> "w")
    }
  }
}

class InitializerTableUndefinedStructTests extends C2CpgSuite {

  "A table whose struct is not defined in the file" should {
    val cpg = code("""
        |static struct cfg_param table[] = { { 0x10, 0x0 }, { 0x11, 0x1 } };
        |static struct cfg_param one = { 0x12, 0x2 };
        |""".stripMargin)

    "leave its entries as they are, since their members are unknown" in {
      cpg.assignment.code.filter(_.startsWith(".")).l shouldBe empty
      cpg.call.nameExact("<operator>.arrayInitializer").argument.isLiteral.code.l.sorted shouldBe
        List("0x0", "0x1", "0x10", "0x11", "0x12", "0x2")
    }
  }
}
