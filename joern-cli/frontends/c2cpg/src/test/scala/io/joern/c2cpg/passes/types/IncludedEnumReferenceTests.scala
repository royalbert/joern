package io.joern.c2cpg.passes.types

import io.joern.c2cpg.parser.FileDefaults
import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.shiftleft.codepropertygraph.generated.Operators
import io.shiftleft.codepropertygraph.generated.nodes.{Call, FieldIdentifier, Method, TypeRef}
import io.shiftleft.semanticcpg.language.*

class IncludedEnumReferenceTests extends C2CpgSuite {

  "Enumerators of an enum declared in an included header" should {
    "be referenced as field accesses linked to the header's enum members" in {
      val cpg = code(
        """
          |enum color { RED, GREEN, BLUE };
          |typedef enum { MODE_A, MODE_B } color_mode;
          |""".stripMargin,
        "include/colors.h"
      ).moreCode(
        """
          |#include "include/colors.h"
          |enum shade { DARK = BLUE + 1 };
          |int table[3] = { [GREEN] = 7 };
          |int initial = MODE_B;
          |int pick(enum color c) {
          |  switch (c) {
          |    case RED: return 1;
          |    default: break;
          |  }
          |  return c == GREEN ? MODE_A : DARK;
          |}
          |""".stripMargin,
        "main.c"
      )
      def accessesOf(name: String): List[Call] = cpg.call.nameExact(Operators.fieldAccess).codeExact(name).l
      val red                                  = cpg.member.nameExact("RED").l
      val green                                = cpg.member.nameExact("GREEN").l
      val blue                                 = cpg.member.nameExact("BLUE").l
      val modeA                                = cpg.member.nameExact("MODE_A").l
      val modeB                                = cpg.member.nameExact("MODE_B").l
      red.typeDecl.fullName.l shouldBe List("color")
      modeA.typeDecl.fullName.l shouldBe List("color_mode")

      inside(accessesOf("RED")) { case List(access: Call) =>
        access.method.name shouldBe "pick"
        inside(access.argument.l) { case List(base: TypeRef, field: FieldIdentifier) =>
          base.typeFullName shouldBe "color"
          field.canonicalName shouldBe "RED"
        }
        access.referencedMember.l shouldBe red
      }
      inside(accessesOf("MODE_A")) { case List(access: Call) =>
        inside(access.argument.l) { case List(base: TypeRef, _: FieldIdentifier) =>
          base.typeFullName shouldBe "color_mode"
        }
        access.referencedMember.l shouldBe modeA
      }
      accessesOf("GREEN").method.name.l.sorted shouldBe List("<global>", "pick")
      accessesOf("GREEN").referencedMember.l shouldBe green ++ green
      accessesOf("BLUE").method.name.l shouldBe List("<clinit>")
      accessesOf("BLUE").referencedMember.l shouldBe blue
      accessesOf("MODE_B").method.name.l shouldBe List("<global>")
      accessesOf("MODE_B").referencedMember.l shouldBe modeB

      cpg.identifier.nameExact("RED", "GREEN", "BLUE", "MODE_A", "MODE_B").l shouldBe empty
      cpg.local.nameExact("RED", "GREEN", "BLUE", "MODE_A", "MODE_B").l shouldBe empty
    }

    "be referenced as field accesses in another header's inline function" in {
      val cpg = code(
        """
          |enum level { LOW, HIGH };
          |""".stripMargin,
        "level.h"
      ).moreCode(
        """
          |#include "level.h"
          |static inline int is_high(int value) { return value == HIGH; }
          |""".stripMargin,
        "check.h"
      ).moreCode(
        """
          |#include "check.h"
          |int main(void) { return is_high(LOW); }
          |""".stripMargin,
        "main.c"
      )
      val low  = cpg.member.nameExact("LOW").l
      val high = cpg.member.nameExact("HIGH").l
      low.size shouldBe 1
      high.size shouldBe 1
      cpg.method.nameExact("is_high").ast.isCall.nameExact(Operators.fieldAccess).referencedMember.l shouldBe high
      cpg.method.nameExact("main").ast.isCall.nameExact(Operators.fieldAccess).referencedMember.l shouldBe low
      cpg.identifier.nameExact("LOW", "HIGH").l shouldBe empty
      cpg.local.nameExact("LOW", "HIGH").l shouldBe empty
    }

    "reach the enum of the header each file includes when two headers use one enumerator name" in {
      val cpg = code(
        """
          |enum first_state { STATE_IDLE = 1 };
          |""".stripMargin,
        "first.h"
      ).moreCode(
        """
          |enum second_state { STATE_IDLE = 2 };
          |""".stripMargin,
        "second.h"
      ).moreCode(
        """
          |#include "first.h"
          |int first_idle(void) { return STATE_IDLE; }
          |""".stripMargin,
        "first.c"
      ).moreCode(
        """
          |#include "second.h"
          |int second_idle(void) { return STATE_IDLE; }
          |""".stripMargin,
        "second.c"
      )
      val firstIdle  = cpg.typeDecl.fullNameExact("first_state").member.nameExact("STATE_IDLE").l
      val secondIdle = cpg.typeDecl.fullNameExact("second_state").member.nameExact("STATE_IDLE").l
      firstIdle.size shouldBe 1
      secondIdle.size shouldBe 1
      inside(cpg.method.nameExact("first_idle").ast.isCall.nameExact(Operators.fieldAccess).l) {
        case List(access: Call) =>
          inside(access.argument.l) { case List(base: TypeRef, _: FieldIdentifier) =>
            base.typeFullName shouldBe "first_state"
          }
          access.referencedMember.l shouldBe firstIdle
      }
      inside(cpg.method.nameExact("second_idle").ast.isCall.nameExact(Operators.fieldAccess).l) {
        case List(access: Call) =>
          inside(access.argument.l) { case List(base: TypeRef, _: FieldIdentifier) =>
            base.typeFullName shouldBe "second_state"
          }
          access.referencedMember.l shouldBe secondIdle
      }
    }

    "reach the enum of the header each file includes when two headers declare an enum of one name" in {
      val cpg = code(
        """
          |enum board_led { LED_RED, LED_GREEN };
          |""".stripMargin,
        "boards/alpha/board.h"
      ).moreCode(
        """
          |enum board_led { LED_GREEN, LED_RED, LED_BLUE };
          |""".stripMargin,
        "boards/beta/board.h"
      ).moreCode(
        """
          |#include "boards/alpha/board.h"
          |int alpha_led(void) { return LED_RED; }
          |""".stripMargin,
        "alpha.c"
      ).moreCode(
        """
          |#include "boards/beta/board.h"
          |int beta_led(void) { return LED_RED + LED_BLUE; }
          |""".stripMargin,
        "beta.c"
      )
      def declared(file: String, name: String)   = cpg.typeDecl.filenameExact(file).member.nameExact(name).l
      def accesses(method: String, name: String) =
        cpg.method.nameExact(method).ast.isCall.nameExact(Operators.fieldAccess).codeExact(name).l
      declared("boards/alpha/board.h", "LED_RED").size shouldBe 1
      declared("boards/beta/board.h", "LED_RED").size shouldBe 1

      accesses("alpha_led", "LED_RED").referencedMember.l shouldBe declared("boards/alpha/board.h", "LED_RED")
      accesses("beta_led", "LED_RED").referencedMember.l shouldBe declared("boards/beta/board.h", "LED_RED")
      accesses("beta_led", "LED_BLUE").referencedMember.l shouldBe declared("boards/beta/board.h", "LED_BLUE")
    }

    "reach the enum of a header found by its name for an include that does not resolve" in {
      val cpg = code(
        """
          |enum board_led { LED_RED, LED_GREEN };
          |""".stripMargin,
        "boards/alpha/alpha_board.h"
      ).moreCode(
        """
          |enum board_led { LED_GREEN, LED_RED, LED_BLUE };
          |""".stripMargin,
        "boards/beta/beta_board.h"
      ).moreCode(
        """
          |#include "alpha_board.h"
          |int alpha_led(void) { return LED_RED; }
          |""".stripMargin,
        "src/alpha_main.c"
      ).moreCode(
        """
          |#include "beta_board.h"
          |int beta_led(void) { return LED_RED + LED_BLUE; }
          |""".stripMargin,
        "src/beta_main.c"
      )
      def declared(file: String, name: String)   = cpg.typeDecl.filenameExact(file).member.nameExact(name).l
      def accesses(method: String, name: String) =
        cpg.method.nameExact(method).ast.isCall.nameExact(Operators.fieldAccess).codeExact(name).l
      declared("boards/alpha/alpha_board.h", "LED_RED").size shouldBe 1
      declared("boards/beta/beta_board.h", "LED_RED").size shouldBe 1

      accesses("alpha_led", "LED_RED").referencedMember.l shouldBe declared("boards/alpha/alpha_board.h", "LED_RED")
      accesses("beta_led", "LED_RED").referencedMember.l shouldBe declared("boards/beta/beta_board.h", "LED_RED")
      accesses("beta_led", "LED_BLUE").referencedMember.l shouldBe declared("boards/beta/beta_board.h", "LED_BLUE")
    }

    "link the copy a macro call makes of an argument as its original" in {
      val cpg = code(
        """
          |enum board_led { LED_RED, LED_GREEN };
          |""".stripMargin,
        "boards/alpha/board.h"
      ).moreCode(
        """
          |enum board_led { LED_GREEN, LED_RED };
          |""".stripMargin,
        "boards/beta/board.h"
      ).moreCode(
        """
          |#include "boards/beta/board.h"
          |#define PASS(value) (value)
          |#define DEFAULT_LED LED_RED
          |int beta_led(void) { return PASS(LED_RED) + DEFAULT_LED; }
          |""".stripMargin,
        "beta.c"
      )
      def calls    = cpg.method.nameExact("beta_led").ast.isCall
      val member   = cpg.typeDecl.filenameExact("boards/beta/board.h").member.nameExact("LED_RED").l
      val macros   = calls.nameExact("PASS", "DEFAULT_LED").l
      val argument = calls.nameExact("PASS").argument.isCall.nameExact(Operators.fieldAccess).l
      val accesses = calls.nameExact(Operators.fieldAccess).l
      member.size shouldBe 1
      macros.size shouldBe 2
      argument.size shouldBe 1
      accesses.size shouldBe 3
      accesses.referencedMember.l shouldBe List.fill(3)(member.head)
      macros.flatMap(_._refOut) shouldBe empty
    }

    "link only the access when a header defines a constant's name as a macro of itself" in {
      val cpg = code(
        """
          |enum level { LOW, HIGH };
          |#define HIGH HIGH
          |""".stripMargin,
        "level.h"
      ).moreCode(
        """
          |#include "level.h"
          |int high(void) { return HIGH; }
          |""".stripMargin,
        "main.c"
      )
      def calls  = cpg.method.nameExact("high").ast.isCall
      val member = cpg.member.nameExact("HIGH").l
      member.size shouldBe 1
      calls.nameExact("HIGH").size shouldBe 1
      calls.nameExact(Operators.fieldAccess).referencedMember.l shouldBe member
      calls.nameExact("HIGH").flatMap(_._refOut).l shouldBe empty
    }

    "reach the copy parsed in the referencing file's language when C and C++ files include one header" in {
      val cpg = code(
        """
          |enum level { LOW, HIGH };
          |""".stripMargin,
        "level.h"
      ).moreCode(
        """
          |#include "level.h"
          |int c_high(void) { return HIGH; }
          |""".stripMargin,
        "c_side.c"
      ).moreCode(
        """
          |#include "level.h"
          |int cpp_high() { return HIGH; }
          |""".stripMargin,
        "cpp_side.cpp"
      )
      def copyIn(globalMethod: String) =
        cpg.member.nameExact("HIGH").filter(_.typeDecl._astIn.collectAll[Method].fullName.l == List(globalMethod)).l
      copyIn("level.h:<global>").size shouldBe 1
      copyIn("level.h:<global><cpp>").size shouldBe 1

      cpg.method.nameExact("c_high").ast.isCall.nameExact(Operators.fieldAccess).referencedMember.l shouldBe copyIn(
        "level.h:<global>"
      )
      cpg.method.nameExact("cpp_high").ast.isCall.nameExact(Operators.fieldAccess).referencedMember.l shouldBe copyIn(
        "level.h:<global><cpp>"
      )
    }

    "preserve parameter and local shadowing" in {
      val cpg = code(
        """
          |enum action_kind { ACTION = 1 };
          |""".stripMargin,
        "action.h"
      ).moreCode(
        """
          |#include "action.h"
          |int parameter(int ACTION) { return ACTION; }
          |int local(void) { int ACTION = 2; return ACTION; }
          |int enumeration(void) { return ACTION; }
          |""".stripMargin,
        "main.c"
      )
      val member    = cpg.member.nameExact("ACTION").l
      val parameter = cpg.method.nameExact("parameter").parameter.nameExact("ACTION").l
      val local     = cpg.method.nameExact("local").local.nameExact("ACTION").l
      member.size shouldBe 1

      cpg.method.nameExact("parameter").ast.isIdentifier.nameExact("ACTION").refsTo.l shouldBe parameter
      cpg.method.nameExact("local").ast.isIdentifier.nameExact("ACTION").refsTo.l.distinct shouldBe local
      cpg.method
        .nameExact("enumeration")
        .ast
        .isCall
        .nameExact(Operators.fieldAccess)
        .referencedMember
        .l shouldBe member
      cpg.method.nameExact("enumeration").ast.isIdentifier.l shouldBe empty
      cpg.method.nameExact("enumeration").local.l shouldBe empty
    }
  }
}

class CppIncludedEnumReferenceTests extends C2CpgSuite(fileSuffix = FileDefaults.CppExt) {

  "Enumerators of an enum declared in an included header" should {
    "be referenced as field accesses linked to the members of namespace and class enums" in {
      val cpg = code(
        """
          |namespace device {
          |  enum Kind { KIND_NONE, KIND_UART };
          |  class Port {
          |   public:
          |    enum State { STATE_OFF, STATE_ON };
          |    int state();
          |  };
          |}
          |""".stripMargin,
        "device.hpp"
      ).moreCode(
        """
          |#include "device.hpp"
          |int device::Port::state() { return STATE_ON; }
          |int is_uart(device::Kind kind) {
          |  using namespace device;
          |  return kind == KIND_UART;
          |}
          |""".stripMargin,
        "device.cpp"
      )
      val stateOn  = cpg.member.nameExact("STATE_ON").l
      val kindUart = cpg.member.nameExact("KIND_UART").l
      stateOn.typeDecl.fullName.l shouldBe List("device.Port.State")
      kindUart.typeDecl.fullName.l shouldBe List("device.Kind")

      inside(cpg.method.nameExact("state").ast.isCall.nameExact(Operators.fieldAccess).l) { case List(access: Call) =>
        inside(access.argument.l) { case List(base: TypeRef, field: FieldIdentifier) =>
          base.typeFullName shouldBe "device.Port.State"
          field.canonicalName shouldBe "STATE_ON"
        }
        access.referencedMember.l shouldBe stateOn
      }
      inside(cpg.method.nameExact("is_uart").ast.isCall.nameExact(Operators.fieldAccess).l) { case List(access: Call) =>
        inside(access.argument.l) { case List(base: TypeRef, _: FieldIdentifier) =>
          base.typeFullName shouldBe "device.Kind"
        }
        access.referencedMember.l shouldBe kindUart
      }
      cpg.identifier.nameExact("STATE_ON", "KIND_UART").l shouldBe empty
      cpg.local.nameExact("STATE_ON", "KIND_UART").l shouldBe empty
    }
  }
}
