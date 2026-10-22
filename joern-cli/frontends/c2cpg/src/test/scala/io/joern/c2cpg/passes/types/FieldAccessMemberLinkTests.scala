package io.joern.c2cpg.passes.types

import io.joern.c2cpg.testfixtures.C2CpgSuite
import io.shiftleft.codepropertygraph.generated.Operators
import io.shiftleft.codepropertygraph.generated.nodes.Member
import io.shiftleft.semanticcpg.language.*

class FieldAccessMemberLinkTests extends C2CpgSuite {

  private def describe(member: Member): String =
    s"${member.typeDecl.filename}:${member.typeDecl.name}.${member.name}"

  "Field accesses in one file" should {
    val cpg = code("""
        |struct msg { unsigned short len; struct msg *next; };
        |typedef struct cell { int v; struct cell *next; } cell_t;
        |typedef struct msg *msg_p;
        |typedef struct { int w; } anon_t;
        |struct outer { struct msg inner; struct msg *link; struct msg items[2]; };
        |union word { int i; unsigned char b[4]; };
        |struct state { int count; } global_state;
        |struct msg *next_msg(void);
        |int f(struct msg *m, cell_t *c, msg_p mp, anon_t *a, struct msg arr[4], struct outer *o, struct msg **pp,
        |      union word w, void *q) {
        |  struct msg v;
        |  cell_t cv;
        |  return m->len + c->v + mp->len + a->w + arr->len + next_msg()->len + v.len + cv.v
        |    + o->inner.len + o->link->len + o->items[1].len + arr[2].len + (*pp)->len + (&v)->len + m->next->len
        |    + w.i + global_state.count + ((struct msg *)q)->len;
        |}
        |""".stripMargin)

    def membersOf(access: String): List[String] =
      cpg.fieldAccess.codeExact(access).referencedMember.map(describe).l

    "link an access through a pointer to a struct" in {
      membersOf("m->len") shouldBe List("Test0.c:msg.len")
    }

    "link accesses through typedefs of a struct, of a pointer and of an anonymous struct" in {
      membersOf("c->v") shouldBe List("Test0.c:cell.v")
      membersOf("cv.v") shouldBe List("Test0.c:cell.v")
      membersOf("mp->len") shouldBe List("Test0.c:msg.len")
      membersOf("a->w") shouldBe List("Test0.c:anon_t.w")
    }

    "link accesses through an array, a call, a dereference and an address" in {
      membersOf("arr->len") shouldBe List("Test0.c:msg.len")
      membersOf("next_msg()->len") shouldBe List("Test0.c:msg.len")
      membersOf("(*pp)->len") shouldBe List("Test0.c:msg.len")
      membersOf("(&v)->len") shouldBe List("Test0.c:msg.len")
      membersOf("arr[2].len") shouldBe List("Test0.c:msg.len")
    }

    "link nested accesses at every level" in {
      membersOf("o->inner") shouldBe List("Test0.c:outer.inner")
      membersOf("o->inner.len") shouldBe List("Test0.c:msg.len")
      membersOf("o->link->len") shouldBe List("Test0.c:msg.len")
      membersOf("o->items[1].len") shouldBe List("Test0.c:msg.len")
      membersOf("m->next->len") shouldBe List("Test0.c:msg.len")
    }

    "link a union's member, a struct defined with its variable, and the accesses that linked before" in {
      membersOf("w.i") shouldBe List("Test0.c:word.i")
      membersOf("global_state.count") shouldBe List("Test0.c:state.count")
      membersOf("v.len") shouldBe List("Test0.c:msg.len")
      membersOf("((struct msg *)q)->len") shouldBe List("Test0.c:msg.len")
    }

    "leave every access with exactly one member" in {
      cpg.fieldAccess.filter(_.referencedMember.size != 1).code.l shouldBe empty
    }
  }

  "Field accesses to structs of the same name in two folders" should {
    val cpg = code(
      """
        |#include "regs.h"
        |int first(regs_t *r) { return r->ctrl; }
        |""".stripMargin,
      "one/drv.c"
    ).moreCode(
      """
        |typedef struct regs { int ctrl; } regs_t;
        |""".stripMargin,
      "one/regs.h"
    ).moreCode(
      """
        |#include "regs.h"
        |int second(regs_t *r) { return r->status + r->ctrl; }
        |""".stripMargin,
      "two/drv.c"
    ).moreCode(
      """
        |typedef struct regs { int status; int ctrl; } regs_t;
        |""".stripMargin,
      "two/regs.h"
    )

    def membersIn(method: String): List[String] =
      cpg.method
        .nameExact(method)
        .ast
        .isCall
        .name(Operators.fieldAccess, Operators.indirectFieldAccess)
        .referencedMember
        .map(describe)
        .l
        .sorted

    "reach the definition in the header each file includes" in {
      membersIn("first") shouldBe List("one/regs.h:regs.ctrl")
      membersIn("second") shouldBe List("two/regs.h:regs.ctrl", "two/regs.h:regs.status")
    }
  }

  "Field accesses to a struct a header defines once per configuration" should {
    val cpg = code(
      """
        |#include "chip.h"
        |int level(chip_t *c) { return c->level; }
        |""".stripMargin,
      "drv.c"
    ).moreCode(
      """
        |#ifdef CHIP_A
        |typedef struct chip { int level; int mode; } chip_t;
        |#else
        |typedef struct chip { int mode; int level; } chip_t;
        |#endif
        |""".stripMargin,
      "chip.h"
    )

    "reach the definition of the active configuration" in {
      cpg.typeDecl.nameExact("chip").size shouldBe 2
      cpg.fieldAccess.codeExact("c->level").referencedMember.map(member => (describe(member), member.order)).l shouldBe
        List(("chip.h:chip.level", 2))
    }
  }

  "A field access to a struct whose body declares a member in each branch of an #if" should {
    val cpg = code(
      """
        |#include "regs.h"
        |unsigned int low(struct regs *r) { return r->lo; }
        |""".stripMargin,
      "drv.c"
    ).moreCode(
      """struct regs {
        |#ifdef BIG_ENDIAN_REGS
        |  unsigned int hi;
        |  unsigned int lo;
        |#else
        |  unsigned int lo;
        |  unsigned int hi;
        |#endif
        |};
        |""".stripMargin,
      "regs.h"
    )

    "reach the member of the branch the access's file sees" in {
      cpg.typeDecl.nameExact("regs").member.map(member => member.name -> member.lineNumber).l shouldBe List(
        "hi" -> Some(3),
        "lo" -> Some(4),
        "lo" -> Some(6),
        "hi" -> Some(7)
      )
      cpg.fieldAccess.codeExact("r->lo").referencedMember.lineNumber.l shouldBe List(6)
    }
  }

  "A field access to a struct that an earlier header only declares" should {
    val cpg = code(
      """
        |#include "a_forward.h"
        |#include "b_define.h"
        |int count(struct ctx *c) { return c->n; }
        |""".stripMargin,
      "main.c"
    ).moreCode("struct ctx;\nint use_ctx(struct ctx *c);\n", "a_forward.h")
      .moreCode("struct ctx { int n; };\n", "b_define.h")

    "reach the member of the definition" in {
      cpg.fieldAccess.codeExact("c->n").referencedMember.map(describe).l shouldBe List("b_define.h:ctx.n")
    }
  }

  "A field access to a member of an anonymous union" should {
    val cpg = code("""
        |struct value { int kind; union { int number; float real; }; };
        |int get(struct value *v) { return v->kind + v->number; }
        |""".stripMargin)

    "reach the member in the anonymous union" in {
      cpg.fieldAccess.codeExact("v->kind").referencedMember.name.l shouldBe List("kind")
      cpg.fieldAccess.codeExact("v->number").referencedMember.name.l shouldBe List("number")
    }
  }

  "Field accesses to two structs one macro defines" should {
    val cpg = code("""
        |#define TWO(a, b) struct a { int x; }; struct b { int y; };
        |TWO(first, second)
        |int f(struct first *p, struct second *q) { return p->x + q->y; }
        |""".stripMargin)

    "reach each struct's member" in {
      cpg.fieldAccess.codeExact("p->x").referencedMember.map(describe).l shouldBe List("Test0.c:first.x")
      cpg.fieldAccess.codeExact("q->y").referencedMember.map(describe).l shouldBe List("Test0.c:second.y")
    }
  }

  "Field accesses to a struct a macro names differently in the header's own parse" should {
    val cpg = code(
      """
        |#define REG_STRUCT(name) struct name##_regs { int id; int ctrl; };
        |#include "regs.h"
        |int f(struct uart_regs *r) { return r->id + r->ctrl; }
        |""".stripMargin,
      "drv.c"
    ).moreCode(
      """
        |#ifndef REG_STRUCT
        |#define REG_STRUCT(name) struct name##_desc { int id; int flags; };
        |#endif
        |REG_STRUCT(uart)
        |""".stripMargin,
      "regs.h"
    )

    "not reach the other struct the header's own parse defines at the same place" in {
      cpg.typeDecl.nameExact("uart_desc").member.name.l shouldBe List("id", "flags")
      cpg.fieldAccess.codeExact("r->id").referencedMember.l shouldBe empty
      cpg.fieldAccess.codeExact("r->ctrl").referencedMember.l shouldBe empty
    }
  }

  "Field accesses to anonymous members one macro defines" should {
    val cpg = code(
      """
        |#include "params.h"
        |int f(struct params *p) { return p->flags + p->level + p->count; }
        |""".stripMargin,
      "main.c"
    ).moreCode(
      """
        |#define SET_MEMBER(member, start, end) union { member; unsigned char reserved##end[(end) - (start)]; }
        |struct params {
        |  SET_MEMBER(unsigned long flags, 0, 8);
        |  SET_MEMBER(struct { int level; int count; }, 8, 16);
        |};
        |""".stripMargin,
      "params.h"
    )

    "reach the member of the anonymous struct or union that declares it" in {
      List("p->flags", "p->level", "p->count").map { access =>
        cpg.fieldAccess
          .codeExact(access)
          .referencedMember
          .map(member => member.name -> member.typeDecl.member.name.l)
          .l
      } shouldBe List(
        List("flags" -> List("flags", "reserved8")),
        List("level" -> List("level", "count")),
        List("count" -> List("level", "count"))
      )
    }
  }

  "A field access in a macro argument" should {
    val cpg = code("""
        |#define READ(x) (x)
        |struct msg { int len; };
        |int f(struct msg *m) { return READ(m->len); }
        |""".stripMargin)

    "be linked in the expansion and in the macro call's argument" in {
      val accesses = cpg.fieldAccess.codeExact("m->len").l
      accesses.size shouldBe 2
      accesses.map(_.referencedMember.name.l) shouldBe List(List("len"), List("len"))
    }
  }

  "C++ member accesses" should {
    val cpg = code(
      """
        |class Base { public: int base; };
        |class Counter : public Base {
        | public:
        |  int count;
        |  void inc() { this->count++; count++; }
        |};
        |int read(Counter &r, Counter *p) { return r.count + p->count + p->base; }
        |class Pool { public: int created; static int pools; Pool() : created(0) {} };
        |int pools() { return Pool::pools; }
        |""".stripMargin,
      "test.cpp"
    )

    "link a static member accessed through its class's name" in {
      cpg.fieldAccess.codeExact("Pool::pools").referencedMember.map(describe).l shouldBe List("test.cpp:Pool.pools")
    }

    "link a member set in a constructor's initializer list" in {
      cpg.method
        .nameExact("Pool")
        .ast
        .isCall
        .name(Operators.indirectFieldAccess)
        .map(access => access.code -> access.referencedMember.map(describe).l)
        .l shouldBe List("this->created" -> List("test.cpp:Pool.created"))
    }

    "link this->x, an implicit this, a reference, a pointer and an inherited member" in {
      cpg.fieldAccess
        .map(access => access.code -> access.referencedMember.map(describe).l)
        .l
        .sortBy(_._1) shouldBe List(
        "Pool::pools"   -> List("test.cpp:Pool.pools"),
        "p->base"       -> List("test.cpp:Base.base"),
        "p->count"      -> List("test.cpp:Counter.count"),
        "r.count"       -> List("test.cpp:Counter.count"),
        "this->count"   -> List("test.cpp:Counter.count"),
        "this->count"   -> List("test.cpp:Counter.count"),
        "this->created" -> List("test.cpp:Pool.created")
      )
    }
  }

  "Field accesses to members of C++ class template specializations" should {
    val cpg = code(
      """
        |template <typename T> struct Box { T val; int tag; };
        |template <> struct Box<char> { char c; int tag; int extra; int get() { return tag + extra; } };
        |template <> struct Box<long> { long tag; };
        |template <typename T> struct Box<T *> { T *ptr; int tag; };
        |int u1(Box<char> *c) { return c->tag + c->extra; }
        |int u2(Box<long> &l) { return (int)l.tag; }
        |int u3(Box<int> b) { return b.tag; }
        |int u4(Box<int *> p) { return p.tag; }
        |""".stripMargin,
      "test.cpp"
    )

    def memberLines(access: String): List[Int] =
      cpg.fieldAccess.codeExact(access).referencedMember.lineNumber.l

    "reach the member of the explicit specialization the access's type is" in {
      memberLines("c->tag") shouldBe List(3)
      memberLines("c->extra") shouldBe List(3)
      memberLines("l.tag") shouldBe List(4)
    }

    "reach the explicit specialization's own member through an implicit this" in {
      cpg.fieldAccess.codeExact("this->tag").lineNumber(3).referencedMember.lineNumber.l shouldBe List(3)
      cpg.fieldAccess.codeExact("this->extra").lineNumber(3).referencedMember.lineNumber.l shouldBe List(3)
    }

    "reach the member of the template or partial specialization an implicit instantiation is made from" in {
      memberLines("b.tag") shouldBe List(2)
      memberLines("p.tag") shouldBe List(5)
    }
  }

  "Field accesses to a struct of a header parsed both as C and as C++" should {
    val cpg = code(
      """
        |#include "point.h"
        |int cx(struct point *p) { return p->x; }
        |""".stripMargin,
      "main.c"
    ).moreCode(
      """
        |#include "point.h"
        |int cppx(point *p) { return p->x; }
        |""".stripMargin,
      "other.cpp"
    ).moreCode("struct point { int x; };\n", "point.h")

    "reach the member of the parse in the access's own language" in {
      val members = cpg.member.nameExact("x").l
      members.size shouldBe 2
      val fromC   = cpg.method.nameExact("cx").ast.isCall.codeExact("p->x").referencedMember.l
      val fromCpp = cpg.method.nameExact("cppx").ast.isCall.codeExact("p->x").referencedMember.l
      fromC.size shouldBe 1
      fromCpp.size shouldBe 1
      fromC should not be fromCpp
      fromC.typeDecl.astParent.isMethod.fullName.l.exists(_.endsWith("<cpp>")) shouldBe false
      fromCpp.typeDecl.astParent.isMethod.fullName.l.exists(_.endsWith("<cpp>")) shouldBe true
    }
  }

  "A field access CDT cannot resolve" should {
    val cpg = code("""
        |int f(struct unknown *u) { return u->x; }
        |""".stripMargin)

    "stay unlinked" in {
      cpg.fieldAccess.codeExact("u->x").referencedMember.l shouldBe empty
    }
  }

}
