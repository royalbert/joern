package io.joern.c2cpg.dataflow

import io.joern.c2cpg.parser.FileDefaults
import io.joern.c2cpg.testfixtures.DataFlowCodeToCpgSuite
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes}
import io.shiftleft.codepropertygraph.generated.nodes.{CfgNode, Identifier}
import io.shiftleft.semanticcpg.language.*

/** A function cannot write a variable of its caller that it receives through a parameter whose evaluation strategy is
  * `BY_COPY`, so the call is no definition of that variable.
  */
class ByValueArgumentFlowTests extends DataFlowCodeToCpgSuite {

  /** The variables that the argument `name` of the calls of `callee` in `method` is stored as defining: the nodes of
    * `method` outside the call that its reaching-definition edges lead to.
    */
  private def definedBy(cpg: Cpg, method: String, callee: String, name: String): List[String] =
    cpg.method
      .nameExact(method)
      .call
      .nameExact(callee)
      .argument
      .isIdentifier
      .nameExact(name)
      .l
      .flatMap { argument =>
        val call = argument.inCall.head
        argument.outE(EdgeTypes.REACHING_DEF).map(_.dst).collect {
          case node: CfgNode if node.method == argument.method && node != call && !call.argument.contains(node) =>
            node.code
        }
      }

  /** The code of the identifiers whose definitions reach the argument of the call of `sink` in `method`. */
  private def definitionsReachingSink(cpg: Cpg, method: String): List[String] =
    cpg.method
      .nameExact(method)
      .call
      .nameExact("sink")
      .argument
      .inE(EdgeTypes.REACHING_DEF)
      .map(_.src)
      .collect { case identifier: Identifier => identifier.code }
      .l

  "A scalar passed by value in a C file" should {
    val cpg = code("""
        |typedef unsigned long size_t;
        |enum color { RED, GREEN };
        |int cond(void);
        |void use(int v) { }
        |void ext(int v);
        |void sink(int v);
        |
        |void guarded(int n) {
        |  if (cond()) use(n);
        |  if (cond()) use(n);
        |  sink(n);
        |}
        |void kinds(size_t len, enum color c) {
        |  int local = 1;
        |  ext(len); ext(c); ext(local);
        |  sink(len + c + local);
        |}
        |""".stripMargin)

    "not be a definition made by a call of a defined function" in {
      definedBy(cpg, "guarded", "use", "n") shouldBe empty
    }

    "not be a definition made by a call of a declared function, whether a local, a typedef or an enum" in {
      definedBy(cpg, "kinds", "ext", "local") shouldBe empty
      definedBy(cpg, "kinds", "ext", "len") shouldBe empty
      definedBy(cpg, "kinds", "ext", "c") shouldBe empty
    }
  }

  "A variable a call may still write" should {
    val cpg = code("""
        |struct pair { int a; int *p; };
        |int g;
        |void ext(int v);
        |void extp(int *p);
        |void exts(struct pair s);
        |void sink(int v);
        |#define SET(x) ((x) = 1)
        |
        |void pointer(int *p) { extp(p); sink(*p); }
        |void taken(int n) { int t = n; int *q = &t; ext(t); sink(t); }
        |void global(void) { ext(g); sink(g); }
        |void bystruct(struct pair s) { exts(s); sink(s.a); }
        |void macro(int n) { SET(n); sink(n); }
        |void assigned(int n) { n = 2; sink(n); }
        |void unparsedMacro(int sr) { ENTER_CRITICAL(sr); sink(sr); }
        |void (*fp)(int);
        |void viaPointer(int n) { fp(n); sink(n); }
        |""".stripMargin)

    "keep the definitions the call makes" in {
      definedBy(cpg, "pointer", "extp", "p") should not be empty
      definedBy(cpg, "taken", "ext", "t") should not be empty
      definedBy(cpg, "global", "ext", "g") should not be empty
      definedBy(cpg, "bystruct", "exts", "s") should not be empty
    }

    "keep the definitions of macro arguments and assignment targets" in {
      definitionsReachingSink(cpg, "macro") should contain("n")
      definitionsReachingSink(cpg, "assigned") should contain("n")
    }

    "keep the definition made by a call without parameter types, such as a macro whose definition is missing" in {
      definedBy(cpg, "unparsedMacro", "ENTER_CRITICAL", "sr") should not be empty
    }

    "keep the definition made by a call through a function pointer" in {
      definitionsReachingSink(cpg, "viaPointer") should contain("n")
    }
  }

  "A scalar passed in a C++ file" should {
    val cpg = code(
      """
        |void byval(int v);
        |void byref(int& v);
        |void var(int a, ...);
        |template <typename T> void tmpl(T v);
        |template <typename T> void forward(T&& v);
        |template <typename T> void tref(T& v);
        |struct S { void m(int v); };
        |void sink(int v);
        |
        |void plain(int n) { byval(n); sink(n); }
        |void variadic(int n) { var(1, n); sink(n); }
        |void member(S s, int n) { s.m(n); sink(n); }
        |void reference(int n) { byref(n); sink(n); }
        |void templated(int n) { tmpl(n); sink(n); }
        |void explicitReference(int n) { tmpl<int&>(n); sink(n); }
        |void forwarding(int n) { forward(n); sink(n); }
        |void templateReference(int n) { tref(n); sink(n); }
        |void unresolved(int n) { undeclared(n); sink(n); }
        |void alsoByReference(int n) { byref(n); byval(n); sink(n); }
        |void boundReference(int n) { int& r = n; byval(n); sink(n); }
        |void captured(int n) { auto l = [&]() { n++; }; byval(n); l(); sink(n); }
        |""".stripMargin,
      s"Test0${FileDefaults.CppExt}"
    )

    "not be a definition by a call whose parameter is a scalar" in {
      definedBy(cpg, "plain", "byval", "n") shouldBe empty
      definedBy(cpg, "member", "m", "n") shouldBe empty
    }

    "keep the definition by a call that takes it through `...` or through a parameter whose type is a template parameter" in {
      definedBy(cpg, "variadic", "var", "n") should not be empty
      definedBy(cpg, "templated", "tmpl", "n") should not be empty
    }

    "keep the definition when the parameter may be a reference" in {
      definedBy(cpg, "reference", "byref", "n") should not be empty
      definedBy(cpg, "explicitReference", "tmpl<int&>", "n") should not be empty
      definedBy(cpg, "forwarding", "forward", "n") should not be empty
      definedBy(cpg, "templateReference", "tref", "n") should not be empty
      definedBy(cpg, "unresolved", "undeclared", "n") should not be empty
    }

    "not be a definition by a call that takes it by value, although other code may write it through a reference" in {
      definedBy(cpg, "alsoByReference", "byval", "n") shouldBe empty
      definedBy(cpg, "alsoByReference", "byref", "n") should not be empty
      definedBy(cpg, "boundReference", "byval", "n") shouldBe empty
      definedBy(cpg, "captured", "byval", "n") shouldBe empty
    }
  }

  "A scalar passed in a header file" should {
    val cpg = code(
      """
        |void use(int v);
        |void sink(int v);
        |static inline void inC(int n) { use(n); sink(n); }
        |""".stripMargin,
      "c.h"
    ).moreCode(
      """
        |void byref(int& v);
        |void sinkCpp(int v);
        |inline void inCpp(int n) { byref(n); sinkCpp(n); }
        |""".stripMargin,
      "cpp.h"
    ).moreCode(
      """
        |void useBoth(int v);
        |void sinkBoth(int v);
        |static inline void inBoth(int n) { useBoth(n); sinkBoth(n); }
        |""".stripMargin,
      "both.h"
    ).moreCode(
      """
        |#include "c.h"
        |#include "both.h"
        |int mainC(void) { return 0; }
        |""".stripMargin,
      "main.c"
    ).moreCode(
      """
        |#include "cpp.h"
        |#include "both.h"
        |int mainCpp() { return 0; }
        |""".stripMargin,
      "main.cpp"
    )

    "not be a definition by a call that takes it by value, whether the header is parsed as C, as C++ or as both" in {
      definedBy(cpg, "inC", "use", "n") shouldBe empty
      cpg.method.nameExact("inBoth").size shouldBe 2
      definedBy(cpg, "inBoth", "useBoth", "n") shouldBe empty
    }

    "keep the definition by a call that takes it by reference" in {
      definedBy(cpg, "inCpp", "byref", "n") should not be empty
    }
  }

  "A variable whose type name two files declare differently" should {
    val cpg = code(
      """
        |typedef int Value;
        |typedef int Count;
        |""".stripMargin,
      "a.c"
    ).moreCode(
      """
        |typedef int* Value;
        |typedef long Count;
        |int sscanf(const char* s, const char* format, ...);
        |void sink(int v);
        |void pointer(Value p) { sscanf("1", "%d", p); sink(*p); }
        |void scalar(Count n) { sscanf("1", "%ld", n); sink(n); }
        |""".stripMargin,
      "b.c"
    )

    "keep the definition when one of the declarations is not a scalar" in {
      cpg.method.nameExact("pointer").parameter.typeFullName.l shouldBe List("Value")
      definedBy(cpg, "pointer", "sscanf", "p") should not be empty
    }

    "keep the definition when the argument is absorbed by `...`, whatever its type" in {
      definedBy(cpg, "scalar", "sscanf", "n") should not be empty
    }
  }

  "A scalar passed to a constructor" should {
    val cpg = code(
      """
        |struct Counter { Counter(int& v) { v++; } };
        |struct Box { Box(int v) { } };
        |void sink(int v);
        |
        |void declared(int n) { Counter c(n); sink(n); }
        |void braced(int n) { Counter c{n}; sink(n); }
        |void temporary(int n) { Counter{n}; sink(n); }
        |void allocated(int n) { Counter* c = new Counter(n); sink(n); }
        |void byValue(int n) { Box b(n); sink(n); }
        |void byValueBraced(int n) { Box b{n}; sink(n); }
        |""".stripMargin,
      s"Test0${FileDefaults.CppExt}"
    )

    "keep the definition when the constructor takes it by reference, however it is called" in {
      List("declared", "braced", "temporary", "allocated").foreach { method =>
        definedBy(cpg, method, "Counter", "n") should not be empty
      }
    }

    "not be a definition when the constructor takes it by value" in {
      definedBy(cpg, "byValue", "Box", "n") shouldBe empty
      definedBy(cpg, "byValueBraced", "Box", "n") shouldBe empty
    }
  }

  "A local whose storage outlives the call" should {
    val cpg = code("""
        |#define STATIC static
        |int g;
        |int depth(int v);
        |void byval(int v);
        |void sink(int v);
        |
        |int counter(int k) { static int n; n = k; depth(n); sink(n); return n; }
        |int viaMacro(int k) { STATIC int m; m = k; depth(m); sink(m); return m; }
        |void blockExtern(void) { extern int g; byval(g); sink(g); }
        |void automatic(int k) { int a = k; byval(a); sink(a); }
        |""".stripMargin)

    "keep the definition a call makes, since the callee or a call it makes can write it" in {
      definedBy(cpg, "counter", "depth", "n") should not be empty
      definedBy(cpg, "viaMacro", "depth", "m") should not be empty
      definedBy(cpg, "blockExtern", "byval", "g") should not be empty
      definedBy(cpg, "automatic", "byval", "a") shouldBe empty
    }
  }

}
