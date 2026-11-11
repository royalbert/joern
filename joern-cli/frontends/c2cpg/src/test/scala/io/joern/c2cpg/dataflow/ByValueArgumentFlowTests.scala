package io.joern.c2cpg.dataflow

import io.joern.c2cpg.parser.FileDefaults
import io.joern.c2cpg.testfixtures.DataFlowCodeToCpgSuite
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes}
import io.shiftleft.codepropertygraph.generated.nodes.{CfgNode, Identifier}
import io.shiftleft.semanticcpg.language.*

/** A function cannot write a scalar variable of its caller that it receives by value, so the call is no definition of
  * that variable. C passes every argument by value; in C++ the parameter must be a scalar, not a reference.
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
  }

  "A scalar passed in a C++ file" should {
    val cpg = code(
      """
        |void byval(int v);
        |void byref(int& v);
        |void var(int a, ...);
        |template <typename T> void tmpl(T v);
        |struct S { void m(int v); };
        |void sink(int v);
        |
        |void plain(int n) { byval(n); sink(n); }
        |void variadic(int n) { var(1, n); sink(n); }
        |void member(S s, int n) { s.m(n); sink(n); }
        |void reference(int n) { byref(n); sink(n); }
        |void templated(int n) { tmpl(n); sink(n); }
        |void unresolved(int n) { undeclared(n); sink(n); }
        |void alsoByReference(int n) { byref(n); byval(n); sink(n); }
        |void boundReference(int n) { int& r = n; byval(n); sink(n); }
        |void captured(int n) { auto l = [&]() { n++; }; byval(n); l(); sink(n); }
        |""".stripMargin,
      s"Test0${FileDefaults.CppExt}"
    )

    "not be a definition by a call whose parameter is a scalar, or that takes it through `...`" in {
      definedBy(cpg, "plain", "byval", "n") shouldBe empty
      definedBy(cpg, "variadic", "var", "n") shouldBe empty
      definedBy(cpg, "member", "m", "n") shouldBe empty
    }

    "keep the definition when the parameter may be a reference" in {
      definedBy(cpg, "reference", "byref", "n") should not be empty
      definedBy(cpg, "templated", "tmpl", "n") should not be empty
      definedBy(cpg, "unresolved", "undeclared", "n") should not be empty
    }

    "keep the definition when the variable may be bound to a reference elsewhere in the method" in {
      definedBy(cpg, "alsoByReference", "byval", "n") should not be empty
      definedBy(cpg, "boundReference", "byval", "n") should not be empty
      definedBy(cpg, "captured", "byval", "n") should not be empty
    }
  }

}
