package io.joern.dataflowengineoss.passes.reachingdef

import io.joern.c2cpg.testfixtures.DataFlowCodeToCpgSuite
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.semanticcpg.language.*

/** `UsageAnalyzer` looks for a use's definitions among those sharing a key with it. These tests compare that with
  * filtering all of `in(node)` by `isUsing`, at every node of a method, for each of the tests `isUsing` makes.
  */
class UsageAnalyzerTests extends DataFlowCodeToCpgSuite {

  /** The (use, definition) codes that the index finds, after checking that it finds what the full filter finds. */
  private def usedPairs(method: Method): Set[(String, String)] = {
    val problem      = ReachingDefProblem.create(method)
    val solution     = new DataFlowSolver().calculateMopSolutionForwards(problem)
    val analyzer     = new UsageAnalyzer(problem, solution.in)
    val numberToNode = analyzer.numberToNode
    solution.in.toSeq.flatMap { case (node, incoming) =>
      analyzer.uses(node).toSeq.flatMap { use =>
        val used = analyzer.usedByIndex(use, incoming)
        used shouldBe incoming.filter(definition => analyzer.isUsing(use, numberToNode(definition)))
        used.toSeq.map(definition => use.code -> numberToNode(definition).code)
      }
    }.toSet
  }

  "A use of the same variable" should {
    val cpg = code("""
        |int f(int a, int *p) {
        |  *p = a;
        |  return g(p);
        |}
        |""".stripMargin)

    "be found by the usage index" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        val pairs = usedPairs(method)
        pairs should contain("a" -> "int a")
        pairs should contain("p" -> "*p")
      }
    }
  }

  "A use of a container whose field was defined" should {
    val cpg = code("""
        |struct s { int x; };
        |int f(struct s t) {
        |  t.x = 1;
        |  return g(t);
        |}
        |""".stripMargin)

    "be found by the usage index" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        usedPairs(method) should contain("t" -> "t.x")
      }
    }
  }

  "A use of a part of a defined variable" should {
    val cpg = code("""
        |struct s { int x; };
        |int f(struct s t, struct s u) {
        |  t = u;
        |  return g(t.x);
        |}
        |""".stripMargin)

    "be found by the usage index" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        usedPairs(method) should contain("t.x" -> "t")
      }
    }
  }

  "A use through another spelling of the same access path" should {
    val cpg = code("""
        |struct s { int a; };
        |int f(struct s *p) {
        |  p->a = 1;
        |  return g((*p).a);
        |}
        |""".stripMargin)

    "be found by the usage index" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        usedPairs(method) should contain("(*p).a" -> "p->a")
      }
    }
  }
}
