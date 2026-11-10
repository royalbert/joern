package io.joern.dataflowengineoss.passes.reachingdef

import io.joern.c2cpg.testfixtures.DataFlowCodeToCpgSuite
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.semanticcpg.language.*

import scala.collection.mutable

/** One case per condition `isUsing` matches under, each with a method that exercises it. */
class UsageAnalyzerTests extends DataFlowCodeToCpgSuite {

  /** Returns the (use, definition) code pairs the index finds in `method`, after checking at every node that the index
    * finds what filtering all of `in(node)` with `isUsing` finds.
    */
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

  "A use of a field through a pointer to the struct" should {
    val cpg = code("""
        |struct s { int a; int b; };
        |int f(int x) {
        |  struct s v;
        |  struct s *p = &v;
        |  p->a = x;
        |  v.b = x;
        |  return g(v.a) + g(p->b);
        |}
        |""".stripMargin)

    "be found by the usage index" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        val pairs = usedPairs(method)
        pairs should contain("v.a" -> "p->a")
        pairs should contain("p->b" -> "v.b")
      }
    }
  }

  "The definitions a use uses" should {
    // 3,000 assignments before the code under test, so that its definitions are numbered above 6,000.
    val assignments = (1 to 3000).map(i => s"  int v$i = $i;").mkString("\n")
    val cpg         = code(s"""
        |int f(int c) {
        |$assignments
        |  int x = 0;
        |  if (c == 1) x = 1;
        |  else if (c == 2) x = 2;
        |  else if (c == 3) x = 3;
        |  else if (c == 4) x = 4;
        |  else x = 5;
        |  int y = c;
        |  return g(x) + h(y);
        |}
        |""".stripMargin)

    /** For every node of `method` and every use at it, the definitions the use uses. */
    def usedSets(method: Method): Seq[(CfgNode, CfgNode, collection.Set[Int])] = {
      val problem  = ReachingDefProblem.create(method)
      val solution = new DataFlowSolver().calculateMopSolutionForwards(problem)
      val analyzer = new UsageAnalyzer(problem, solution.in)
      analyzer.usedIncomingDefs.toSeq.flatMap { case (node, byUse) =>
        byUse.toSeq.map { case (use, used) => (node, use, used) }
      }
    }

    "be kept without a bit set as long as their highest number" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        val usesOfY = usedSets(method).collect {
          case (call: Call, use, used) if call.name == "h" && use.code == "y" => used
        }
        usesOfY should not be empty
        usesOfY.foreach { used =>
          used.size should be <= 4
          used.min should be > 6000
          used should not be a[mutable.BitSet]
        }
      }
    }

    "be handed out in ascending order" in {
      inside(cpg.method.nameExact("f").l) { case List(method) =>
        val sets = usedSets(method).map(_._3)
        sets.foreach(used => used.toSeq shouldBe used.toSeq.sorted)
        sets.exists(used => used.size > 4 && !used.isInstanceOf[mutable.BitSet]) shouldBe true
      }
    }
  }
}
