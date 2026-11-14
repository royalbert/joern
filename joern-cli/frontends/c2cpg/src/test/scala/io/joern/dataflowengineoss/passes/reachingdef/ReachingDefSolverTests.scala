package io.joern.dataflowengineoss.passes.reachingdef

import io.joern.c2cpg.testfixtures.DataFlowCodeToCpgSuite
import io.shiftleft.semanticcpg.language.*

/** [[ReachingDefSolver]] must reach the fixpoint [[DataFlowSolver]] reaches: the same `in` and `out` at every node, and
  * the same `in` read through its views, in the same order.
  */
class ReachingDefSolverTests extends DataFlowCodeToCpgSuite {

  private val programs = Map(
    "straight line and a branch" -> """
        |int f(int c) {
        |  int x = 1;
        |  if (c) x = 2;
        |  g(x);
        |  x = x + c;
        |  return x;
        |}
        |""".stripMargin,
    "nested loops with continue and break" -> """
        |int f(int n, int *a) {
        |  int s = 0;
        |  for (int i = 0; i < n; i++) {
        |    if (a[i] < 0) continue;
        |    for (int j = i; j < n; j++) {
        |      if (a[j] == 0) break;
        |      s = s + a[j];
        |    }
        |    a[i] = s;
        |  }
        |  return s;
        |}
        |""".stripMargin,
    "goto, switch fall-through and unreachable code" -> """
        |int f(int c, int d) {
        |  int x = 0;
        |again:
        |  switch (c) {
        |    case 0: x = 1;
        |    case 1: x = x + d; break;
        |    default: x = 3;
        |  }
        |  if (x < 10) { c = c - 1; goto again; }
        |  return x;
        |  x = 4;
        |  g(x);
        |}
        |""".stripMargin,
    "field accesses, pointers and a loop at the end" -> """
        |struct s { int a; int b; };
        |int f(struct s *p, int c) {
        |  p->a = c;
        |  p->b = p->a + 1;
        |  if (c) p->a = p->b;
        |  int *q = &p->a;
        |  *q = 5;
        |  x = c ? p->a : p->b;
        |  do { p->b = p->b - 1; } while (p->b > 0);
        |}
        |""".stripMargin
  )

  "the dense solver of ReachingDefPass" should {
    programs.toSeq.sortBy(_._1).foreach { case (name, program) =>
      s"reach the fixpoint of DataFlowSolver, in: $name" in {
        code(program).method.isExternal(false).l.foreach { method =>
          val problem  = ReachingDefProblem.create(method)
          val expected = new DataFlowSolver().calculateMopSolutionForwards(problem)
          val actual   = ReachingDefSolver.solve(problem)
          val views    = ReachingDefSolver.solveIn(problem)
          problem.flowGraph.allNodesReversePostOrder.foreach { node =>
            withClue(s"${method.name}, at ${node.code}: ") {
              actual.in(node) shouldBe expected.in(node)
              actual.out(node) shouldBe expected.out(node)
              views(node) shouldBe expected.in(node)
              views(node).toList shouldBe expected.in(node).toList
              views(node).size shouldBe expected.in(node).size
              expected.in(node).foreach(definition => views(node).contains(definition) shouldBe true)
            }
          }
        }
      }
    }
  }
}
