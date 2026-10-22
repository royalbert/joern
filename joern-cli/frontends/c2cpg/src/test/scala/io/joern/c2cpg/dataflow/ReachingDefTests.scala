package io.joern.c2cpg.dataflow

import io.joern.c2cpg.testfixtures.DataFlowCodeToCpgSuite
import io.joern.dataflowengineoss.language.*
import io.joern.dataflowengineoss.passes.reachingdef.{
  ReachingDefFlowGraph,
  ReachingDefProblem,
  ReachingDefTransferFunction
}
import io.shiftleft.codepropertygraph.generated.nodes.{Call, Identifier}
import io.shiftleft.semanticcpg.language.*

class ReachingDefTests extends DataFlowCodeToCpgSuite {

  "ReachingDefTest1" should {
    val cpg = code("""
       |int foo() {
       | int y = x + 1;
       | return y;
       |}
       |""".stripMargin)

    val fooMethod = cpg.method("foo").head
    val flowGraph = new ReachingDefFlowGraph(fooMethod)

    "create ReachingDefFlowGraph with correct entry/exit" in {
      flowGraph.entryNode shouldBe fooMethod
      flowGraph.exitNode shouldBe fooMethod.methodReturn
    }

    "create ReachingDefFlowGraph with correct successors" in {
      val List(id) = flowGraph.succ(fooMethod).collectAll[Identifier].l
      id.name shouldBe "y"

      flowGraph.succ(fooMethod.methodReturn) shouldBe List()

      val List(ret) = cpg.method("foo").ast.isReturn.l
      flowGraph.succ(ret) shouldBe List(fooMethod.methodReturn)
    }

    "create ReachingDefFlowGraph with correct predecessors" in {
      val List(ret) = cpg.method("foo").ast.isReturn.l
      val List(id)  = flowGraph.succ(fooMethod).collectAll[Identifier].l
      flowGraph.pred(id) shouldBe List(fooMethod)
      flowGraph.pred(fooMethod.methodReturn) shouldBe List(ret)
    }
  }

  "ReachingDefTest2" should {
    val cpg = code("""
      |int foo(int x, int y) {
      | y = x + 1;
      | return y;
      |}
      |""".stripMargin)

    val fooMethod = cpg.method("foo").head
    val flowGraph = new ReachingDefFlowGraph(fooMethod)

    "create ReachingDefFlowGraph with correct successors" in {
      val param1    = fooMethod.parameter.index(1).head
      val param2    = fooMethod.parameter.index(2).head
      val paramOut1 = param1.asOutput.head
      val paramOut2 = param2.asOutput.head

      flowGraph.succ(fooMethod) shouldBe List(param1)
      flowGraph.succ(param1) shouldBe List(param2)
      val List(id) = flowGraph.succ(param2).collectAll[Identifier].l
      id.name shouldBe "y"

      val List(ret) = cpg.method("foo").ast.isReturn.l
      flowGraph.succ(ret).iterator.to(Set) shouldBe Set(paramOut1)
      flowGraph.succ(paramOut1) shouldBe List(paramOut2)
      flowGraph.succ(paramOut2) shouldBe List(fooMethod.methodReturn)
    }

    "create ReachingDefFlowGraph with correct predecessors" in {
      val param1    = fooMethod.parameter.index(1).head
      val param2    = fooMethod.parameter.index(2).head
      val paramOut1 = param1.asOutput.head
      val paramOut2 = param2.asOutput.head
      val List(ret) = cpg.method("foo").ast.isReturn.l

      flowGraph.pred(param2) shouldBe List(param1)
      flowGraph.pred(param1) shouldBe List(fooMethod)
      flowGraph.pred(paramOut1) shouldBe List(ret)
      flowGraph.pred(paramOut2) shouldBe List(paramOut1)
      flowGraph.pred(fooMethod.methodReturn) shouldBe List(paramOut2)
    }

  }

  "ReachingDefTest3" should {
    val cpg = code("""
      |void foo(int x, int y) {
      | y = x + 1;
      |}
      |""".stripMargin)

    val fooMethod = cpg.method("foo").head
    val flowGraph = new ReachingDefFlowGraph(fooMethod)

    "create ReachingDefFlowGraph with correct successors" in {
      val param1    = fooMethod.parameter.index(1).head
      val param2    = fooMethod.parameter.index(2).head
      val paramOut1 = param1.asOutput.head
      val paramOut2 = param2.asOutput.head
      flowGraph.succ(param1) shouldBe List(param2)

      val List(id) = flowGraph.succ(param2).collectAll[Identifier].l
      id.name shouldBe "y"

      flowGraph.succ(cpg.call.codeExact("y = x + 1").head) shouldBe List(paramOut1)
      flowGraph.succ(paramOut1) shouldBe List(paramOut2)
      flowGraph.succ(paramOut2) shouldBe List(fooMethod.methodReturn)
    }

    "create ReachingDefFlowGraph with correct predecessors" in {
      val param1    = fooMethod.parameter.index(1).head
      val param2    = fooMethod.parameter.index(2).head
      val paramOut1 = param1.asOutput.head
      val paramOut2 = param2.asOutput.head
      val call      = cpg.call.codeExact("y = x + 1").head

      flowGraph.pred(param1) shouldBe List(fooMethod)
      flowGraph.pred(param2) shouldBe List(param1)
      flowGraph.pred(paramOut1) shouldBe List(call)
      flowGraph.pred(paramOut2) shouldBe List(paramOut1)
      flowGraph.pred(fooMethod.methodReturn) shouldBe List(paramOut2)
    }

  }

  "An initializer table" should {
    val cpg = code("""
      |struct cfg { int len; int max; };
      |void sink(int);
      |int foo() {
      | struct cfg t[2] = { { 1, 2 }, { 3, 4 } };
      | struct cfg c = { 5, 6 };
      | sink(c.max);
      |}
      |""".stripMargin)

    "count each list as one definition, and the entries it sets as none" in {
      val fooMethod = cpg.method("foo").head
      val gen     = ReachingDefProblem.create(fooMethod).transferFunction.asInstanceOf[ReachingDefTransferFunction].gen
      val lists   = fooMethod.ast.isCall.nameExact("<operator>.arrayInitializer").l
      val entries = lists.argument.isCall.nameExact("<operator>.assignment").l
      lists.map(gen(_).size) shouldBe List(1, 1, 1, 1)
      entries.map(gen(_).size) shouldBe List(0, 0, 0, 0, 0, 0)
    }

    "still carry an entry's value to a use of the object" in {
      val source = cpg.literal.code("6")
      val sink   = cpg.call("sink").argument
      sink.reachableByFlows(source).l should not be empty
    }
  }

  "A designated initializer table" should {
    val cpg = code("""
      |struct cfg { int len; int max; };
      |void sink(int);
      |int foo() {
      | struct cfg t[2] = { [0] = { .len = 1, .max = 2 }, [1] = { .len = 3 } };
      | struct cfg c = { .len = 5, .max = 6 };
      | sink(c.max);
      |}
      |""".stripMargin)

    "count no definition for a designated entry, as for a positional one" in {
      val fooMethod = cpg.method("foo").head
      val gen     = ReachingDefProblem.create(fooMethod).transferFunction.asInstanceOf[ReachingDefTransferFunction].gen
      val entries = fooMethod.ast.isCall
        .nameExact("<operator>.assignment")
        .filter(assignment =>
          assignment.astParent.isBlock && (assignment.astParent.astParent match {
            case list: Call => list.name == "<operator>.arrayInitializer"
            case _          => false
          })
        )
        .l
      entries.map(_.code).sorted shouldBe List(
        ".len = 1",
        ".len = 3",
        ".len = 5",
        ".max = 2",
        ".max = 6",
        "[0] = { .len = 1, .max = 2 }",
        "[1] = { .len = 3 }"
      )
      entries.map(gen(_).size) shouldBe List.fill(7)(0)
    }

    "still carry an entry's value to a use of the object" in {
      val source = cpg.literal.code("6")
      val sink   = cpg.call("sink").argument
      sink.reachableByFlows(source).l should not be empty
    }
  }

  "A positional table of a struct with several members" should {
    val entries = (0 until 800).map(i => s"{ $i, $i, $i, $i }").mkString(", ")
    val cpg     = code(s"""
      |struct reg { int addr; int value; int mask; int delay; };
      |int source(void);
      |void sink(int);
      |void init(void) {
      | int a = source();
      | struct reg seq[800] = { $entries };
      | sink(a);
      |}
      |""".stripMargin)

    "keep the flows of the function that holds it" in {
      cpg.call("sink").argument.reachableByFlows(cpg.call("source")).l should not be empty
    }
  }

  "An assignment written as an entry of a list" should {
    val cpg = code("""
      |int source(void);
      |void sink(int);
      |void init(void) {
      | int x;
      | int a[1] = { x = source() };
      | sink(x);
      |}
      |""".stripMargin)

    "still define its variable" in {
      cpg.call("sink").argument.reachableByFlows(cpg.call("source")).l should not be empty
    }
  }

  "A compound literal" should {
    val cpg = code("""
      |struct cfg { int len; int max; };
      |void sink(int);
      |int foo() {
      | struct cfg c = (struct cfg){ 7, 8 };
      | sink(c.max);
      |}
      |""".stripMargin)

    "still carry an entry's value to a use of the object the literal makes" in {
      cpg.call("sink").argument.reachableByFlows(cpg.literal.code("8")).l should not be empty
    }
  }

  "A pointer to a compound literal" should {
    val cpg = code("""
      |struct cfg { int len; int max; };
      |void sink(int);
      |int foo() {
      | struct cfg *p = &(struct cfg){ .len = 5, .max = 6 };
      | sink(p->max);
      |}
      |""".stripMargin)

    "still carry an entry's value to a use of the object it points to" in {
      cpg.call("sink").argument.reachableByFlows(cpg.literal.code("6")).l should not be empty
    }
  }
}
