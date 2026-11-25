package io.joern.dataflowengineoss.passes.reachingdef

import io.joern.dataflowengineoss.semanticsloader.Semantics
import io.shiftleft.codepropertygraph.generated.{Cpg, EdgeTypes}
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.passes.ForkJoinParallelCpgPass
import io.shiftleft.semanticcpg.language.*
import org.slf4j.{Logger, LoggerFactory}

import scala.collection.mutable

/** A pass that calculates reaching definitions ("data dependencies"), in which those of `definitionRules` that apply to
  * the graph decide what a call does to its arguments (see [[DefinitionRule]]); none by default. The tags the rules
  * give an argument are put on it, for every method the pass handles, including one it skips as too large.
  */
class ReachingDefPass(cpg: Cpg, maxNumberOfDefinitions: Int = 4000, definitionRules: Seq[DefinitionRule] = Nil)(implicit
  semantics: Semantics
) extends ForkJoinParallelCpgPass[Method](cpg) {

  private val logger: Logger = LoggerFactory.getLogger(this.getClass)
  // If there are any regex method full names, load them early
  semantics.initialize(cpg)

  /** Whether any method is a module: [[io.joern.dataflowengineoss.globalFromLiteral]] finds literals in modules only.
    */
  private lazy val graphHasModules: Boolean = cpg.method.isModule.nonEmpty

  override def generateParts(): Array[Method] = {
    graphHasModules
    cpg.method.toArray
  }

  override def runOnPart(dstGraph: DiffGraphBuilder, method: Method): Unit = {
    logger.info("Calculating reaching definitions for: {} in {}", method.fullName, method.filename)
    val problem  = createProblem(method)
    val bailsOut = shouldBailOut(method, problem)
    storeArgumentTags(dstGraph, problem)
    if (bailsOut) {
      logger.warn("Skipping.")
      return
    }

    val solution     = new DataFlowSolver().calculateMopSolutionForwards(problem)
    val ddgGenerator = new DdgGenerator(semantics, graphHasModules)
    ddgGenerator.addReachingDefEdges(dstGraph, method, problem, solution)
  }

  /** The reaching-definition problem of `method`. Creating it builds the flow graph, which with the count of
    * definitions is all that [[shouldBailOut]] reads; the `gen` and kill sets are built when the solver first needs
    * them.
    */
  private[reachingdef] def createProblem(method: Method): DataFlowProblem[CfgNode, mutable.BitSet] =
    ReachingDefProblem.create(method, applicableRules)

  /** The rules of `definitionRules` that apply to the graph, in their order, each asked once. */
  private[reachingdef] lazy val applicableRules: Seq[DefinitionRule] = definitionRules.filter(_.appliesTo(cpg))

  /** Puts the tags the rules give the arguments of the problem's method on those arguments, as TAG nodes. */
  private def storeArgumentTags(dstGraph: DiffGraphBuilder, problem: DataFlowProblem[CfgNode, mutable.BitSet]): Unit =
    problem.transferFunction match {
      case transfer: ReachingDefTransferFunction =>
        transfer.argumentTags.foreach { case (argument, tags) =>
          tags.foreach { case (name, value) =>
            val tag = NewTag().name(name).value(value)
            dstGraph.addNode(tag)
            dstGraph.addEdge(argument, tag, EdgeTypes.TAGGED_BY)
          }
        }
      case _ =>
    }

  /** Before we start propagating definitions in the graph, which is the bulk of the work, we check how many definitions
    * were are dealing with in total. If a threshold is reached, we bail out instead, leaving reaching definitions
    * uncalculated for the method in question. Users can increase the threshold if desired.
    */
  private def shouldBailOut(method: Method, problem: DataFlowProblem[CfgNode, mutable.BitSet]): Boolean = {
    val transferFunction = problem.transferFunction.asInstanceOf[ReachingDefTransferFunction]
    // The number of definitions in the `gen` sets, counted without building them
    val numberOfDefinitions = transferFunction.numberOfDefinitions
    logger.info("Number of definitions for {}: {}", method.fullName, numberOfDefinitions)
    if (numberOfDefinitions > maxNumberOfDefinitions) {
      logger.warn("{} has more than {} definitions", method.fullName, maxNumberOfDefinitions)
      true
    } else {
      false
    }
  }

}
