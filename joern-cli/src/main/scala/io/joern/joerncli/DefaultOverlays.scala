package io.joern.joerncli

import io.joern.dataflowengineoss.layers.dataflows.{OssDataFlow, OssDataFlowOptions}
import io.joern.dataflowengineoss.DefaultSemantics
import io.joern.dataflowengineoss.passes.reachingdef.DefinitionRule
import io.joern.dataflowengineoss.semanticsloader.FlowSemantic
import io.joern.x2cpg.X2Cpg.applyDefaultOverlays
import io.shiftleft.codepropertygraph.generated.Cpg
import io.shiftleft.semanticcpg.layers.*

object DefaultOverlays {

  val DEFAULT_CPG_IN_FILE           = "cpg.bin"
  val defaultMaxNumberOfDefinitions = 4000

  /** Load the CPG at `storeFilename` and add enhancements, turning the CPG into an SCPG.
    *
    * @param storeFilename
    *   the filename of the cpg
    * @param definitionRules
    *   rules for the data-flow overlay that decide what a call does to its arguments (see `OssDataFlowOptions`)
    * @param semantics
    *   semantics for the data-flow overlay, besides the default ones
    * @param beforeOverlays
    *   run on the loaded graph before any overlay
    */
  def create(
    storeFilename: String,
    maxNumberOfDefinitions: Int = defaultMaxNumberOfDefinitions,
    definitionRules: Seq[DefinitionRule] = Seq.empty,
    semantics: List[FlowSemantic] = Nil,
    beforeOverlays: Cpg => Unit = _ => ()
  ): Cpg = {
    val cpg = CpgBasedTool.loadFromFile(storeFilename)
    beforeOverlays(cpg)
    applyDefaultOverlays(cpg)
    val context = new LayerCreatorContext(cpg)
    val options = new OssDataFlowOptions(maxNumberOfDefinitions, definitionRules = definitionRules)
    if (semantics.nonEmpty) options.semantics = DefaultSemantics().plus(semantics)
    new OssDataFlow(options).run(context)
    cpg
  }

}
