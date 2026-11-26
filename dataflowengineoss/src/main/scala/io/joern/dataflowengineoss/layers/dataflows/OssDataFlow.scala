package io.joern.dataflowengineoss.layers.dataflows

import io.joern.dataflowengineoss.DefaultSemantics
import io.joern.dataflowengineoss.passes.reachingdef.{DefinitionRule, ReachingDefPass}
import io.joern.dataflowengineoss.semanticsloader.{FlowSemantic, FullNameSemantics, Semantics}
import io.shiftleft.semanticcpg.layers.{LayerCreator, LayerCreatorContext, LayerCreatorOptions}

object OssDataFlow {
  val overlayName: String = "dataflowOss"
  val description: String = "Layer to support the OSS lightweight data flow tracker"

  def defaultOpts = new OssDataFlowOptions()
}

/** @param definitionRules
  *   the rules that decide what a call does to its arguments (see [[DefinitionRule]]); none by default
  */
class OssDataFlowOptions(
  var maxNumberOfDefinitions: Int = 4000,
  var semantics: Semantics = DefaultSemantics(),
  var definitionRules: Seq[DefinitionRule] = Nil
) extends LayerCreatorOptions {}

class OssDataFlow(opts: OssDataFlowOptions)(implicit val semantics: Semantics = opts.semantics) extends LayerCreator {

  override val overlayName: String = OssDataFlow.overlayName
  override val description: String = OssDataFlow.description

  override def create(context: LayerCreatorContext): Unit = {
    ReachingDefPass(context.cpg, opts.maxNumberOfDefinitions, opts.definitionRules).createAndApply()
  }
}
