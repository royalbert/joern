package io.joern.dataflowengineoss.plugin

import io.joern.dataflowengineoss.passes.reachingdef.DefinitionRule
import io.joern.dataflowengineoss.semanticsloader.FlowSemantic

/** A plug-in for the data-flow calculation, under a name, so that a tool such as `joern-parse --data-flow-plugin
  * <name>` can run one it does not know at compile time. It can give a [[DefinitionRule]], semantics, or both.
  *
  * Implementations are found through `java.util.ServiceLoader`: a jar on the class path lists them in
  * `META-INF/services/io.joern.dataflowengineoss.plugin.DataFlowPlugin`. A plug-in needs a public constructor without
  * parameters. Being on the class path changes nothing: a plug-in runs only when it is named.
  */
trait DataFlowPlugin {

  /** The name the plug-in is selected by. */
  def name: String

  /** The rule for the reaching-definition problem, if the plug-in has one. */
  def definitionRule: Option[DefinitionRule] = None

  /** Semantics added to the default ones for the data-flow calculation; for a method that has default semantics too,
    * the two are merged.
    */
  def semantics: List[FlowSemantic] = Nil
}
