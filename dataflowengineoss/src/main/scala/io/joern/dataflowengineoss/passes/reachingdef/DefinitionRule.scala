package io.joern.dataflowengineoss.passes.reachingdef

import io.shiftleft.codepropertygraph.generated.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.{Call, Expression, Method}

/** The changes a rule makes to what a call does to one of its arguments in the reaching-definition problem.
  *
  * @param defines
  *   whether the call gives the argument a new definition
  * @param cutsOff
  *   whether the definitions of the argument's variable that reach the call stop there
  * @param tags
  *   (name, value) tags that [[ReachingDefPass]] puts on the argument
  */
final case class ArgumentEffect(
  defines: Boolean = false,
  cutsOff: Boolean = false,
  tags: Seq[(String, String)] = Seq.empty
) {

  /** This and `other` together: a definition or cut-off that either makes, and the tags of both. */
  def and(other: ArgumentEffect): ArgumentEffect =
    ArgumentEffect(defines || other.defines, cutsOff || other.cutsOff, tags ++ other.tags)
}

object ArgumentEffect {

  /** No changes. */
  val NoChange: ArgumentEffect = ArgumentEffect()

  /** Joern's default for an argument that can be a definition: a new definition that cuts off the earlier ones. */
  val Overwrites: ArgumentEffect = ArgumentEffect(defines = true, cutsOff = true)
}

/** A rule's answer for one argument of a call: the changes it makes ([[ArgumentEffect.NoChange]] for none), and whether
  * the argument is then passed on, to the next rule and after the last to Joern's default.
  */
final case class ArgumentDecision(effect: ArgumentEffect, passOn: Boolean)

object ArgumentDecision {

  /** No changes, and passed on: as if the rule were not there. */
  val PassOn: ArgumentDecision = ArgumentDecision(ArgumentEffect.NoChange, passOn = true)
}

/** A rule that takes part in deciding, for each call and each of its arguments that can be a definition, what the call
  * does to the argument in the reaching-definition problem, and so which definitions reach past the call.
  *
  * Joern's default is that a call overwrites each of its identifier and call arguments ([[ArgumentEffect.Overwrites]]),
  * except the operands of a ternary, which it leaves alone. For each argument, the rules are asked in their order: each
  * answers with the changes it makes and whether it passes the argument on ([[ArgumentDecision]]). What the call does
  * to the argument is the changes of every rule asked, together, and Joern's default too if the last rule asked passed
  * the argument on; a rule that does not pass it on is the last one asked.
  *
  * [[ReachingDefPass]] asks each rule once per pass whether it applies ([[appliesTo]]), and each rule that applies once
  * per method for that method's rule ([[forMethod]]). It runs one method per task, in parallel, so [[appliesTo]] and
  * [[forMethod]] may be called from any thread. The rule [[forMethod]] returns is used by one thread only, so it may
  * keep state for its method.
  */
trait DefinitionRule {

  /** Whether the rule applies to `cpg`. Asked once per pass, before any method is solved. */
  def appliesTo(cpg: Cpg): Boolean

  /** The rule for the calls of `method`: given a call and one of its arguments, the rule's answer for the argument. */
  def forMethod(method: Method): Call => Expression => ArgumentDecision
}
