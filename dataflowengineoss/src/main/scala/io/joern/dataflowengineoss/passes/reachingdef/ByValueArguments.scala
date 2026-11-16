package io.joern.dataflowengineoss.passes.reachingdef

import io.joern.x2cpg.Defines as X2CpgDefines
import io.shiftleft.codepropertygraph.generated.{DispatchTypes, EvaluationStrategies, Operators}
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.semanticcpg.language.*

/** The arguments of the calls in `method` that a call cannot write, because the callee receives them by value.
  *
  * A call cannot write a variable it receives through a parameter whose evaluation strategy is `BY_COPY`: the callee
  * gets a copy that shares nothing with the variable. So a call of a function does not define an identifier argument
  * when every method the call may invoke takes it through such a parameter. The variable must be one only this method
  * can write: a local or a parameter of the method, not a variable it shares with other code (a captured or global
  * variable, or one with a storage class such as `static`), and not one whose address the method takes. Operators keep
  * their own semantics, and a macro may assign its arguments, so only calls of functions qualify. A callee the graph
  * only has a stub for, an argument that a variadic parameter absorbs, and a call that invokes no known method keep
  * their definitions.
  *
  * c2cpg sets `BY_COPY`. Calls in other languages keep the handling they have now; each language decides whether it
  * needs different handling, with evaluation strategy value(s) of its own.
  */
private[reachingdef] class ByValueArguments(method: Method) {

  /** The locals and parameters of `method` whose address the method takes, as in `&x` or `&x.field`. */
  private lazy val addressTaken: Set[Declaration] =
    method.call
      .nameExact(Operators.addressOf)
      .argument
      .ast
      .isIdentifier
      .flatMap(_.refsTo)
      .toSet

  /** Whether `call` receives `argument` by value, so that the call does not define it. */
  def isPassedByValue(call: Call, argument: Expression): Boolean =
    isFunctionCall(call) && (argument match {
      case identifier: Identifier => isUnshared(identifier) && calleesTakeByValue(call, identifier.argumentIndex)
      case _                      => false
    })

  private def isFunctionCall(call: Call): Boolean =
    !call.name.startsWith("<operator") && call.dispatchType != DispatchTypes.INLINED

  private def isUnshared(identifier: Identifier): Boolean =
    identifier.refsTo.l match {
      case List(local: Local) =>
        local.closureBindingId.isEmpty && !hasStorageClass(local._tagViaTaggedByOut) && !addressTaken.contains(local)
      case List(param: MethodParameterIn) =>
        !hasStorageClass(param._tagViaTaggedByOut) && !addressTaken.contains(param)
      case _ => false
    }

  private def hasStorageClass(tags: Iterator[Tag]): Boolean =
    tags.exists(_.name == X2CpgDefines.StorageClassTag)

  private def calleesTakeByValue(call: Call, index: Int): Boolean = {
    val callees = NoResolve.getCalledMethods(call).l
    callees.nonEmpty && callees.forall { callee =>
      !callee.isExternal && callee.parameter.index(index).l.exists { parameter =>
        !parameter.isVariadic && parameter.evaluationStrategy == EvaluationStrategies.BY_COPY
      }
    }
  }

}
