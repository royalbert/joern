package io.joern.dataflowengineoss.passes.reachingdef

import io.joern.x2cpg.Defines as X2CpgDefines
import io.shiftleft.codepropertygraph.generated.DispatchTypes
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.semanticcpg.language.*

/** The arguments of a call that the call cannot write, because their variables are passed by value.
  *
  * A frontend tags the LOCAL or METHOD_PARAMETER_IN of a variable `STORAGE_CLASS` with the value `by_value` when no
  * call it is passed to can write it. A call of a function therefore does not define such a variable when it is passed
  * as an argument. Operators keep their own semantics, and a macro may assign its arguments, so only calls of functions
  * qualify.
  */
private[reachingdef] object ByValueArguments {

  /** The value of [[X2CpgDefines.StorageClassTag]] that marks a variable as passed by value. */
  private val ByValue = "by_value"

  /** Whether `call` receives `argument` by value, so that the call does not define it. */
  def isPassedByValue(call: Call, argument: Expression): Boolean =
    isFunctionCall(call) && (argument match {
      case identifier: Identifier => identifier.refsTo.exists(isTaggedByValue)
      case _                      => false
    })

  private def isFunctionCall(call: Call): Boolean =
    !call.name.startsWith("<operator") && call.dispatchType != DispatchTypes.INLINED

  private def isTaggedByValue(declaration: Declaration): Boolean =
    declaration match {
      case local: Local             => hasByValueTag(local._tagViaTaggedByOut)
      case param: MethodParameterIn => hasByValueTag(param._tagViaTaggedByOut)
      case _                        => false
    }

  private def hasByValueTag(tags: Iterator[Tag]): Boolean =
    tags.exists(tag => tag.name == X2CpgDefines.StorageClassTag && tag.value == ByValue)

}
