package io.joern.c2cpg.astcreation

import io.joern.x2cpg.Ast
import io.shiftleft.codepropertygraph.generated.{DispatchTypes, EvaluationStrategies, Operators}
import org.eclipse.cdt.core.dom.ast.*
import org.eclipse.cdt.core.dom.ast.c.{ICASTArrayDesignator, ICASTDesignatedInitializer, ICASTFieldDesignator}
import org.eclipse.cdt.core.dom.ast.cpp.{
  ICPPASTArrayDesignator,
  ICPPASTConstructorInitializer,
  ICPPASTDesignatedInitializer,
  ICPPASTFieldDesignator,
  ICPPBinding,
  ICPPClassType
}
import org.eclipse.cdt.internal.core.dom.parser.{ASTInternal, ASTQueries}
import org.eclipse.cdt.internal.core.dom.parser.c.CASTArrayRangeDesignator
import org.eclipse.cdt.internal.core.dom.parser.cpp.CPPASTArrayRangeDesignator

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.Try

trait AstForInitializersCreator { this: AstCreator =>

  protected def astForInitializerList(list: IASTInitializerList): Ast = {
    val MAX_INITIALIZERS = 1000
    val op               = Operators.arrayInitializer
    val initCallNode     =
      callNode(list, code(list), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(Defines.Any))
    val clauses = list.getClauses.slice(0, MAX_INITIALIZERS)
    val obj     = objectOf(list)
    val entries = obj.map(filled => slots(list, filled.tpe)).getOrElse(Nil)
    val args    = clauses.toList.zipWithIndex.map { case (entry, i) =>
      (obj, entries.lift(i).flatten) match {
        case (Some(filled), Some(MemberSlot(field))) if field.getName.nonEmpty =>
          positionalEntryAst(filled, entry, field)
        case _ => astForNode(entry)
      }
    }
    val ast = callAst(initCallNode, args)
    if (list.getClauses.length > MAX_INITIALIZERS) {
      val placeholder =
        literalNode(list, "<too-many-initializers>", Defines.Any).argumentIndex(MAX_INITIALIZERS)
      ast.withChild(Ast(placeholder)).withArgEdge(initCallNode, placeholder)
    } else {
      ast
    }
  }

  protected def astForCPPASTConstructorInitializer(c: ICPPASTConstructorInitializer): Ast = {
    val name      = Defines.OperatorConstructorInitializer
    val callNode_ =
      callNode(c, code(c), name, name, DispatchTypes.STATIC_DISPATCH, None, Some(Defines.Any))
    val args = c.getArguments.toList.map(a => astForNode(a))
    callAst(callNode_, args)
  }

  protected def astForCASTDesignatedInitializer(initializer: ICASTDesignatedInitializer): Ast =
    designatedInitializerAst(initializer, initializer.getDesignators.toSeq, initializer.getOperand)

  /** A designated entry `.ops[1].read = r` is one assignment to the slot its designators lead to, `dev.ops[1].read`.
    * Where they lead to no known member, each designator is an assignment of its own, as before.
    */
  private def designatedInitializerAst(initializer: IASTNode, ds: Seq[IASTNode], operand: IASTNode): Ast = {
    val node = blockNode(initializer)
    scope.pushNewBlockScope(node)
    def assignment(left: Ast, offset: Int): Ast = {
      val op        = Operators.assignment
      val callNode_ =
        callNode(
          initializer,
          code(initializer),
          op,
          op,
          DispatchTypes.STATIC_DISPATCH,
          None,
          Some(registerType(Defines.Void))
        )
          .argumentIndex(offset)
      callAst(callNode_, List(left, astForNode(operand)))
    }
    val calls = designatedTarget(initializer, ds) match {
      case Some(target) => List(assignment(target, 1))
      case None         => withIndex(ds)((designator, offset) => assignment(astForNode(designator), offset)).toList
    }
    scope.popScope()
    blockAst(node, calls)
  }

  /** Where an entry of an initializer list goes in the object the list fills: a member of a struct or union, an
    * anonymous struct or union member, or an element of an array.
    */
  private sealed trait Slot { def tpe: IType }
  private case class MemberSlot(field: IField) extends Slot { def tpe: IType = field.getType }
  private case class ElementSlot(
    index: String,
    element: IType,
    position: Option[Int],
    indexExpr: Option[IASTExpression]
  ) extends Slot { def tpe: IType = element }

  /** An anonymous struct or union member (`union { int i; float f; };`), whose members are members of the object it is
    * in (C17 6.7.2.1p13).
    */
  private case class AnonymousSlot(tpe: ICompositeType) extends Slot

  /** An object an initializer list fills, as C writes it (`uart`, `many[1]`, `ou.o`), with its type and an expression
    * that names it at a given node.
    */
  private case class InitializedObject(code: String, tpe: IType, ast: IASTNode => Ast)

  private def bare(tpe: IType): IType = tpe match {
    case typedef: ITypedef         => bare(typedef.getType)
    case qualified: IQualifierType => bare(qualified.getType)
    case other                     => other
  }

  /** The name of `tpe` as the type that declares the members of an object of that type: a struct, union or class
    * without a tag is declared under the name of the typedef that names it (`typedef struct { ... } ops_t;`), which its
    * own name, being empty, cannot give.
    */
  private def declaringTypeName(tpe: IType): String = untaggedTypedef(tpe) match {
    case Some(cppTypedef: ICPPBinding) => safeCdtCall(cppTypedef.getQualifiedName.mkString(".")).getOrElse(Defines.Any)
    case Some(typedef)                 => typedef.getName
    case None                          => safeGetType(tpe)
  }

  /** The typedef that names the struct, union or class without a tag that `tpe` is, if there is one. */
  private def untaggedTypedef(tpe: IType): Option[ITypedef] = tpe match {
    case qualified: IQualifierType => untaggedTypedef(qualified.getType)
    case typedef: ITypedef         =>
      bare(typedef) match {
        case composite: ICompositeType if composite.getName.isEmpty =>
          untaggedTypedef(typedef.getType).orElse(Some(typedef))
        case _ => None
      }
    case _ => None
  }

  /** The object the initializer list `list` fills: the variable it initializes, or the element or member of the object
    * an enclosing list fills that `list` sets. None where there is no named object, as for a compound literal.
    */
  private def objectOf(list: IASTInitializerList): Option[InitializedObject] =
    initializedObjects.get(list) match {
      case Some(known) => known
      case None        => val found = objectOfUncached(list); initializedObjects.put(list, found); found
    }

  private val initializedObjects = mutable.HashMap.empty[IASTInitializerList, Option[InitializedObject]]
  private val entrySlots         = mutable.HashMap.empty[IASTInitializerList, List[Option[Slot]]]

  private def objectOfUncached(list: IASTInitializerList): Option[InitializedObject] = list.getParent match {
    case eq: IASTEqualsInitializer =>
      eq.getParent match {
        case declarator: IASTDeclarator => variableObject(ASTQueries.findInnermostDeclarator(declarator).getName)
        case _                          => None
      }
    case outer: IASTInitializerList =>
      for {
        filled <- objectOf(outer)
        slot   <- slots(outer, filled.tpe).lift(outer.getClauses.indexWhere(_ eq list)).flatten
        obj    <- objectAt(filled, slot)
      } yield obj
    case parent => designators(parent).flatMap(designatedObject(parent, _))
  }

  private def variableObject(name: IASTName): Option[InitializedObject] =
    safeGetBinding(name).collect { case binding: IVariable =>
      // The variable's own name: the code of a name a macro builds, as in `DECLARE_OPS(uart, r)`, is the macro's call.
      val variable = shortName(name)
      InitializedObject(
        variable,
        binding.getType,
        at => {
          val tpe = registerType(declaringTypeName(binding.getType))
          val id  = identifierNode(at, variable, variable, tpe)
          scope.addVariableReference(variable, id, tpe, EvaluationStrategies.BY_REFERENCE)
          Ast(id)
        }
      )
    }

  /** The member or element of `filled` that `slot` names, or `filled` itself for an anonymous member, whose members are
    * its own; None for an unnamed member.
    */
  private def objectAt(filled: InitializedObject, slot: Slot): Option[InitializedObject] = slot match {
    case AnonymousSlot(anonymous)                    => Some(filled.copy(tpe = anonymous))
    case MemberSlot(field) if field.getName.nonEmpty =>
      val code_ = s"${filled.code}.${field.getName}"
      Some(InitializedObject(code_, field.getType, at => fieldAccessAst(filled, field, field.getName, code_, at)))
    case ElementSlot(index, element, _, indexExpr) =>
      val code_ = s"${filled.code}[$index]"
      Some(
        InitializedObject(
          code_,
          element,
          at => {
            val op     = Operators.indexAccess
            val access =
              callNode(
                at,
                code_,
                op,
                op,
                DispatchTypes.STATIC_DISPATCH,
                None,
                Some(registerType(declaringTypeName(element)))
              )
            val indexAst = indexExpr.map(astForNode).getOrElse(Ast(literalNode(at, index, registerType("int"))))
            callAst(access, List(filled.ast(at), indexAst))
          }
        )
      )
    case _ => None
  }

  /** The object a designated entry's designators lead to from the object its list fills (`.o`, `[1]`, `.o.p`). */
  private def designatedObject(entry: IASTNode, ds: Seq[IASTNode]): Option[InitializedObject] =
    Option(entry.getParent)
      .collect { case list: IASTInitializerList => list }
      .flatMap(objectOf)
      .flatMap(filled =>
        ds.foldLeft(Option(filled))((obj, designator) =>
          obj.flatMap(current => designatedSlot(current.tpe, designator).flatMap(objectAt(current, _)))
        )
      )

  /** The slot of a designator in an object of type `tpe`: the member a field designator names, the element a constant
    * array designator names.
    */
  private def designatedSlot(tpe: IType, designator: IASTNode): Option[Slot] = (bare(tpe), designator) match {
    case (composite: ICompositeType, _) =>
      fieldDesignatorName(designator)
        .flatMap(name =>
          fieldsOf(composite)
            .find(_.getName == name.toString)
            .orElse(safeGetBinding(name).collect { case field: IField => field })
        )
        .map(MemberSlot(_))
    case (array: IArrayType, _) => arrayDesignatorSlot(designator, array.getType)
    case _                      => None
  }

  /** The slot of each entry of `list`, which fills an object of type `tpe`; None for a designated entry and where the
    * slot is unknown. A positional entry takes the slot at its position (C17 6.7.9p17): the position follows the
    * entries before it, a designated one moving it to just after the slot it names. Unnamed bit-fields take no part
    * (p9). An entry without braces for a slot that is itself a struct, union or array starts that slot's own entries
    * (p20), so from there the position is unknown until a designator names a slot; for an anonymous struct member,
    * whose members are the object's own, the entries go on with its members. Positional entries of a union, which set
    * its first member only, are left out.
    */
  private def slots(list: IASTInitializerList, tpe: IType): List[Option[Slot]] =
    entrySlots.get(list) match {
      case Some(known) => known
      case None        => val found = slotsUncached(list, tpe); entrySlots.put(list, found); found
    }

  private def slotsUncached(list: IASTInitializerList, tpe: IType): List[Option[Slot]] =
    list.getClauses.toList
      .foldLeft((frameOf(tpe).toList, List.empty[Option[Slot]])) { case ((cursor, acc), entry) =>
        val (slot, next) = designators(entry) match {
          // The position after a designator whose slot is unknown is unknown too.
          case Some(ds) => (None, ds.headOption.map(cursorAfter(tpe, _)).getOrElse(Nil))
          case None     => place(cursor, entry)
        }
        (next, slot :: acc)
      }
      ._2
      .reverse

  /** A position in the elements of an object an initializer list fills: the element at `index` is the next one. A union
    * takes one element.
    */
  private case class Frame(elementAt: Int => Option[Slot], size: Option[Int], index: Int, union: Boolean) {
    def full: Boolean = size.exists(index >= _) || (union && index > 0)
    def next: Frame   = copy(index = index + 1)
  }

  /** The first position in an object of type `tpe`; None where its elements are unknown, and for a C++ `class`, whose
    * positional entries are left as they are.
    */
  private def frameOf(tpe: IType): Option[Frame] = bare(tpe) match {
    case composite: ICompositeType if composite.getKey != ICPPClassType.k_class =>
      elementsOf(composite).map(elements =>
        Frame(elements.lift, Some(elements.size), 0, composite.getKey == ICompositeType.k_union)
      )
    case array: IArrayType =>
      Some(Frame(i => Some(ElementSlot(i.toString, array.getType, Some(i), None)), None, 0, union = false))
    case _ => None
  }

  /** The slot of the positional entry `entry` at `cursor`, the position in the innermost object first, and the position
    * after it; Nil where the position is unknown. An object whose elements are all set gives way to the next element of
    * the object it is in: an anonymous member to the member after it.
    */
  @tailrec
  private def place(cursor: List[Frame], entry: IASTInitializerClause): (Option[Slot], List[Frame]) = cursor match {
    case Nil                          => (None, Nil)
    case frame :: outer if frame.full => place(outer.headOption.map(_.next :: outer.tail).getOrElse(Nil), entry)
    case frame :: outer               =>
      frame.elementAt(frame.index) match {
        case Some(AnonymousSlot(anonymous)) if !frame.union && !entry.isInstanceOf[IASTInitializerList] =>
          frameOf(anonymous) match {
            case Some(inner) => place(inner :: cursor, entry)
            case None        => (None, Nil)
          }
        case Some(slot) if startsElidedBraces(entry, slot.tpe) => (None, Nil)
        case Some(_) if frame.union                            => (None, frame.next :: outer)
        case Some(slot)                                        => (Some(slot), frame.next :: outer)
        case None                                              => (None, Nil)
      }
  }

  /** The position just after the slot `designator` names in an object of type `tpe`, the position in the innermost
    * object first; Nil where it is unknown. A range designator (`[0 ... 3]`) ends at its last element; a member of an
    * anonymous member is followed by the members after it in that anonymous member.
    */
  private def cursorAfter(tpe: IType, designator: IASTNode): List[Frame] =
    (frameOf(tpe), designatedSlot(tpe, designator)) match {
      case (Some(frame), Some(ElementSlot(_, _, Some(position), _))) => List(frame.copy(index = position + 1))
      case (Some(frame), Some(MemberSlot(field)))                    => cursorAfterMember(frame, field.getName)
      case _                                                         => Nil
    }

  private def cursorAfterMember(frame: Frame, name: String): List[Frame] =
    (0 until frame.size.getOrElse(0)).iterator
      .map(i =>
        frame.elementAt(i) match {
          case Some(MemberSlot(field)) if field.getName == name => List(frame.copy(index = i + 1))
          case Some(AnonymousSlot(anonymous))                   =>
            frameOf(anonymous)
              .map(cursorAfterMember(_, name))
              .filter(_.nonEmpty)
              .map(_ :+ frame.copy(index = i))
              .getOrElse(Nil)
          case _ => Nil
        }
      )
      .find(_.nonEmpty)
      .getOrElse(Nil)

  /** The elements of a struct or union that an initializer list sets in order: its named members and its anonymous
    * struct and union members, one element each; unnamed bit-fields take no part (C17 6.7.9p9). None where its
    * definition is not visible.
    */
  private def elementsOf(composite: ICompositeType): Option[Vector[Slot]] =
    compositeElements.getOrElseUpdate(composite, elementsOfUncached(composite))

  private val compositeElements = mutable.HashMap.empty[ICompositeType, Option[Vector[Slot]]]

  private def elementsOfUncached(composite: ICompositeType): Option[Vector[Slot]] =
    safeCdtCall(ASTInternal.getPhysicalNodeOfScope(composite.getCompositeScope)).collect {
      case definition: IASTCompositeTypeSpecifier =>
        definition.getMembers.toVector.flatMap {
          case member: IASTSimpleDeclaration if member.getDeclarators.isEmpty =>
            member.getDeclSpecifier match {
              case anonymous: IASTCompositeTypeSpecifier if anonymous.getName.toString.isEmpty =>
                safeGetBinding(anonymous.getName).collect { case tpe: ICompositeType => AnonymousSlot(tpe) }
              case _ => None
            }
          case member: IASTSimpleDeclaration =>
            member.getDeclarators.toVector.flatMap { declarator =>
              safeGetBinding(ASTQueries.findInnermostDeclarator(declarator).getName).collect {
                case field: IField if field.getName.nonEmpty && !field.isStatic => MemberSlot(field)
              }
            }
          case _ => Vector.empty
        }
    }

  /** The members of `composite`; none where its definition is not visible, for which CDT gives one problem field named
    * after the struct.
    */
  private def fieldsOf(composite: ICompositeType): Vector[IField] = {
    val fields = composite.getFields.toVector
    if (fields.exists(_.isInstanceOf[IProblemBinding])) Vector.empty else fields
  }

  /** Whether `entry`, set without braces to a slot of type `tpe`, starts the entries of that slot's own members (brace
    * elision, C17 6.7.9p20) rather than setting it whole: true for a struct, union or array, unless the entry is a
    * string for an array or a value of the slot's own type.
    */
  private def startsElidedBraces(entry: IASTInitializerClause, tpe: IType): Boolean = bare(tpe) match {
    case aggregate @ (_: ICompositeType | _: IArrayType) =>
      entry match {
        case _: IASTInitializerList                                                                       => false
        case literal: IASTLiteralExpression if literal.getKind == IASTLiteralExpression.lk_string_literal =>
          !aggregate.isInstanceOf[IArrayType]
        case expr: IASTExpression =>
          !safeCdtCall(expr.getExpressionType).exists(exprType => bare(exprType).isSameType(aggregate))
        case _ => false
      }
    case _ => false
  }

  /** The designators of a designated initializer entry, None for any other node. */
  private def designators(node: IASTNode): Option[Seq[IASTNode]] = node match {
    case initializer: ICASTDesignatedInitializer   => Some(initializer.getDesignators.toSeq)
    case initializer: ICPPASTDesignatedInitializer => Some(initializer.getDesignators.toSeq)
    case _                                         => None
  }

  /** The member a field designator (`.read`) names, None for any other designator. */
  private def fieldDesignatorName(designator: IASTNode): Option[IASTName] = designator match {
    case field: ICASTFieldDesignator   => Some(field.getName)
    case field: ICPPASTFieldDesignator => Some(field.getName)
    case _                             => None
  }

  /** The element an array designator names (`[2]`, `[ALT0]`, `[0 ... 3]`), with the designator's index written as in
    * the source and, for a single index, its expression; the position after it is known when its bounds are integer
    * constants.
    */
  private def arrayDesignatorSlot(designator: IASTNode, element: IType): Option[Slot] = {
    def single(index: IASTExpression) =
      Option(index).map(expr => ElementSlot(code(expr), element, constant(expr), Some(expr)))
    def range(floor: IASTExpression, ceiling: IASTExpression) =
      Option.when(floor != null && ceiling != null)(
        ElementSlot(s"${code(floor)} ... ${code(ceiling)}", element, constant(ceiling), None)
      )
    designator match {
      case array: ICASTArrayDesignator               => single(array.getSubscriptExpression)
      case array: ICPPASTArrayDesignator             => single(array.getSubscriptExpression)
      case rangeDesignator: CASTArrayRangeDesignator =>
        range(rangeDesignator.getRangeFloor, rangeDesignator.getRangeCeiling)
      case rangeDesignator: CPPASTArrayRangeDesignator =>
        range(rangeDesignator.getRangeFloor, rangeDesignator.getRangeCeiling)
      case _ => None
    }
  }

  /** The value of an integer constant expression that is a literal, also one a macro expands to. */
  private def constant(expr: IASTExpression): Option[Int] = expr match {
    case lit: IASTLiteralExpression if lit.getKind == IASTLiteralExpression.lk_integer_constant =>
      Try(java.lang.Long.decode(String.valueOf(lit.getValue).replaceAll("[uUlL]+$", "")).toInt).toOption
    case _ => None
  }

  /** The field access `filled.member` for the member `field` of `filled`, typed with the field's type. */
  private def fieldAccessAst(
    filled: InitializedObject,
    field: IField,
    member: String,
    accessCode: String,
    at: IASTNode
  ): Ast = {
    val op     = Operators.fieldAccess
    val access =
      callNode(
        at,
        accessCode,
        op,
        op,
        DispatchTypes.STATIC_DISPATCH,
        None,
        Some(registerType(declaringTypeName(field.getType)))
      )
    callAst(access, List(filled.ast(at), Ast(fieldIdentifierNode(at, member, member))))
  }

  /** A positional entry `r` of `uart = { r }` that sets the member `read`: the assignment `uart.read = r`, written
    * `.read = r`, as for `{ .read = r }`.
    */
  private def positionalEntryAst(filled: InitializedObject, entry: IASTNode, field: IField): Ast = {
    val member = field.getName
    val target = fieldAccessAst(filled, field, member, s".$member", entry)
    val assign = callNode(
      entry,
      s".$member = ${code(entry)}",
      Operators.assignment,
      Operators.assignment,
      DispatchTypes.STATIC_DISPATCH,
      None,
      Some(registerType(Defines.Void))
    )
    callAst(assign, List(target, astForNode(entry)))
  }

  /** The target of a designated entry: the slot its designators lead to from the object its list fills. A last field
    * designator (`.read` in `uart = { .read = r }`) is a field access on the object the others lead to, `uart.read`,
    * written `.read`, so that the member linker connects the entry to the member it sets, as it does for `x->read = r`.
    * An array designator (`[1]`) leads to the element, `uart[1]`. None where the designators lead to no known member,
    * and for a range of elements (`[0 ... 3]`).
    */
  private def designatedTarget(entry: IASTNode, ds: Seq[IASTNode]): Option[Ast] =
    for {
      last   <- ds.lastOption
      filled <- designatedObject(entry, ds.init)
      slot   <- designatedSlot(filled.tpe, last)
      target <- slot match {
        case MemberSlot(field) =>
          fieldDesignatorName(last).map(name => fieldAccessAst(filled, field, code(name), code(last), last))
        case element: ElementSlot if !isRangeDesignator(last) => objectAt(filled, element).map(_.ast(last))
        case _: ElementSlot | _: AnonymousSlot                => None
      }
    } yield target

  private def isRangeDesignator(designator: IASTNode): Boolean =
    designator.isInstanceOf[CASTArrayRangeDesignator] || designator.isInstanceOf[CPPASTArrayRangeDesignator]

  protected def astForCPPASTDesignatedInitializer(initializer: ICPPASTDesignatedInitializer): Ast =
    designatedInitializerAst(initializer, initializer.getDesignators.toSeq, initializer.getOperand)

  protected def astForCASTArrayRangeDesignator(des: CASTArrayRangeDesignator): Ast = {
    val op        = Operators.arrayInitializer
    val callNode_ =
      callNode(des, code(des), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(Defines.Any))
    val floorAst   = nullSafeAst(des.getRangeFloor)
    val ceilingAst = nullSafeAst(des.getRangeCeiling)
    callAst(callNode_, List(floorAst, ceilingAst))
  }

  protected def astForCPPASTArrayRangeDesignator(des: CPPASTArrayRangeDesignator): Ast = {
    val op        = Operators.arrayInitializer
    val callNode_ =
      callNode(des, code(des), op, op, DispatchTypes.STATIC_DISPATCH, None, Some(Defines.Any))
    val floorAst   = nullSafeAst(des.getRangeFloor)
    val ceilingAst = nullSafeAst(des.getRangeCeiling)
    callAst(callNode_, List(floorAst, ceilingAst))
  }

}
