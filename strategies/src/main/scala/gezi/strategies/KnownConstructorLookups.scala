package gezi.strategies

import gezi.ir.Code
import gezi.ir.Spine

/** The kind of a spine head as row 3 reads it: an instruction of no constructor
  * shape, a constructor of some fields applied to some arguments (capped at
  * the fields plus one), or a head that is no instruction.
  */
enum LookupHead:
  case Lookup
  case Constructor(fields: Int, applied: Int)
  case Other

/** The fold state of `known_constructor_lookups` (`lookups(Count, HeadKind,
  * Known)`): the count, which is the value and the rank; the spine head's
  * kind; and whether the term is a known constructor value.
  */
final case class LookupsState(count: BigInt, head: LookupHead, known: Boolean) extends FoldState

/** The reading of `known_constructor_lookups`: the spine head's kind and
  * whether the term is a known constructor value, which an application
  * over it reads; the arguments applied are capped at the fields plus one,
  * so finitely many.
  */
final case class LookupsReading(head: LookupHead, known: Boolean) extends ModuleReading

/** Row 3 of the HM baseline, the repeller of lookups on known constructors,
  * the port of
  * `gezi/prolog/gezi/baseline/known_constructor_lookups.pl`,
  * whose module documentation this follows. The value is the number, over
  * the spines of the spelling, of the arguments that are known constructor
  * values of a spine whose head is an instruction of no constructor shape.
  *
  * CONSTRUCTOR SHAPE (Church and Scott alike): an instruction's layer is a thunk
  * with no filling whose code is a binder c, the head, applied to arguments
  * A1 ... An, each a FIELD (a binder among the leading k binders) or a field
  * applied to every CASE BINDER in order (a folded recursive field); the
  * leading k binders are the fields in order, the case binders are the
  * binders after them, the head among them. The instruction is then a
  * constructor of k fields. A KNOWN CONSTRUCTOR VALUE is a constructor of no
  * field, an application spine whose head is a constructor of k fields
  * applied to exactly k arguments, a thunk with no filling of the shape of a
  * constructor of no field, or an instruction whose layer is such an application
  * or such a thunk (one layer only). The shape is read from the definition,
  * never from a name.
  */
object KnownConstructorLookups extends NormalityModule:

  val name: String = "known_constructor_lookups"

  val meetsExtractionContract: Boolean = true

  def folded(layer: OrderTerm, reading: TermReading): FoldState = state(layer, reading)

  /** A field: a binder at a position, or a binder at a position applied to
    * the binders at the positions given (`field_read/3`).
    */
  private final case class Field(position: Int, applied: Option[Vector[Int]])

  /** The number of fields of a thunk with no filling of the constructor
    * shape (`constructor_fields/2`).
    */
  private def constructorFields(term: OrderTerm): Option[Int] = term match
    case OrderTerm.Thunk(code, holes, Vector()) =>
      Spine.of(code) match
        case (Code.Slot(headSlot), arguments) =>
          for
            headPosition <- TermReading.binderPosition(holes, headSlot)
            read <- sequenced(arguments.map(fieldRead(holes, _)))
            if read.zipWithIndex.forall((field, index) => field.position == index + 1)
            fields = read.size
            if headPosition > fields
            caseBinders = (fields + 1 to holes.size).toVector
            if read.forall(_.applied.forall(_ == caseBinders))
          yield fields
        case _ => None
    case _ => None

  private def sequenced[Value](options: Vector[Option[Value]]): Option[Vector[Value]] =
    if options.forall(_.isDefined) then Some(options.flatten) else None

  private def fieldRead(holes: Vector[gezi.ir.Hole], argument: Code): Option[Field] =
    argument match
      case Code.Slot(slot) => TermReading.binderPosition(holes, slot).map(Field(_, None))
      case _ =>
        Spine.of(argument) match
          case (Code.Slot(slot), appliedSlots) if appliedSlots.nonEmpty =>
            for
              position <- TermReading.binderPosition(holes, slot)
              applied <- sequenced(appliedSlots.map {
                case Code.Slot(appliedSlot) => TermReading.binderPosition(holes, appliedSlot)
                case _                          => None
              })
            yield Field(position, Some(applied))
          case _ => None

  /** The number of fields of an instruction whose layer has the constructor shape
    * (`handle_constructor/2`).
    */
  private def instructionConstructor(term: OrderTerm, reading: TermReading): Option[Int] = term match
    case OrderTerm.Name(instruction) => constructorFields(reading.instructionLayer(instruction))
    case _                      => None

  private def saturatedConstructor(head: OrderTerm, arguments: Vector[OrderTerm], reading: TermReading): Boolean =
    instructionConstructor(head, reading).exists(fields => fields > 0 && arguments.size == fields)

  /** `known_constructor_value/1`. */
  private def knownConstructorValue(term: OrderTerm, reading: TermReading): Boolean = term match
    case OrderTerm.Name(instruction) =>
      val layer = reading.instructionLayer(instruction)
      constructorFields(layer).contains(0) || (layer match
        case application @ OrderTerm.Apply(_, _) =>
          val (head, arguments) = TermReading.spine(application)
          saturatedConstructor(head, arguments, reading)
        case _ => false
      )
    case leaf if TermReading.leafTerm(leaf) => false
    case application @ OrderTerm.Apply(_, _) =>
      val (head, arguments) = TermReading.spine(application)
      saturatedConstructor(head, arguments, reading)
    case thunk @ OrderTerm.Thunk(_, _, _) => constructorFields(thunk).contains(0)
    case _                                => false

  private def state(term: OrderTerm, reading: TermReading): LookupsState = term match
    case OrderTerm.Folded(folded, _) => TermOrder.ownState[LookupsState](folded)
    case name @ OrderTerm.Name(_) =>
      val head = instructionConstructor(name, reading) match
        case Some(fields) => LookupHead.Constructor(fields, 0)
        case None         => LookupHead.Lookup
      LookupsState(0, head, knownConstructorValue(name, reading))
    case leaf if TermReading.leafTerm(leaf) => LookupsState(0, LookupHead.Other, false)
    case OrderTerm.Apply(function, argument) =>
      val functionState = state(function, reading)
      val argumentState = state(argument, reading)
      val own = if functionState.head == LookupHead.Lookup && argumentState.known then 1 else 0
      val head = functionState.head match
        case LookupHead.Constructor(fields, applied) => LookupHead.Constructor(fields, (applied + 1).min(fields + 1))
        case other                                   => other
      val known = head match
        case LookupHead.Constructor(fields, applied) => fields == applied && fields > 0
        case _                                       => false
      LookupsState(functionState.count + argumentState.count + own, head, known)
    case OrderTerm.Choice(members) =>
      LookupsState(members.map(state(_, reading).count).sum, LookupHead.Other, false)
    case OrderTerm.Parallel(left, right, _) =>
      LookupsState(state(left, reading).count + state(right, reading).count, LookupHead.Other, false)
    case thunk @ OrderTerm.Thunk(code, holes, fillings) =>
      val body = state(TermReading.resolved(code, holes, fillings), reading)
      LookupsState(body.count, LookupHead.Other, knownConstructorValue(thunk, reading))
    case other => TermOrder.refused(other)

  def rank(state: FoldState): OrderValue = OrderValue.Number(TermOrder.ownState[LookupsState](state).count)

  override def reading(state: FoldState): ModuleReading =
    val own = TermOrder.ownState[LookupsState](state)
    LookupsReading(own.head, own.known)

  def value(state: FoldState): OrderValue = rank(state)
