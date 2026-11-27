package gezi.strategies

import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.Code
import gezi.ir.DispatchPattern
import gezi.ir.Fallback
import gezi.ir.Specialization
import gezi.ir.SpecializationRange
import gezi.frontend.Defunctionalization
import gezi.ir.{Configured, NativeSpecializer}
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.{Apply, Choice, Opaque, Parallel, Thunk, UriNode}

/** A filter function's code `parallel(slot(Value), slot(Criterion))`, its holes
  * and its fillings.
  */
final case class FilterFunction[C <: NativeSpecializer & Singleton](
    code: Code,
    holes: Vector[Hole],
    fillings: Vector[OrderTerm[C]]
):

  /** The slot of the filter's value. */
  def valueSlot: Int = TermReading.slotPairSlots(code)._1

  /** The slot of the filter's criterion. */
  def criterionSlot: Int = TermReading.slotPairSlots(code)._2

/** The readings of IR terms that more than one module of a normality degree
  * uses, the port of `gezi/prolog/gezi/baseline/term_reading.pl`, whose module
  * documentation (THE RESOLVED BODY, FILTERS, THE OPERANDS) the readings
  * follow. It names no module. It reads the layer each instruction carries; a
  * name's term it reads from nowhere (`nameTerm`, FIXME).
  * https://github.com/Atry/private-overlay/issues/1960
  *
  * Malformed input throws `TermOrderError` with `SlotOutOfRange`, or
  * `LambdaError` with `FillingsNotMatched` from the slot assignment of
  * `Defunctionalization.slotValues` for a thunk whose fillings do not match its
  * non-hole slots.
  */
final case class TermReading[C <: NativeSpecializer & Singleton](
    index: StandardLibraryIndex[C]
):

  /** The front end entry of each library term the index declares `name_marker`,
    * `closure_marker`, `tag_origin` or `tag_next`, the first the index gives.
    */
  val occurrenceRoles: Map[Configured[C], Property] =
    index.combinatorProperties.reverse.collect {
      case CombinatorProperty(
            instruction,
            role @ (Property.NameMarker | Property.ClosureMarker |
            Property.TagOrigin | Property.TagNext)
          ) =>
        (Configured.fromPure[C](index.specializer)(instruction), role)
    }.toMap

  /** The library terms the index declares `repeller`: an application of one
    * repels its class from the extraction (`ModuleCostModel.repeller`).
    */
  val repellers: Set[Configured[C]] =
    index.combinatorProperties.collect {
      case CombinatorProperty(instruction, Property.Repeller) =>
        Configured.fromPure[C](index.specializer)(instruction)
    }.toSet

  /** The term a name stands for, the order term of its layer with the names
    * under it kept as names: none for every instruction.
    *
    * FIXME (2026-11-13): broken, the readers of a name's term read none.
    * https://github.com/Atry/private-overlay/issues/1960 The terms were the
    * index's definitions (`OrderTerm.layerOf` of each define's instruction),
    * empty since 977af2109 (step L5) and deleted with the index's definitions
    * when the library became files reached by paths (read back with
    * `git show c30720a56:lambda_jit/strategies/src/main/scala/lambdajit/strategies/TermReading.scala`).
    * Its readers therefore never see a named filter function, input filter, eta
    * expansion or application (`filterFunction`, `applicationNamed`,
    * `InputFilterRepulsion`, `OrdinaryFilters`), and `instructionLayer` reads a
    * name's own layer one level down. The candidate is the round's leaves
    * (`StandardLibraryIndex.noinline`, the names an order term keeps folded);
    * it changes the term order, so it is a change of its own whose readings are
    * reviewed, not part of the deletion.
    */
  def nameTerm(instruction: Configured[C]): Option[OrderTerm[C]] = None

  /** The term of a name (`nameTerm`), else the stored layer the instruction
    * stands for, each child `Unfolded` (`handle_layer/2` of the modules that
    * read it); a native storage the e-graph keeps as a leaf is itself
    * `Unfolded`, a term no reading looks into, its view not read.
    */
  def instructionLayer(instruction: Configured[C]): OrderTerm[C] =
    given C = index.specializer
    nameTerm(instruction).getOrElse(
      if instruction.heldAsLeaf then OrderTerm.Unfolded(instruction)
      else
        instruction.layer match
          case Apply(function, argument) =>
            OrderTerm.Apply(
              OrderTerm.Unfolded(function),
              OrderTerm.Unfolded(argument)
            )
          case Parallel(left, right) =>
            OrderTerm.Parallel(
              OrderTerm.Unfolded(left),
              OrderTerm.Unfolded(right),
              specializationRange = false
            )
          case Choice(_, _) =>
            // The members of the right `+` spine, a right side that is a leaf
            // ending it, as `OrderTerm.layerOf` reads them.
            val members = gezi.ir.ChoiceSpine.members[Configured[C]](
              instruction,
              current =>
                if !Configured.same(current, instruction) && nameTerm(
                    current
                  ).isDefined
                then None
                else
                  current.layer match
                    case Choice(left, right) => Some((left, right))
                    case _                   => None
            )
            OrderTerm.Choice(members.map(OrderTerm.Unfolded(_)))
          case Thunk(code, holes, fillings) =>
            OrderTerm.Thunk(code, holes, fillings.map(OrderTerm.Unfolded(_)))
          case UriNode(_) | Opaque(_) =>
            throw IllegalStateException(s"the opaque $instruction has no layer")
          // A storage is a leaf of its term's layer, its view not read.
          case _: gezi.ir.NativeStorage => OrderTerm.Unfolded(instruction)
    )

  /** The instruction reads as an application: its term is one
    * (`application_named/2`).
    */
  def applicationNamed(term: OrderTerm[C]): Option[OrderTerm[C]] = term match
    case OrderTerm.Name(instruction) =>
      nameTerm(instruction).collect {
        case application @ OrderTerm.Apply(_, _) => application
      }
    case _ => None

  /** The head, read through names of applications beforehand, is a filter
    * function: a thunk of code `parallel(slot(_), slot(_))` or an instruction
    * whose term is one (`filter_function/4`).
    *
    * FIXME (carried from term_reading.pl:165; X4 at extraction and an
    * https://github.com/Atry/private-overlay/issues/1952 unproven filter at
    * extraction, see `FilterAttraction`'s documentation): the criterion is the
    * right operand by the standard order of ∥; nothing reads whether it is a
    * type, nor whether the filter is proven.
    */
  def filterFunction(head: OrderTerm[C]): Option[FilterFunction[C]] =
    val thunk = head match
      case OrderTerm.Name(instruction) => nameTerm(instruction)
      case other                       => Some(other)
    thunk.collect {
      case OrderTerm.Thunk(code, holes, fillings)
          if TermReading.slotPair(code) =>
        FilterFunction(code, holes, fillings)
    }

/** The readings of terms that need no index. */
object TermReading:

  /** An opaque leaf: a metavariable of a pattern, a hole of a resolved body
    * (`leaf_term/1`), or a child no module prices.
    */
  def leafTerm[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C]
  ): Boolean = term match
    case OrderTerm.Metavariable(_) | OrderTerm.Bound(_) |
        OrderTerm.Unpriced(_) =>
      true
    case _ => false

  /** The flattened application spine: the head and the arguments (`spine/3`).
    */
  def spine[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C]
  ): (OrderTerm[C], Vector[OrderTerm[C]]) =
    @scala.annotation.tailrec
    def collected(
        current: OrderTerm[C],
        arguments: List[OrderTerm[C]]
    ): (OrderTerm[C], Vector[OrderTerm[C]]) =
      current match
        case OrderTerm.Apply(function, argument) =>
          collected(function, argument :: arguments)
        case head => (head, arguments.toVector)
    collected(term, Nil)

  /** The body of a thunk, each hole a leaf `Bound`, each filled slot its
    * filling; an inner thunk's fillings, codes over the enclosing slots,
    * resolved in turn (`resolved/4`).
    */
  def resolved[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[OrderTerm[C]]
  ): OrderTerm[C] =
    instantiated(code, holes, fillings, Vector.empty)._1

  /** The code with the arguments in its holes in lambda order (an ignored hole
    * dropping its argument), a hole left without one a leaf `Bound`, and the
    * fillings in the other slots; and the arguments beyond the holes
    * (`instantiated/6`).
    */
  def instantiated[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[OrderTerm[C]],
      arguments: Vector[OrderTerm[C]]
  ): (OrderTerm[C], Vector[OrderTerm[C]]) =
    val holeValues = holes.zipWithIndex.map((hole, position) =>
      if position < arguments.size then arguments(position)
      else OrderTerm.Bound[C](hole)
    )
    val extra = arguments.drop(holes.size)
    val assignment = Defunctionalization.slotValues(holes, holeValues, fillings)
    (codeResolved(code, assignment), extra)

  private def codeResolved[C <: NativeSpecializer & Singleton](
      code: Code,
      assignment: Vector[OrderTerm[C]]
  ): OrderTerm[C] = code match
    case Code.Slot(index) =>
      if index >= 0 && index < assignment.size then assignment(index)
      else
        throw TermOrderError(
          TermOrderErrorReason.SlotOutOfRange(index, assignment)
        )
    case Code.Apply(function, argument) =>
      OrderTerm.Apply(
        codeResolved(function, assignment),
        codeResolved(argument, assignment)
      )
    case Code.Parallel(left, right) =>
      OrderTerm.Parallel(
        codeResolved(left, assignment),
        codeResolved(right, assignment),
        specializationRange = false
      )
    case Code.Choice(left, right) =>
      dispatchPattern(left, right, assignment) match
        case Some(Left(specialization)) =>
          typedMember(specialization.map(codeResolved(_, assignment)))
        case Some(Right(judgment)) => codeResolved(judgment.value, assignment)
        case None => OrderTerm.Choice(choiceMembers(code, assignment))
    case Code.Thunk(inner, innerHoles, fillingCodes) =>
      OrderTerm.Thunk(
        inner,
        innerHoles,
        fillingCodes.map(codeResolved(_, assignment))
      )

  /** The typed member of a specialization choice the dispatch recognizer
    * accepts (`DispatchPattern.typedMember`), its range `F (A ∥ D) ∥ R` marked
    * as one (`OrderTerm.Parallel.specializationRange`): the code's dispatch
    * pattern and the extraction's `Specialization` production are priced alike.
    */
  def typedMember[C <: NativeSpecializer & Singleton](
      specialization: Specialization[OrderTerm[C]]
  ): OrderTerm[C] = specialization.range match
    case SpecializationRange.Filtered(range) =>
      val application =
        DispatchPattern.typedMember(
          specialization.copy(range = SpecializationRange.Absent),
          ModuleCostModel.orderPatternLayer[C]
        )
      OrderTerm.Parallel(application, range, specializationRange = true)
    case SpecializationRange.Absent | SpecializationRange.Contracted(_) =>
      DispatchPattern.typedMember(
        specialization,
        ModuleCostModel.orderPatternLayer[C]
      )

  /** The members of a choice's right `+` spine resolved, a right side that is a
    * dispatch pattern ending it as one member.
    */
  private def choiceMembers[C <: NativeSpecializer & Singleton](
      code: Code,
      assignment: Vector[OrderTerm[C]]
  ): Vector[OrderTerm[C]] = code match
    case Code.Choice(left, right)
        if dispatchPattern(left, right, assignment).isEmpty =>
      codeResolved(left, assignment) +: choiceMembers(right, assignment)
    case other => Vector(codeResolved(other, assignment))

  /** The dispatch pattern the choice of the two codes is read as
    * (`DispatchPattern`), which `codeResolved` resolves as what the refinement
    * runs of it (`ModuleCostModel`, THE PRICE OF A CHOICE): a specialization
    * choice its typed member, whether or not its criteria decode, which only
    * decides whether the run checks them; a judgment its value. A curried
    * member's contract is a slot whose filling is λf. f (`identityContract`).
    */
  private def dispatchPattern[C <: NativeSpecializer & Singleton](
      left: Code,
      right: Code,
      assignment: Vector[OrderTerm[C]]
  ): Option[Either[Specialization[Code], Fallback[Code]]] =
    DispatchPattern
      .specializations(
        left,
        right,
        DispatchPattern.codeLayers,
        slotIdentity(assignment)
      )
      .headOption match
      case Some(specialization) => Some(Left(specialization))
      case None                 =>
        DispatchPattern
          .fallbacks(left, right, DispatchPattern.codeLayers)
          .headOption
          .map(Right(_))

  /** The code is a slot whose filling is λf. f. */
  private def slotIdentity[C <: NativeSpecializer & Singleton](
      assignment: Vector[OrderTerm[C]]
  )(code: Code): Boolean = code match
    case Code.Slot(index) => assignment.lift(index).exists(identityContract)
    case _                => false

  /** The term's spelling is λf. f as the refinement runs it
    * (`DispatchPattern.identityContractLayer`): a name by its layers, an opaque
    * one and a native storage having none; a child entry by its cost's flag
    * (`ModuleCost.identityContract`); a thunk by its code over its fillings.
    */
  def identityContract[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C]
  ): Boolean = term match
    case OrderTerm.Name(instruction) =>
      // A native storage is a value, never λf. f: no layer read, its view not made.
      DispatchPattern.identityContract(instruction, termLayers[C])
    case OrderTerm.Folded(_, identity)          => identity
    case OrderTerm.Thunk(code, holes, fillings) =>
      DispatchPattern.identityContractLayer(
        Thunk(code, holes, fillings),
        identityContract
      )
    case _ => false

  /** The layers of a term of the configuration read as a node of the dispatch
    * patterns: its own, a term held as a leaf (an opaque term, a storage)
    * having none.
    */
  def termLayers[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  ): Vector[Layer[Configured[C]]] =
    if term.heldAsLeaf then Vector.empty
    else
      term.layer match
        case layer @ (Apply(_, _) | Parallel(_, _) | Choice(_, _) |
            Thunk(_, _, _)) =>
          Vector(layer)
        case _ => Vector.empty

  /** The position, from 1, of the binder whose hole is the slot
    * (`binder_position/3`).
    */
  def binderPosition(holes: Vector[Hole], slot: Int): Option[Int] =
    val position = holes.indexOf(Hole.Bound(slot))
    if position >= 0 then Some(position + 1) else None

  /** The code of a filter function (`slot_pair/1`). */
  def slotPair(code: Code): Boolean = code match
    case Code.Parallel(Code.Slot(_), Code.Slot(_)) => true
    case _                                         => false

  /** The value slot and the criterion slot of a filter function's code. */
  def slotPairSlots(code: Code): (Int, Int) = code match
    case Code.Parallel(Code.Slot(value), Code.Slot(criterion)) =>
      (value, criterion)
    case other =>
      throw IllegalArgumentException(s"the code $other is no filter function's")
