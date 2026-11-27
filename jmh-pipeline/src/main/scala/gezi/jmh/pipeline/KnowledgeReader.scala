package gezi.jmh.pipeline

import gezi.weakhead.ApplicationReading
import gezi.weakhead.Computation
import gezi.weakhead.Computed
import gezi.weakhead.Head
import gezi.weakhead.Mode
import gezi.weakhead.NeutralVariable
import gezi.weakhead.ParallelView
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead
import gezi.ir.{Configured, NativeSpecializer, ChoiceSpine, NoFacts}

/** The configuration of the terms here: no facts. */
private given knowledgeReaderNoFacts: NoFacts.type = NoFacts

/** The fresh neutral handler of the slot at the position, from 0.
  *
  * A neutral value, a free variable, used here as an exception argued at its
  * declaration (`CONTRIBUTING.md`, "Types live only in the term"): it stands
  * for a binder of the value read (a Scott value's handler, a constructor's or
  * a define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument. A
  * closed term in its place would not do: a term that is no such value could
  * ignore it and build the reading itself.
  */
final case class SlotHandler(position: Int) extends NeutralVariable

/** The fresh neutral variable a lemma's Scott pair is opened with.
  *
  * A neutral value, a free variable, used here as an exception argued at its
  * declaration (`CONTRIBUTING.md`, "Types live only in the term"): it stands
  * for a binder of the value read (a Scott value's handler, a constructor's or
  * a define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument. A
  * closed term in its place would not do: a term that is no such value could
  * ignore it and build the reading itself.
  */
case object PairSelector extends NeutralVariable

/** A reading of a knowledge term: what it read, the evaluator steps it spent
  * and the tables it held at its end (none untabled).
  */
final case class KnowledgeReading(read: KnowledgeRead, spent: Long, tables: Int)

/** How the slots of the top-level mixin are read. */
enum SlotReading:

  /** Each slot by its own self-application `o o c1 ... cW`, its handler the
    * slot's neutral handler and every other c top: the reading the encoding of
    * [[KnowledgeInLambdalattice]] is written for.
    */
  case OneSlotEach

  /** Every slot by one self-application, each c the neutral handler of its
    * slot, a variant of `OneSlotEach`.
    */
  case AllSlotsAtOnce

/** The measurement-only reader of a knowledge term
  * ([[KnowledgeInLambdalattice]]) on the weak-head evaluator: a slot's heads
  * are its handler applied to each wrapper's b, a choice whose members are read
  * off its IR layer; each member of a lemma slot, applied to the fresh neutral
  * variable `PairSelector`, has the one head `PairSelector L R`. The whole
  * reading runs within one budget of steps; a reading the budget stops, or a
  * head of another shape, is an error of the knowledge term, thrown as
  * `IllegalStateException`.
  */
object KnowledgeReader:

  /** The reading of the knowledge term with the slots of the layout, under the
    * mode and the option of taking applications apart, within the limit of
    * steps.
    */
  def read[C <: NativeSpecializer & Singleton](
      mode: Mode,
      applications: ApplicationReading,
      slotReading: SlotReading,
      knowledge: Configured[C],
      layout: Vector[KnowledgeSlot],
      limit: Long
  )(using C): KnowledgeReading =
    val (read, after) =
      finished(mode, applications, slotReading, knowledge, layout, limit)
    KnowledgeReading(read, after.budget.spent, after.tables.held)

  /** What the reading read and the state it ended in. */
  private def finished[C <: NativeSpecializer & Singleton](
      mode: Mode,
      applications: ApplicationReading,
      slotReading: SlotReading,
      knowledge: Configured[C],
      layout: Vector[KnowledgeSlot],
      limit: Long
  )(using C): (KnowledgeRead, ReadingState[C]) =
    val computation = for
      contents <- slotContents(mode, slotReading, knowledge, layout.size)
      lemmas <- Computation.traversed(layout.zip(contents).collect {
        case (KnowledgeSlot.Lemmas, pairs) => pairs
      })(pairs => Computation.traversed(pairs)(opened(mode, _)))
    yield KnowledgeRead(
      lemmas.flatten,
      layout.zip(contents).collect {
        case (KnowledgeSlot.WithProperty(property), members) =>
          (property, members)
      },
      layout.zip(contents).collect {
        case (KnowledgeSlot.Implemented(native), members) => (native, members)
      }
    )
    computation.result(
      ReadingState
        .knowingTop(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
        .copy(applications = applications)
    ) match
      case Computed.Done(read, after) => (read, after)
      case Computed.Stopped(after)    =>
        throw IllegalStateException(
          s"the knowledge term was not read within $limit steps (${after.exhausted})"
        )

  /** The members of each slot, in the order of the slots. */
  private def slotContents[C <: NativeSpecializer & Singleton](
      mode: Mode,
      slotReading: SlotReading,
      knowledge: Configured[C],
      width: Int
  )(using C): Computation[ReadingState[C], Vector[Vector[Configured[C]]]] =
    slotReading match
      case SlotReading.OneSlotEach =>
        Computation.traversed((0 until width).toVector)(position =>
          heads(mode, selfApplication(knowledge, width, Set(position))).map(
            found => found.flatMap(head => handled(head, Set(position))._2)
          )
        )
      case SlotReading.AllSlotsAtOnce =>
        val positions = (0 until width).toSet
        heads(mode, selfApplication(knowledge, width, positions)).map { found =>
          val handledHeads = found.map(handled(_, positions))
          (0 until width).toVector.map(position =>
            handledHeads.collect { case (`position`, members) =>
              members
            }.flatten
          )
        }

  /** `o o c1 ... cW`, the c of each handled position its neutral handler and
    * every other c top (`KnowledgeInLambdalattice.noAnswer`). The reading knows
    * top (`ReadingState.knowingTop`, as the host's `KnowledgeReading` reads),
    * so an unhandled slot's `top b`, which is `top ∥ b`, has no parallel set,
    * as `{} b` had none before top replaced `{}`; read without knowing top,
    * `top ∥ b` was one parallel set of top's head and b's, which `handled`
    * refused.
    */
  private def selfApplication[C <: NativeSpecializer & Singleton](
      knowledge: Configured[C],
      width: Int,
      handledPositions: Set[Int]
  )(using C): Value[C] =
    val self = knowledge
    (0 until width).foldLeft(Value.Apply(self, self): Value[C])(
      (function, position) =>
        Value.Apply(
          function,
          if handledPositions.contains(position) then
            NeutralValue(SlotHandler(position), Vector.empty)
          else KnowledgeInLambdalattice.noAnswer[C]
        )
    )

  /** The position of a slot's head and the members of its b. */
  private def handled[C <: NativeSpecializer & Singleton](
      head: Head[C],
      handledPositions: Set[Int]
  )(using C): (Int, Vector[Configured[C]]) = head match
    case Head.Neutral(SlotHandler(position), Vector(body))
        if handledPositions.contains(position) =>
      // The members of b's right `+` spine, which top ends
      // (`KnowledgeInLambdalattice.term`).
      val chain = Values.instruction(body)
      ChoiceSpine.members[Configured[C]](
        chain,
        term =>
          term.layer match
            case gezi.ir.Choice(left, right) => Some((left, right))
            case _                           => None
      ) match
        case members :+ ended
            if Configured.same(ended, KnowledgeInLambdalattice.noAnswer[C]) =>
          (position, members)
        case _ =>
          throw IllegalStateException(
            s"a slot's b is no chain ended by top: $chain"
          )
    case other =>
      throw IllegalStateException(
        s"a slot's head is not its handler applied to a b: $other"
      )

  /** The two sides of a lemma's Scott pair. */
  private def opened[C <: NativeSpecializer & Singleton](
      mode: Mode,
      pair: Configured[C]
  )(using C): Computation[ReadingState[C], (Configured[C], Configured[C])] =
    heads(mode, Value.Apply(pair, NeutralValue(PairSelector, Vector.empty)))
      .map {
        case Vector(Head.Neutral(PairSelector, Vector(left, right))) =>
          (Values.instruction(left), Values.instruction(right))
        case other =>
          throw IllegalStateException(s"a lemma is no Scott pair: $other")
      }

  /** The head of every parallel set of the term, as plain values. Throws
    * `IllegalStateException` for a parallel set that is not one head: the
    * knowledge terms of the benchmark are written without a parallel.
    */
  private def heads[C <: NativeSpecializer & Singleton](
      mode: Mode,
      term: Value[C]
  )(using C): Computation[ReadingState[C], Vector[Head[C]]] =
    WeakHead
      .heads(mode, term)
      .collected
      .map(found =>
        found.map(set =>
          set.view match
            case ParallelView.Single(head) => head
            case _                         =>
              throw IllegalStateException(
                s"a parallel set of the knowledge is not one head: $set"
              )
        )
      )
