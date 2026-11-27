package gezi.contest.modules.moore

import java.lang.constant.MethodTypeDesc
import gezi.hotspot.Budget
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.ForeignCall
import gezi.hotspot.ForeignProgress
import gezi.hotspot.ForeignValue
import gezi.hotspot.Progress
import gezi.hotspot.Spent
import gezi.ir.{Closed, Configured, NativeSpecializer, Value}
import gezi.jit.DeclaredValue
import gezi.jit.Jit
import gezi.jit.JitValue
import gezi.jit.JitValues
import gezi.jit.JvmBits
import gezi.jit.JvmBitsFamily
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.weakhead.Answers
import gezi.weakhead.Computation
import gezi.weakhead.ReadingExecutor
import gezi.weakhead.ReadingState
import gezi.weakhead.ReadingSuspension
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*

/** What one layer of a filtered state asks: an answer that ends its branch, or
  * a call with the transition its replies go to.
  */
private enum MooreStep[C <: NativeSpecializer & Singleton]:
  case Answer(term: JitValue[C])
  case Call(call: ForeignCall, transition: JitValue[C])

/** What a round read: the steps of its states, the executor and the steps spent
  * after them, and whether every state of the round was read.
  */
private final case class MooreRound[C <: NativeSpecializer & Singleton](
    steps: Vector[MooreStep[C]],
    executor: ReadingExecutor[C],
    spent: Long,
    complete: Boolean
)

/** The executor that runs FFI programs on the entry's JIT. Every other program
  * it hands to the reading executor it wraps.
  *
  * A program is a state under the filter of one step, `x ∥ moore_state_type`,
  * so that what is not a state never reaches the executor. The JIT reads that
  * decode point to native values, with no normal form: the output decoded, the
  * transition held as it is written. Each member of a choice of states reads as
  * its own output and transition. A state that is no tuple of two, whose output
  * is outside the schema, or whose transition refers to the state's
  * continuation decodes to nothing, which loses an answer and adds none. Each
  * reply stays a native value, applied to the transition, and the result goes
  * under the filter again, so that only one step is ever checked.
  *
  * The calls are made between two readings and never inside one, since a
  * reading's tables hold a pure function of a term.
  *
  * A choice is read as lanes of one batch. The states of a round are read
  * together and all their calls go to the service at once, each reply to its
  * own transition. Choices in different argument positions multiply, since an
  * application does not distribute over a choice in its argument: the calls of
  * `f (a + b) (c + d)` are the four combinations, each a member of the term by
  * the monotonicity of application.
  *
  * FIXME (https://github.com/Atry/private-overlay/issues/1797): the argument
  * values are boxed through `ForeignValue` and called by the service, and only
  * a `call` at an output's root whose arguments are all `decode` runs; nested
  * calls, `new` and whole-block compilation of the call are later steps. A
  * state whose reading the budget ends also ends the run, so that the lanes
  * after it in the round make no call, which loses answers and adds none.
  */
final case class MooreExecutor[C <: NativeSpecializer & Singleton](
    reading: ReadingExecutor[C],
    jit: Jit[C],
    criteria: MooreCriteria[C]
) extends Executor[C, ReadingSuspension[C]]:

  // The configuration's own types and its specializer, in scope of every construction of the executor.
  private type JitValue = gezi.jit.JitValue[C]
  private type Native = NativeValue[JitValue]
  private type MooreStep = gezi.contest.modules.moore.MooreStep[C]
  private given specializer: C = jit.configuration.specializer

  def executed(
      term: Configured[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (
      Executor[C, ReadingSuspension[C]],
      ExecutionDependencies,
      Progress[C, ReadingSuspension[C]]
  ) =
    val (next, after, progress) = reading.executed(term, dependencies, budget)
    (copy(reading = next), after, progress)

  def resumed(
      suspension: ReadingSuspension[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (
      Executor[C, ReadingSuspension[C]],
      ExecutionDependencies,
      Progress[C, ReadingSuspension[C]]
  ) =
    val (next, after, progress) =
      reading.resumed(suspension, dependencies, budget)
    (copy(reading = next), after, progress)

  def exported(
      suspension: ReadingSuspension[C],
      dependencies: ExecutionDependencies
  ): (ExecutionDependencies, Option[Configured[C]]) =
    reading.exported(suspension, dependencies)

  override def foreignProgram(state: Configured[C]): Option[Configured[C]] =
    Some(specializer.parallel(state, criteria.state))

  override def interacted(
      program: Configured[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (
      Executor[C, ReadingSuspension[C]],
      ExecutionDependencies,
      ForeignProgress[C]
  ) =
    // One budget for the whole run: the reading's per-reading costs are cleared
    // once here, and its states' computations share them.
    run(
      Vector(Value.of(program)),
      reading.readingStarted,
      dependencies,
      budget,
      0L,
      Vector.empty
    )

  /** Round after round until no state is pending, or the budget or the stop
    * ends the run: a round reads the states pending, makes all their calls in
    * one batch, and the replies give the next round's states.
    */
  @tailrec
  private def run(
      pending: Vector[JitValue],
      current: ReadingExecutor[C],
      dependencies: ExecutionDependencies,
      budget: Budget,
      spent: Long,
      answers: Vector[Closed[C]]
  ): (
      Executor[C, ReadingSuspension[C]],
      ExecutionDependencies,
      ForeignProgress[C]
  ) =
    def ended(
        executor: ReadingExecutor[C],
        steps: Long,
        found: Vector[Closed[C]],
        finished: Boolean
    ) =
      (
        copy(reading = executor),
        dependencies,
        ForeignProgress(found.distinct, finished, Spent(steps, Map.empty))
      )
    if pending.isEmpty then ended(current, spent, answers, finished = true)
    else if spent >= budget.steps || budget.stop.stopRequested then
      ended(current, spent, answers, finished = false)
    else
      val round =
        roundRead(pending, current, dependencies, budget, spent, Vector.empty)
      // An answer is an output field left unread, a value of the configuration the program was read under: it is
      // closed because the filtered state's reading decodes a closed state.
      val answered = answers ++ round.steps.collect {
        case MooreStep.Answer(term) =>
          Value
            .closed(term)
            .getOrElse(
              throw IllegalStateException(
                s"a decoded answer is not closed: $term"
              )
            )
      }
      val calls = round.steps.collect { case MooreStep.Call(call, transition) =>
        (call, transition)
      }
      val replies =
        if calls.isEmpty then Some(Vector.empty)
        else dependencies.foreign.replies(calls.map(_._1), budget.stop)
      replies match
        case Some(replied) if round.complete =>
          val following =
            calls.zip(replied).flatMap { case ((_, transition), values) =>
              values.map(value =>
                filtered(
                  gezi.ir.Value.Apply(transition, replyValue(value)),
                  criteria.state
                )
              )
            }
          run(
            following,
            round.executor,
            dependencies,
            budget,
            round.spent,
            answered
          )
        case _ => ended(round.executor, round.spent, answered, finished = false)

  /** The steps of the states in order, each read within what is left of the
    * budget; a state the budget or the stop ends leaves the round incomplete,
    * with the steps of the states before it.
    */
  @tailrec
  private def roundRead(
      states: Vector[JitValue],
      current: ReadingExecutor[C],
      dependencies: ExecutionDependencies,
      budget: Budget,
      spent: Long,
      found: Vector[MooreStep]
  ): MooreRound[C] = states.headOption match
    case None => MooreRound(found, current, spent, complete = true)
    case Some(_) if spent >= budget.steps || budget.stop.stopRequested =>
      MooreRound(found, current, spent, complete = false)
    case Some(state) =>
      val (next, read, stepSpent) = current.computed(
        steps(state),
        dependencies,
        budget.copy(steps = budget.steps - spent)
      )
      read match
        case None =>
          MooreRound(found, next, spent + stepSpent, complete = false)
        case Some(stepped) =>
          roundRead(
            states.drop(1),
            next,
            dependencies,
            budget,
            spent + stepSpent,
            found ++ stepped
          )

  private def filtered(term: JitValue, criterion: Configured[C]): JitValue =
    Value.parallel(specializer)(term, Value.of(criterion))

  /** What each layer the filtered state decodes into asks. */
  private def steps(
      state: JitValue
  ): Computation[ReadingState[C], Vector[MooreStep]] =
    jit.representedHeads(state).flatMap(layerSteps).collected

  private def layerSteps(layer: Native): Answers[ReadingState[C], MooreStep] =
    layer match
      case DeclaredValue(
            _,
            0,
            Vector(output, NativeValue.Unread(transition))
          ) =>
        output match
          case DeclaredValue(_, 0, Vector(NativeValue.Unread(answer))) =>
            Answers.single(MooreStep.Answer(answer))
          case DeclaredValue(_, 1, Vector(expression)) =>
            calls(expression, transition)
          case other =>
            throw IllegalStateException(s"a decoded output is $other")
      case other => throw IllegalStateException(s"a decoded state is $other")

  /** The calls the expression at an output's root asks, one for each
    * combination of its symbols' and its arguments' values.
    */
  private def calls(
      expression: Native,
      transition: JitValue
  ): Answers[ReadingState[C], MooreStep] = expression match
    case DeclaredValue(_, 0, Vector(NativeValue.Unread(method), arguments)) =>
      val values = argumentValues(arguments, Vector.empty)
      jit
        .representedHeads(
          filtered(
            Value.Apply(Value.of(criteria.methodSymbols), method),
            criteria.symbols
          )
        )
        .flatMap(symbols =>
          val (owner, name, descriptor) = symbolsRead(symbols)
          val parameters = MethodTypeDesc
            .ofDescriptor(descriptor)
            .parameterList
            .asScala
            .toVector
            .map(_.descriptorString)
          if values.size > parameters.size then Answers.empty
          else
            parameters
              .zip(values)
              .foldLeft(
                Answers
                  .single[ReadingState[C], Vector[ForeignValue]](Vector.empty)
              ) { case (sofar, (parameter, value)) =>
                sofar.flatMap(found =>
                  argumentValue(parameter, value).map(found :+ _)
                )
              }
              .map(read =>
                MooreStep
                  .Call(ForeignCall(owner, name, descriptor, read), transition)
              )
        )
    case other => throw laterStep(s"the node $other at an output's root")

  /** The values of the `decode` nodes of a Scott list of expressions. */
  @tailrec
  private def argumentValues(
      list: Native,
      found: Vector[JitValue]
  ): Vector[JitValue] = list match
    case DeclaredValue(_, 0, Vector()) => found
    case DeclaredValue(
          _,
          1,
          Vector(DeclaredValue(_, 2, Vector(NativeValue.Unread(value))), rest)
        ) =>
      argumentValues(rest, found :+ value)
    case DeclaredValue(_, 1, Vector(nested, _)) =>
      throw laterStep(s"the nested node $nested")
    case other =>
      throw IllegalStateException(s"a decoded list of arguments is $other")

  /** The value at a parameter, read under the criterion its descriptor gives (a
    * Java method's descriptor already gives the type of each of its values).
    */
  private def argumentValue(
      parameter: String,
      value: JitValue
  ): Answers[ReadingState[C], ForeignValue] = parameter match
    case "Z" =>
      jit.representedHeads(filtered(value, criteria.boolean)).map {
        case NativeValue.Truth(truth) => ForeignValue.Truth(truth)
        case other                    =>
          throw IllegalStateException(s"a decoded boolean is $other")
      }
    case "B"       => bitsValue(value, criteria.bits8, 8)
    case "S" | "C" => bitsValue(value, criteria.bits16, 16)
    case "I" | "F" => bitsValue(value, criteria.bits32, 32)
    case "J" | "D" => bitsValue(value, criteria.bits64, 64)
    case other     => throw laterStep(s"an argument at the parameter $other")

  private def bitsValue(
      value: JitValue,
      criterion: Configured[C],
      width: Int
  ): Answers[ReadingState[C], ForeignValue] =
    jit
      .representedHeads(filtered(value, criterion))
      .map(read => ForeignValue.Bits(width, MooreExecutor.bits(read)))

  /** The run-time value of a reply, a value of its representation. */
  private def replyValue(value: ForeignValue): JitValue = value match
    case ForeignValue.Truth(truth) =>
      jit.configuration.operations
        .storageOf(representation(criteria.boolean), NativeValue.Truth(truth))
    case ForeignValue.Bits(width, bits) =>
      jit.configuration.operations.storageOf(
        representation(widthCriterion(width)),
        JvmBitsFamily.masked(width, bits)
      )
    // A service's reply term is a pure term, the same under every configuration, brought into this one.
    case ForeignValue.Term(term) =>
      Value.of(Configured.fromPure(specializer)(term))

  private def widthCriterion(width: Int): Configured[C] = width match
    case 8     => criteria.bits8
    case 16    => criteria.bits16
    case 32    => criteria.bits32
    case 64    => criteria.bits64
    case other =>
      throw IllegalArgumentException(
        s"a reply of $other bits is no JVM value type"
      )

  private def representation(
      criterion: Configured[C]
  ): Representation[JitValue] =
    jit
      .representationOf(criterion)
      .getOrElse(
        throw IllegalStateException(
          s"the entry's knowledge has no family of the criterion $criterion: enable corpora/compiler/java_ffi"
        )
      )

  private def symbolsRead(value: Native): (String, String, String) = value match
    case DeclaredValue(_, 0, Vector(owner, name, descriptor)) =>
      (
        MooreExecutor.text(owner),
        MooreExecutor.text(name),
        MooreExecutor.text(descriptor)
      )
    case other => throw IllegalStateException(s"decoded symbols are $other")

  private def laterStep(what: String): UnsupportedOperationException =
    UnsupportedOperationException(
      s"$what runs in a later step (https://github.com/Atry/private-overlay/issues/1797)"
    )

object MooreExecutor:

  /** The bits of a decoded tuple. */
  private def bits(value: NativeValue[?]): Long = value match
    case JvmBits(_, found) => found
    case other => throw IllegalStateException(s"a decoded bit tuple is $other")

  /** The text of a decoded list of UTF-8 bytes. */
  private def text(list: NativeValue[?]): String =
    val bytes = byteValues(list, Vector.empty)
    Vector
      .unfold(0)(index =>
        bytes.lift(index).map { first =>
          val size = if first < 0x80 then 1
          else if first < 0xe0 then 2
          else if first < 0xf0 then 3
          else 4
          val start = if size == 1 then first else first & (0xff >> (size + 1))
          val codePoint = bytes
            .slice(index + 1, index + size)
            .foldLeft(start)((sofar, byte) => (sofar << 6) | (byte & 0x3f))
          (Character.toString(codePoint), index + size)
        }
      )
      .mkString

  @tailrec
  private def byteValues(
      list: NativeValue[?],
      found: Vector[Int]
  ): Vector[Int] = list match
    case DeclaredValue(_, 0, Vector())           => found
    case DeclaredValue(_, 1, Vector(byte, rest)) =>
      byteValues(rest, found :+ bits(byte).toInt)
    case other =>
      throw IllegalStateException(s"a decoded list of bytes is $other")
