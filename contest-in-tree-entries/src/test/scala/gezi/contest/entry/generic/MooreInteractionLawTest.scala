package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.Interaction
import gezi.contest.entry.OutputDisplay
import gezi.contest.modules.moore.MooreExecutor
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.ReadableText
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.SeededSnapshots
import gezi.hotspot.ExpansionSource
import gezi.hotspot.ForeignCall
import gezi.hotspot.ForeignService
import gezi.hotspot.ForeignValue
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.jit.JitRunState
import gezi.jit.NativesProvider
import gezi.saturation.StopSignal
import snapshot4s.generated.snapshotConfig

private given mooreInteractionLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of an FFI program run by a configured entry
  * on the fixture
  * entry whose executor is the Moore module and on generated values, with a
  * scripted service. Its purpose is to catch a value decoded wrongly, a reply
  * given to another member's transition, and a state outside the criterion
  * that still answers. The laws read answers only: which calls an executor
  * makes is its behaviour, and whether two executors cause the same side
  * effects is outside what the language means.
  * The snapshot records what this configuration calls and replies, which is
  * not a promise of the language, as no snapshot of a behaviour is.
  */
class MooreInteractionLawTest extends GeneratedProperties with SeededSnapshots:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  private lazy val entry: GenericEntry[?] =
    val (data, afterEntry) = EntryData.at(
      buildRoot,
      buildRoot.resolve("tests/moore_fixtures/entry_with_moore.lambdalattice"),
      Defaults.entryDataState
    )
    GenericEntryProvider.initialized(
      data,
      ExecutorModules.registered(buildRoot),
      ExtractorModules.registered(buildRoot),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )

  /** The fixture entry, read before the first test and not charged to it. */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => entry)

  /** Replies to each call with its arguments, one reply for each. */
  private object Echoing extends ForeignService:
    def replies(calls: Vector[ForeignCall], stop: StopSignal): Option[Vector[Vector[ForeignValue]]] =
      Some(calls.map(_.arguments))

  /** Replies to each call with a closed term that spells the call, so that
    * an answer that holds its replies shows the calls in the order they
    * reached it.
    */
  private object Spelling extends ForeignService:
    def replies(calls: Vector[ForeignCall], stop: StopSignal): Option[Vector[Vector[ForeignValue]]] =
      Some(calls.map(call =>
        val arguments = call.arguments.collect { case ForeignValue.Bits(width, value) => s"$width:$value" }.mkString(",")
        Vector(ForeignValue.Term(closed(s"λk. k \"${call.owner}.${call.name}${call.descriptor}[$arguments]\"")))
      ))

  private def closed(text: String): Configured[NoFacts.type] = Defunctionalization.thunkInstruction(Lambdalattice.term(text))(using gezi.ir.NoFacts)

  private val identity: Configured[NoFacts.type] = closed("λx. x")

  /** The bit tuple of the byte, high bit first (`java_ffi/bits`). */
  private def byteText(value: Byte): String =
    val bits = (7 to 0 by -1).map(bit => if ((value >> bit) & 1) == 1 then "(λt e. t)" else "(λt e. e)").mkString(" ")
    s"(λtuple. tuple $bits)"

  /** The state that calls a method of one byte and goes on with the transition. */
  private def callState(value: Byte, transition: String): String =
    val decoded = s"(λon_call on_new on_decode. on_decode ${byteText(value)})"
    val arguments = s"(λh t n c. c h t) $decoded (λn c. n)"
    val expression = s"(λon_call on_new on_decode. on_call (λk. k [\"test/Echo\", \"echo\", \"(B)V\"]) ($arguments))"
    s"(λk. k (λon_finish on_run. on_run $expression) ($transition))"

  /** The state that ends its branch with the answer. */
  private def finishState(answer: String): String =
    s"(λk. k (λon_finish on_run. on_finish ($answer)) (λignored. λy. y))"

  private val pair = "(λx y s. s x y)"

  /** The normal forms of the answers of the program under the service. */
  private def answers(program: String, service: ForeignService, stop: StopSignal): Set[Configured[NoFacts.type]] =
    val source = ExpansionSource.fresh()
    val run = entry
      .interacted(closed(program), service, source, stop)
      .getOrElse(throw IllegalStateException("the fixture entry's executor runs no FFI program"))
    assert(run.finished, s"the run of $program did not finish")
    run.answers.flatMap(normalForms(_, source, stop)).toSet

  private def normalForms(term: Configured[NoFacts.type], source: ExpansionSource, stop: StopSignal): Vector[Configured[NoFacts.type]] =
    val output = NoFacts.application(identity, term)
    given gezi.ir.StorageAccess = gezi.weakhead.ReadingConfiguration.withoutFacts.storageAccess
    entry.run(Cells.cell(DeBruijnTerm.Constant(output)), source, stop) match
      case Interaction.Finished(OutputDisplay.Values(choices), _, _) =>
        gezi.weakhead.ScottADTChoices.members(choices).map(gezi.weakhead.ScottADTChoices.withFilters)
      case Interaction.Finished(OutputDisplay.Remainder(_) | OutputDisplay.Mixed(_, _), _, _) =>
        throw IllegalStateException(s"the entry did not evaluate $term")

  private val byte: Gen[Byte] = Gen.byte(Range.constant(Byte.MinValue, Byte.MaxValue))

  /** The text of a closed normal form, a Church numeral. */
  private val normalForm: Gen[String] =
    Gen.int(Range.linear(0, 4)).map(count => s"λf x. ${"f (" * count}x${")" * count}")

  stoppableProperty("a reply reaches the transition of the output it answers") { stopped =>
    for
      value <- byte.forAll
      w <- normalForm.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val found = answers(callState(value, s"λreply. ${finishState(s"$pair reply ($w)")}"), Echoing, stop)
      Result.diff(found, normalForms(closed(s"$pair ${byteText(value)} ($w)"), ExpansionSource.fresh(), stop).toSet)(_ == _)
  }

  stoppableProperty("each member of a choice of states goes on with the replies to its own output") { stopped =>
    for
      first <- byte.forAll
      offset <- Gen.int(Range.linear(1, 255)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val second = (first + offset).toByte
      def branch(value: Byte, tag: String): String = callState(value, s"λreply. ${finishState(s"$pair $tag reply")}")
      val found = answers(s"(${branch(first, "(λt e. t)")} + ${branch(second, "(λt e. e)")})", Echoing, stop)
      val expected = Vector(s"$pair (λt e. t) ${byteText(first)}", s"$pair (λt e. e) ${byteText(second)}")
        .flatMap(text => normalForms(closed(text), ExpansionSource.fresh(), stop))
        .toSet
      Result.diff(found, expected)(_ == _)
  }

  /** The states outside the criterion: a third field, an output with an
    * argument after its last field, and a transition that refers to the
    * state's continuation, each of which the filter turns into the top of
    * ⊑_O, no answer.
    */
  private def outside(answer: String): Gen[String] = Gen.elementUnsafe(
    List(
      s"(λk. k (λon_finish on_run. on_finish ($answer)) (λi. λy. y) (λy. y))",
      s"(λk. k (λon_finish on_run. on_finish ($answer) (λy. y)) (λi. λy. y))",
      s"(λk. k (λon_finish on_run. on_finish ($answer)) k)"
    )
  )

  stoppableProperty("a state outside the criterion has no answer") { stopped =>
    for
      other <- normalForm.forAll
      state <- outside(other).forAll
    yield Result.diff(answers(state, Echoing, StopSignal.completedWith(stopped)), Set.empty[Configured[NoFacts.type]])(_ == _)
  }

  private val fewInputs: hedgehog.core.PropertyConfig => hedgehog.core.PropertyConfig =
    _.copy(testLimit = hedgehog.core.SuccessCount(12))

  /** The state that calls a method of two bytes, each argument a choice of
    * the values, and ends with the reply.
    */
  private def choicesCall(first: List[Byte], second: List[Byte]): String =
    def decoded(values: List[Byte]) =
      s"(λon_call on_new on_decode. on_decode ${values.map(byteText).mkString("(", " + ", ")")})"
    val cons = "(λh t n c. c h t)"
    val arguments = s"$cons ${decoded(first)} ($cons ${decoded(second)} (λn c. n))"
    val expression = s"(λon_call on_new on_decode. on_call (λk. k [\"test/Echo\", \"pair\", \"(BB)V\"]) ($arguments))"
    s"(λk. k (λon_finish on_run. on_run $expression) (λreply. ${finishState("reply")}))"

  /** Its purpose is to catch choices in two argument positions read as lanes
    * paired by position, or some combination not called.
    */
  stoppableProperty("the calls of choices in two arguments are their cartesian product", fewInputs) { stopped =>
    for
      first <- Gen.list(byte, Range.linear(1, 3)).forAll
      second <- Gen.list(byte, Range.linear(1, 3)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val found = answers(choicesCall(first, second), Spelling, stop)
      val expected =
        for
          left <- first.distinct
          right <- second.distinct
          term <- normalForms(
            closed(s"λk. k \"test/Echo.pair(BB)V[8:${left & 0xff},8:${right & 0xff}]\""),
            ExpansionSource.fresh(),
            stop
          )
        yield term
      Result.diff(found, expected.toSet)(_ == _)
  }

  /** Replies to each call with a closed term that spells how many calls its
    * batch holds, so that an answer shows the batches its branch went through.
    */
  private object BatchSizing extends ForeignService:
    def replies(calls: Vector[ForeignCall], stop: StopSignal): Option[Vector[Vector[ForeignValue]]] =
      Some(calls.map(_ => Vector(ForeignValue.Term(closed(s"λk. k ${calls.size}")))))

  /** Its purpose is to catch the branches of a choice falling out of one
    * batch after their first call. The batches are this executor's behaviour
    * and no promise of the language.
    */
  stoppableProperty("the branches of a choice make each round's calls in one batch", fewInputs) { stopped =>
    for
      first <- byte.forAll
      offset <- Gen.int(Range.linear(1, 255)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val second = (first + offset).toByte
      val batch = "(λk. k 2)"
      def branch(value: Byte, tag: String): String =
        callState(value, s"λone. ${callState(value, s"λtwo. ${finishState(s"$pair $tag ($pair one two)")}")}")
      val found = answers(s"(${branch(first, "(λt e. t)")} + ${branch(second, "(λt e. e)")})", BatchSizing, stop)
      val expected = Vector("(λt e. t)", "(λt e. e)")
        .flatMap(tag => normalForms(closed(s"$pair $tag ($pair $batch $batch)"), ExpansionSource.fresh(), stop))
        .toSet
      Result.diff(found, expected)(_ == _)
  }

  /** A recursion of `count` calls whose one accumulator links each reply to
    * the ones before it, so that a step's own evaluation does not grow with
    * the count while the state does.
    */
  private def linkedCalls(count: Int): String =
    def natural(value: Int): String = if value == 0 then "(λz s. z)" else s"(λz s. s ${natural(value - 1)})"
    val fixpoint = "(λf. (λx. f (x x)) (λx. f (x x)))"
    val step = callState(7, s"λr. self ($pair r accumulator) rest")
    s"($fixpoint (λself accumulator n. n ${finishState("accumulator")} (λrest. $step))) (λy. y) ${natural(count)}"

  private def countsAfter(after: gezi.contest.entry.Entry[?]): gezi.jit.JitCounts = after match
    case generic: GenericEntry[?] =>
      generic.executor match
        case moore: MooreExecutor[?] => countsOf(moore)
        case other                   => throw IllegalStateException(s"the fixture entry's executor is $other")
    case other => throw IllegalStateException(s"the fixture entry became $other")

  /** The counts of the JIT state the Moore executor's reading holds under its JIT's configuration. */
  private def countsOf[C <: gezi.ir.NativeSpecializer & Singleton](moore: MooreExecutor[C]): gezi.jit.JitCounts =
    JitRunState
      .held(moore.reading.jitState, moore.jit.configuration)
      .getOrElse(throw IllegalStateException(s"the executor holds no JIT state: ${moore.reading.jitState}"))
      .counts

  /** The values the check that a field holds no case of a decoding visits
    * in a run of `count` linked calls.
    */
  private def caseWalkVisits(count: Int, stop: StopSignal): Long =
    val run = entry
      .interacted(closed(linkedCalls(count)), Echoing, ExpansionSource.fresh(), stop)
      .getOrElse(throw IllegalStateException("the fixture entry's executor runs no FFI program"))
    assert(run.finished, s"the run of $count calls did not finish")
    countsAfter(run.entry).decodingCaseVisits

  /** Its purpose is to catch the check that a field holds no case of a
    * decoding going back to walking the whole state at every step, which
    * costs the square of the number of calls: one more call adds as many
    * visits after any number of calls as after one.
    */
  stoppableProperty("one more call of a growing state adds as many visits whatever the state's length", fewInputs) { stopped =>
    for count <- Gen.int(Range.linear(1, 48)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      Result.diff(caseWalkVisits(count + 1, stop) - caseWalkVisits(count, stop), caseWalkVisits(2, stop) - caseWalkVisits(1, stop))(_ == _)
  }

  /** A recursion of `count` calls of one method, whose owner is the text. */
  private def repeatedCalls(owner: String, count: Int): String =
    def natural(value: Int): String = if value == 0 then "(λz s. z)" else s"(λz s. s ${natural(value - 1)})"
    val decoded = s"(λon_call on_new on_decode. on_decode ${byteText(7)})"
    val arguments = s"(λh t n c. c h t) $decoded (λn c. n)"
    val expression = s"(λon_call on_new on_decode. on_call (λk. k [\"$owner\", \"echo\", \"(B)V\"]) ($arguments))"
    val step = s"(λk. k (λon_finish on_run. on_run $expression) (λr. self rest))"
    s"((λf. (λx. f (x x)) (λx. f (x x))) (λself n. n ${finishState("λy. y")} (λrest. $step))) ${natural(count)}"

  /** The layers of syntax the JIT reads in one more call, from a run of three
    * calls to a run of six.
    */
  private def readsOfThreeMoreCalls(owner: String, stop: StopSignal): Long =
    def reads(count: Int): Long =
      val run = entry
        .interacted(closed(repeatedCalls(owner, count)), Echoing, ExpansionSource.fresh(), stop)
        .getOrElse(throw IllegalStateException("the fixture entry's executor runs no FFI program"))
      assert(run.finished, s"the run of $count calls did not finish")
      countsAfter(run.entry).syntaxReads
    reads(6) - reads(3)

  /** Its purpose is to catch a run reading a method's symbols again at every
    * call, whose cost grows with the symbols' length.
    */
  stoppableProperty("a further call of a method reads as much whatever the length of its symbols", fewInputs) { stopped =>
    for length <- Gen.int(Range.linear(2, 48)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      Result.diff(readsOfThreeMoreCalls("a" * length, stop), readsOfThreeMoreCalls("a", stop))(_ == _)
  }

  /** Its purpose is to show, for this configuration, the calls a two-step
    * program makes in order, with the values decoded at each.
    */
  stoppableTest("the calls of a two-step program") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    assertSeededSnapshot(byte.flatMap(first => byte.map((first, _))), seed = 1878L, count = 8, "moore/two_step_calls.txt")(
      (first, second) => s"$first $second",
      (found: Vector[String]) => found.mkString("\n")
    ) { (first, second) =>
      val program = callState(first, s"λone. ${callState(second, s"λtwo. ${finishState(s"$pair one two")}")}")
      answers(program, Spelling, stop).toVector.map(ReadableText.printedNameless(_).text).sorted
    }
  }
