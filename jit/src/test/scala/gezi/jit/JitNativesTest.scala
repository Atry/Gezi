package gezi.jit

import gezi.saturation.StopSignal
import gezi.jit.JitTesting.*
import gezi.strategies.BaselineRounds
import gezi.jit.NativesTesting.*
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.Property
import gezi.standardlibrary.SplitMix
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import gezi.strategies.DispatchStrategies
import gezi.strategies.FixpointReport
import gezi.strategies.Round
import gezi.strategies.Schedule
import gezi.strategies.StrategyTesting
import gezi.frontend.Term
import gezi.frontend.Term.choice
import gezi.frontend.Term.λ
import gezi.hotspot.baselines.BaselineCaches
import gezi.saturation.End
import gezi.ir.Instruction

/** A term over the library terms of `JitTesting.libraryTermsFile` and
  * filter_by, as data a test draws and resolves; `term` is the HOAS term it
  * stands for and `text` a description of it for the tests' messages.
  */
enum DrawnTerm:

  /** The library term of the key (`JitTesting.libraryTerm`). */
  case Leaf(key: String)

  /** The closure filter_by (`NativesTesting.filterBy`). */
  case FilterBy
  case Variable(name: String)
  case Lambda(variable: String, body: DrawnTerm)
  case Apply(function: DrawnTerm, argument: DrawnTerm)
  case Parallel(left: DrawnTerm, right: DrawnTerm)
  case Choice(members: Vector[DrawnTerm])

  /** A description of the term in lambdalattice's notation, for messages. */
  def text: String = this match
    case Leaf(key)                 => key
    case FilterBy                  => "filter_by"
    case Variable(name)            => name
    case Lambda(variable, body)    => s"(λ$variable. ${body.text})"
    case Apply(function, argument) => s"(${function.text} ${argument.text})"
    case Parallel(left, right)     => s"(${left.text} ∥ ${right.text})"
    case Choice(members)           => members.reverseIterator.map(_.text).mkString("(", " + ", ")")

  /** The closed HOAS term, each variable the one its abstraction binds.
    * Throws `IllegalArgumentException` for a variable no abstraction binds.
    */
  def term: Term = termUnder(Map.empty)

  private def termUnder(bound: Map[String, Term]): Term = this match
    case Leaf(key)                 => JitTesting.libraryTerm(key)
    case FilterBy                  => NativesTesting.filterBy
    case Variable(name)            => bound.getOrElse(name, throw IllegalArgumentException(s"no abstraction binds $name"))
    case Lambda(variable, body)    => Term.λ(argument => body.termUnder(bound.updated(variable, argument)))
    case Apply(function, argument) => function.termUnder(bound)(argument.termUnder(bound))
    case Parallel(left, right)     => left.termUnder(bound) ∥ right.termUnder(bound)
    case Choice(members)           => Term.choice(members.map(_.termUnder(bound))*)

  /** Each term with every choice replaced by one of its members, the empty
    * choice kept (choice_resolution/2).
    */
  def resolutions: Vector[DrawnTerm] = this match
    case Choice(members) if members.nonEmpty => members.flatMap(_.resolutions)
    case Apply(function, argument) =>
      for
        resolvedFunction <- function.resolutions
        resolvedArgument <- argument.resolutions
      yield Apply(resolvedFunction, resolvedArgument)
    case Lambda(variable, body) => body.resolutions.map(Lambda(variable, _))
    case Parallel(left, right) =>
      for
        resolvedLeft <- left.resolutions
        resolvedRight <- right.resolutions
      yield Parallel(resolvedLeft, resolvedRight)
    case other => Vector(other)

/** The port of `gezi/tests/jit_natives.plt`: the natives of the
  * backend in the JIT, on the native route's library compiled with the
  * backend's knowledge modules (natives on).
  * Each check is one whose failure is a defect by definition; the file
  * comment of the Prolog test says why each holds (THE REFERENCE'S ANSWER,
  * A CHOICE RESOLUTION, THE VOUCHING CHECK, FILTER_BY).
  *
  * The programs are written in the HOAS over the library terms of
  * `JitTesting.libraryTermsFile`, each a member read by projection, so no
  * name is resolved, and filter_by is the closure `NativesTesting.filterBy`.
  * The programs compiled by the native route's schedule
  * (jit_natives.plt's compiled_program/3) are each a fixture as written, as
  * the schedule's output and as the term the backend runs, refined
  * (`compiledFixtures`). The instructions are interned globally, so a reading
  * under another library reads the same compiled term, as the Prolog
  * store's hash consing shared it between the libraries.
  *
  * Every run is bounded by a count of steps (`NativesTesting.normalFormLimit`).
  */
class JitNativesTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of JitNativesTest, "theNativesWriteNoFile", takes 31.246 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: that test starts a child JVM; the other tests of the suite take 8 s at most. FIXME: the other tests exceed the 3 s default with no reason yet. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(50, "s")

  // ---- the library terms ----

  private lazy val zero = libraryTerm("zero")
  private lazy val successor = libraryTerm("successor")
  private lazy val natFold = libraryTerm("nat_fold")
  private lazy val natType = libraryTerm("nat_type")
  private lazy val trueTerm = libraryTerm("true")
  private lazy val falseTerm = libraryTerm("false")
  private lazy val booleanType = libraryTerm("boolean_type")
  private lazy val booleanNot = libraryTerm("boolean_not")
  private lazy val nil = libraryTerm("nil")
  private lazy val cons = libraryTerm("cons")
  private lazy val listType = libraryTerm("list_type")
  private lazy val listFold = libraryTerm("list_fold")
  private lazy val konstant = libraryTerm("konstant")
  private lazy val compose = libraryTerm("compose")
  private lazy val double = libraryTerm("double")
  private lazy val even = libraryTerm("even")

  /** The identity closure. */
  private def identity: Term = λ(argument => argument)

  // ---- the compiled programs ----

  /** A term the tests read: a program in the HOAS over the library terms
    * and filter_by, or an instruction of a compiled program.
    */
  private enum Fixture:
    case Written(program: Term)
    case Interned(instruction: Instruction)

  /** The schedule of the native route whose type check enables the
    * knowledge of `NativeRouteCompilationTest` (the rounds fixture's
    * `prolog_backend_type_check`), each round within 600 instances, the
    * Prolog test's: measured there 2026-10-29, the largest round here, the
    * type check of successor^8 zero, reaches its fixed point at 339, and
    * that of X2 at 313.
    */
  private lazy val nativeRouteSchedule: Vector[Round] =
    BaselineRounds.nativeRouteSchedule(nativesOn, StrategyTesting.round("prolog_backend_type_check"), 600)

  /** The program through the front end, which tags its occurrences, and
    * the native route's schedule, each round reaching its fixed point: the
    * program as written, the last
    * round's output, and the term the backend runs of it under the strategy
    * `fallback` (program_compiled/3).
    */
  private def programCompiled(program: Term, stop: StopSignal): (Instruction, Instruction, Instruction) =
    val input = StrategyTesting.programInput(nativesOn, program)
    val scheduled = Schedule.run(nativesOn.index, Vector(input), nativeRouteSchedule, stop)
    scheduled.records.foreach(record =>
      record.report match
        case FixpointReport(End.FixedPoint(_)) => ()
        case other                            => fail(s"a round of the schedule ended $other")
    )
    val output = scheduled.outputs match
      case Vector(found) => found
      case other         => fail(s"the schedule gave ${other.size} outputs")
    val Dispatched(refined, _, _) = StrategyDispatch.dispatched(
      CompilationStrategy(DispatchStrategies.fallback, nativeRouteSchedule),
      input,
      BackendFacts.of(nativesOn),
      BaselineCaches.provider(),
      stop
    )
    val written = termInstruction(program)
    (written, output, refined)

  private def numeral(size: Int): Term = (1 to size).foldLeft(zero)((value, _) => successor(value))

  private def doubles(count: Int, base: Term): Term = (1 to count).foldLeft(base)((value, _) => double(value))

  /** The programs of compiled_program/3: X2 (`compiled(x2, …)`), a numeral, nested negations, the parity of a double and a
    * list.
    */
  private lazy val compiledPrograms: Vector[(String, Term)] = Vector(
    "x2" -> natFold(zero)(compose(successor)(successor))(numeral(1)),
    "two" -> numeral(2),
    "negations" -> booleanNot(booleanNot(trueTerm)),
    "parity_of_a_double" -> even(doubles(1, numeral(1))),
    "list" -> cons(numeral(1))(nil)
  )

  /** Each program of compiled_program/3 compiled natives on, one after the
    * other: `compiled(Name, Kind)` with its term for each kind, written,
    * output and refined, in that order (compiled_terms/1).
    */
  private lazy val compiledFixtures: Vector[(String, Instruction)] =
    compiledPrograms.flatMap { (name, program) =>
      val (written, output, refined) = programCompiled(program, StopSignal.NeverStopped)
      Vector(s"compiled($name, written)" -> written, s"compiled($name, output)" -> output, s"compiled($name, refined)" -> refined)
    }

  /** The library terms, the natives-on library, the native route's schedule and the compiled programs, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => libraryTerms, _ => nativesOn, _ => nativeRouteSchedule, _ => compiledFixtures)

  /** The plain value of the fixture: a program's library terms kept as
    * references (`JitTesting.termValue`), an instruction as its reference.
    */
  private def fixtureValue(fixture: Fixture): Value = fixture match
    case Fixture.Written(program) => termValue(program)
    case Fixture.Interned(instruction) => instruction

  private lazy val booleanPrograms: Vector[(String, Term)] = Vector(
    "true_alone" -> trueTerm,
    "false_alone" -> falseTerm,
    "true_filtered" -> filterBy(booleanType)(trueTerm),
    "false_filtered" -> filterBy(booleanType)(falseTerm),
    "boolean_filter_over_a_choice" -> filterBy(booleanType)(choice(trueTerm, falseTerm)),
    "boolean_parallel" -> (falseTerm ∥ booleanType),
    "selection_by_true_filtered" -> filterBy(booleanType)(trueTerm)(zero)(successor(zero)),
    "selection_by_false_filtered" -> filterBy(booleanType)(falseTerm)(zero)(successor(zero)),
    "selection_of_filtered_naturals" ->
      filterBy(booleanType)(falseTerm)(filterBy(natType)(zero))(filterBy(natType)(successor(zero))),
    "successor_of_true" -> successor(trueTerm),
    "successor_of_true_filtered" -> successor(filterBy(booleanType)(trueTerm)),
    "successor_of_true_under_nat_filters" -> filterBy(natType)(successor(filterBy(natType)(trueTerm))),
    "true_under_a_nat_filter" -> filterBy(natType)(trueTerm),
    "zero_under_a_boolean_filter" -> filterBy(booleanType)(zero),
    "nat_filtered_zero_under_a_boolean_filter" -> filterBy(booleanType)(filterBy(natType)(zero)),
    "boolean_filtered_true_under_a_nat_filter" -> filterBy(natType)(filterBy(booleanType)(trueTerm)),
    "boolean_filter_under_a_lambda" -> λ(x => (x ∥ booleanType)(zero)(successor(zero)))(falseTerm)
  )

  private lazy val decodePointPrograms: Vector[(String, Term)] = Vector(
    "decode_point_at_the_root" -> ((successor(zero) ∥ natType)(zero)(identity)),
    "decode_point_applied_in_a_code" -> λ(y => (y ∥ natType)(zero)(identity))(successor(zero)),
    "decode_point_by_filter_by" -> λ(y => filterBy(natType)(y)(zero)(identity))(successor(zero))
  )

  private lazy val outputFilterPrograms: Vector[(String, Term)] = Vector(
    "output_filter_on_a_function" -> ((successor ∥ λ(_ => natType))(filterBy(natType)(zero))),
    "output_filter_by_a_constant_closure" ->
      filterBy(λ(kept => λ(_ => kept))(natType))(successor)(filterBy(natType)(zero))
  )

  private lazy val handWrittenPrograms: Vector[(String, Term)] = Vector(
    "zero_filtered" -> filterBy(natType)(zero),
    "two_filtered" -> filterBy(natType)(successor(successor(zero))),
    "filter_over_a_filter" -> filterBy(natType)(filterBy(natType)(successor(zero))),
    "filter_over_a_choice" -> filterBy(natType)(choice(zero, successor(zero))),
    "parallel_under_successors" -> successor(successor(successor(zero) ∥ natType)),
    "filter_under_a_lambda" -> λ(x => successor(x ∥ natType))(successor(zero)),
    "fold_over_a_filter" ->
      natFold(zero)(compose(successor)(successor))(filterBy(natType)(successor(successor(zero))))
  ) ++ booleanPrograms ++ decodePointPrograms ++ outputFilterPrograms

  private lazy val nonNumberPrograms: Vector[(String, Term)] = Vector(
    "list_filtered" -> filterBy(natType)(cons(zero)(nil)),
    "identity_filtered" -> filterBy(natType)(identity),
    "list_filtered_under_a_lambda" ->
      λ(x => natFold(zero)(konstant(zero))(successor(x ∥ natType)))(cons(zero)(nil)),
    "false_filtered" -> filterBy(natType)(falseTerm),
    "boolean_filtered_false_under_a_nat_filter" -> filterBy(natType)(filterBy(booleanType)(falseTerm)),
    "one_filtered_as_a_boolean" -> filterBy(booleanType)(successor(zero)),
    "list_filtered_as_a_boolean" -> filterBy(booleanType)(cons(zero)(nil)),
    "identity_filtered_as_a_boolean" -> filterBy(booleanType)(identity)
  )

  /** Every fixture, the compiled programs' terms first, then the terms
    * written by hand (fixture_terms/1).
    */
  private def fixtures: Vector[(String, Fixture)] =
    compiledFixtures.map((name, instruction) => name -> Fixture.Interned(instruction)) ++
      handWrittenPrograms.map((name, program) => name -> Fixture.Written(program))

  /** The normal forms the JIT reads of the fixture under the library, from
    * a fresh state, and the spending.
    */
  private def fixtureRead(library: StandardLibrary, fixture: Fixture, budget: Int = JitConfiguration.defaultBudget): Spent[Vector[Instruction]] =
    val value = fixtureValue(fixture)
    normalFormsSpent(Mode.Jit(Jit(configurationOf(library, budget))), value, normalFormLimit)

  /** The normal forms the JIT reads of the program under the library. */
  private def jitRead(library: StandardLibrary, program: Term, budget: Int = JitConfiguration.defaultBudget): Spent[Vector[Instruction]] =
    fixtureRead(library, Fixture.Written(program), budget)

  /** The normal forms the reference reads of the program. */
  private def referenceRead(program: Term): Spent[Vector[Instruction]] =
    normalFormsSpent(Mode.TablingWeakHead, termValue(program), normalFormLimit)

  /** The JIT, natives on, reads its normal forms within its count, and the
    * reference's read-out by membership confirms each (answers_confirmed/3).
    */
  private def answersConfirmed(name: String, fixture: Fixture): Int =
    val read = fixtureRead(nativesOn, fixture)
    val normalForms = read.outcome match
      case Bounded.Finished(found) => found
      case other                   => fail(s"$name: the JIT did not finish: $other")
    val value = fixtureValue(fixture)
    normalForms.foreach(normalForm =>
      assertEquals(referenceReads(value, normalForm, confirmationLimit), Confirmation.Confirmed, name)
    )
    normalForms.size

  test("theJitWithNativesReadsOnlyAnswersOfTheReference") {
    val counts = fixtures.map((name, fixture) => name -> answersConfirmed(name, fixture))
    println(s"normal forms confirmed: $counts")
    assertEquals(counts.map(_._1), fixtures.map(_._1))
  }

  // ---- random terms ----

  /** A random generator's state: the random bits and the count of variables
    * named so far.
    */
  private final case class Drawing(random: SplitMix, variables: Int):
    def between(low: Int, high: Int): (Int, Drawing) =
      val (drawn, after) = random.between(low, high)
      (drawn, copy(random = after))
    def variable: (String, Drawing) = (s"V$variables", copy(variables = variables + 1))

  private def applied(function: DrawnTerm, arguments: DrawnTerm*): DrawnTerm =
    arguments.foldLeft(function)(DrawnTerm.Apply(_, _))

  private def leafApplied(key: String, arguments: DrawnTerm*): DrawnTerm = applied(DrawnTerm.Leaf(key), arguments*)

  private def filteredBy(criterion: String, operand: DrawnTerm): DrawnTerm =
    applied(DrawnTerm.FilterBy, DrawnTerm.Leaf(criterion), operand)

  private def successorOfFiltered(argument: DrawnTerm, drawing: Drawing): (DrawnTerm, Drawing) =
    val (name, after) = drawing.variable
    (
      DrawnTerm.Apply(
        DrawnTerm.Lambda(name, leafApplied("successor", DrawnTerm.Parallel(DrawnTerm.Variable(name), DrawnTerm.Leaf("nat_type")))),
        argument
      ),
      after
    )

  /** A random closed term of about the size over the naturals
    * (random_natural_surface/2), or with the booleans mixed in
    * (random_mixed_surface/2).
    */
  private def randomTerm(size: Int, mixed: Boolean, drawing: Drawing): (DrawnTerm, Drawing) =
    if size <= 1 then
      if mixed then
        val (leaf, after) = drawing.between(1, 3)
        (DrawnTerm.Leaf(Vector("zero", "true", "false")(leaf - 1)), after)
      else (DrawnTerm.Leaf("zero"), drawing)
    else
      val (kind, afterKind) = drawing.between(1, if mixed then 13 else 8)
      val smaller = size - 1
      def one(build: DrawnTerm => DrawnTerm): (DrawnTerm, Drawing) =
        val (argument, after) = randomTerm(smaller, mixed, afterKind)
        (build(argument), after)
      kind match
        case 1 => (DrawnTerm.Leaf("zero"), afterKind)
        case 2 => one(leafApplied("successor", _))
        case 3 => one(filteredBy("nat_type", _))
        case 4 => one(DrawnTerm.Parallel(_, DrawnTerm.Leaf("nat_type")))
        case 5 =>
          val half = 1.max(smaller / 2)
          val (left, afterLeft) = randomTerm(half, mixed, afterKind)
          val (right, afterRight) = randomTerm(half, mixed, afterLeft)
          (DrawnTerm.Choice(Vector(left, right)), afterRight)
        case 6 =>
          val half = 1.max(smaller / 2)
          val (zeroCase, afterZero) = randomTerm(half, mixed, afterKind)
          val (argument, afterArgument) = randomTerm(half, mixed, afterZero)
          (
            leafApplied("nat_fold", zeroCase, leafApplied("compose", DrawnTerm.Leaf("successor"), DrawnTerm.Leaf("successor")), argument),
            afterArgument
          )
        case 7 =>
          val (argument, after) = randomTerm(smaller, mixed, afterKind)
          successorOfFiltered(argument, after)
        case 8  => one(argument => leafApplied("successor", leafApplied("successor", argument)))
        case 9  => (DrawnTerm.Leaf("true"), afterKind)
        case 10 => (DrawnTerm.Leaf("false"), afterKind)
        case 11 => one(filteredBy("boolean_type", _))
        case 12 => one(DrawnTerm.Parallel(_, DrawnTerm.Leaf("boolean_type")))
        case _ =>
          val third = 1.max(smaller / 3)
          val (selector, afterSelector) = randomTerm(third, mixed, afterKind)
          val (left, afterLeft) = randomTerm(third, mixed, afterSelector)
          val (right, afterRight) = randomTerm(third, mixed, afterLeft)
          (DrawnTerm.Apply(DrawnTerm.Apply(selector, left), right), afterRight)

  /** 100 random terms over the naturals of about 12 nodes, then 100 mixed
    * with the booleans of about 10, from fixed seeds (random_surfaces/1).
    */
  lazy val randomTerms: Vector[DrawnTerm] =
    def drawn(count: Int, seed: Long, size: Int, mixed: Boolean): Vector[DrawnTerm] =
      (0 until count).foldLeft((Vector.empty[DrawnTerm], Drawing(SplitMix(seed), 0))) { case ((found, drawing), _) =>
        val (drawnTerm, after) = randomTerm(size, mixed, drawing)
        (found :+ drawnTerm, after)
      }._1
    drawn(100, 20261015, 12, mixed = false) ++ drawn(100, 20261012, 10, mixed = true)

  /** The reference confirms the normal form of the drawn term, directly or
    * on a choice resolution when the direct read-out runs out of its count
    * (reference_confirms_within/4).
    */
  private def referenceConfirms(drawnTerm: DrawnTerm, normalForm: Instruction): String =
    val value = termValue(drawnTerm.term)
    referenceReads(value, normalForm, confirmationLimit) match
      case Confirmation.Confirmed => "confirmed"
      case Confirmation.NotRead   => "not_read"
      case Confirmation.Exceeded =>
        val resolved = drawnTerm.resolutions.exists(resolution =>
          val resolvedValue = termValue(resolution.term)
          referenceReads(resolvedValue, normalForm, confirmationLimit) == Confirmation.Confirmed
        )
        if resolved then "confirmed_by_resolution" else "exceeded"

  test("theJitWithNativesReadsOnlyAnswersOfTheReferenceOnRandomTerms") {
    val verdicts = randomTerms.map(drawnTerm =>
      jitRead(nativesOn, drawnTerm.term).outcome match
        case Bounded.Finished(normalForms) =>
          val outcomes = normalForms.map(referenceConfirms(drawnTerm, _))
          outcomes.foreach(outcome =>
            assert(Set("confirmed", "confirmed_by_resolution").contains(outcome), s"${drawnTerm.text}: $outcome")
          )
          if outcomes.contains("confirmed_by_resolution") then s"resolved(${normalForms.size})"
          else s"confirmed(${normalForms.size})"
        case _ => "unfinished"
    )
    println(s"random terms: ${EvaluatorTesting.clumpedCounts(verdicts)}")
  }

  /** The JIT's heads of the fixture are the reference's, tabling(weak_head)'s,
    * both within `headsLimit` steps (heads_agree/2); the heads are compared
    * by spelling.
    */
  /** The steps a heads reading of this suite may take. MEASURED 2026-11-12
    * (fbf5e019d, the suite's 504 heads readings): at
    * most 142,880 steps; the Prolog tests read within 1,000,000 inferences.
    */
  private val headsLimit: Long = 150000

  /** The steps the first head of a fallback program may take. MEASURED
    * 2026-11-12: 11 steps for every program, with room for a program a few
    * times larger.
    */
  private val firstHeadLimit: Long = 1000

  private def fixtureHeadsAgree(library: StandardLibrary, name: String, fixture: Fixture): Unit =
    val value = fixtureValue(fixture)
    val reference = headsRead(Mode.TablingWeakHead, value, headsLimit).outcome
    val read = headsRead(Mode.Jit(Jit(configurationOf(library))), value, headsLimit)
    assert(reference.finished, s"$name: the reference did not finish")
    assertEquals(read.outcome, reference, name)

  /** The JIT's heads of the program are the reference's. */
  private def headsAgree(library: StandardLibrary, name: String, program: Term): Unit =
    fixtureHeadsAgree(library, name, Fixture.Written(program))

  /** The non-number program whose decode point stands under successor, a
    * field the term never reads.
    */
  private val decodePointUnderAConstructor = "list_filtered_under_a_lambda"

  // Natives on, a filter on a value that is no natural decodes into nothing.
  test("aFilterOnANonNumberGivesNoAnswerWithNatives") {
    nonNumberPrograms.filterNot(_._1 == decodePointUnderAConstructor).foreach((name, program) =>
      assertEquals(jitRead(nativesOn, program).outcome, Bounded.Finished(Vector.empty), name)
    )
  }

  // Natives on, a decode point under successor, which the reference never
  // reads, is not forced, since a constructor is not strict in its field
  // (`Jit.nativeAppliedHeads`), so the JIT reads the reference's answer.
  test("aDecodePointUnderAConstructorIsNotForcedWithNatives") {
    val dropped = natFold(zero)(konstant(zero))(successor(cons(zero)(nil) ∥ natType))
    val zeroNormalForm = referenceRead(zero).outcome match
      case Bounded.Finished(Vector(found)) => found
      case other                           => fail(s"zero: $other")
    nonNumberPrograms.filter(_._1 == decodePointUnderAConstructor).foreach((name, program) =>
      assertEquals(jitRead(nativesOn, program).outcome, Bounded.Finished(Vector(zeroNormalForm)), name)
    )
    assertEquals(jitRead(nativesOn, dropped).outcome, Bounded.Finished(Vector(zeroNormalForm)))
    val reference = referenceRead(dropped).outcome
    assertEquals(reference, Bounded.Finished(Vector(zeroNormalForm)))
  }

  /** The fallback points of fallback_surface/3: the term and the term the
    * reference reads in its place.
    */
  private lazy val fallbackPrograms: Vector[(String, Term, Term)] = Vector(
    ("typed_numeral", choice(successor(zero ∥ natType), successor(zero ∥ natType) ∥ natType), successor(zero)),
    (
      "untyped_numeral",
      choice(successor(successor(zero)), successor(successor(zero)) ∥ natType),
      successor(successor(zero))
    ),
    ("list", choice(cons(zero)(nil), cons(zero)(nil) ∥ natType), cons(zero)(nil)),
    (
      "successor_of_an_untyped_numeral",
      successor(choice(successor(zero), successor(zero) ∥ natType)),
      successor(successor(zero))
    ),
    ("successor_of_a_list", successor(choice(cons(zero)(nil), cons(zero)(nil) ∥ natType)), successor(cons(zero)(nil))),
    ("closure_body", λ(y => choice(y, y ∥ natType))(successor(zero)), successor(zero)),
    ("identity_of_zero", choice(identity(zero), identity(zero) ∥ natType), identity(zero)),
    ("identity_of_true", choice(identity(trueTerm), identity(trueTerm) ∥ booleanType), identity(trueTerm)),
    ("identity_of_false", choice(identity(falseTerm), identity(falseTerm) ∥ booleanType), identity(falseTerm)),
    (
      "natural_point_inside_a_boolean_point",
      choice(choice(zero, zero ∥ natType), choice(zero, zero ∥ natType) ∥ booleanType),
      zero
    ),
    (
      "boolean_point_inside_a_natural_point",
      choice(choice(trueTerm, trueTerm ∥ booleanType), choice(trueTerm, trueTerm ∥ booleanType) ∥ natType),
      trueTerm
    ),
    (
      "false_through_a_natural_point",
      choice(choice(falseTerm, falseTerm ∥ natType), choice(falseTerm, falseTerm ∥ natType) ∥ booleanType),
      falseTerm
    ),
    ("item_outside_the_element", cons(choice(identity, identity ∥ natType))(nil ∥ listType(natType)), cons(identity)(nil)),
    ("item_inside_the_element", cons(choice(zero, zero ∥ natType))(nil ∥ listType(natType)), cons(zero)(nil)),
    (
      "choice_of_zero_and_an_untyped_numeral",
      choice(choice(identity(zero), successor(zero)), choice(identity(zero), successor(zero)) ∥ natType),
      choice(identity(zero), successor(zero))
    ),
    (
      "choice_of_a_typed_and_an_untyped_numeral",
      choice(
        choice(successor(zero ∥ natType), successor(successor(zero))),
        choice(successor(zero ∥ natType), successor(successor(zero))) ∥ natType
      ),
      choice(successor(zero), successor(successor(zero)))
    )
  )

  private lazy val twoSlotPrograms: Vector[(String, Term)] = Vector(
    "two_slots_of_a_numeral" -> λ(x => λ(y => choice(x, y ∥ natType)))(successor(zero))(successor(zero)),
    "two_slots_of_a_choice" ->
      λ(x => λ(y => choice(x, y ∥ natType)))(choice(successor(zero), cons(zero)(nil)))(choice(successor(zero), cons(zero)(nil)))
  )

  private val expectedConstantHeads: Vector[(String, JitHead)] = Vector(
    "identity_of_zero" -> JitHead.Represented(Representation.BigInteger, NativeValue.Natural(0)),
    "identity_of_true" -> JitHead.Represented(Representation.Truth, NativeValue.Truth(true)),
    "identity_of_false" -> JitHead.Represented(Representation.Truth, NativeValue.Truth(false)),
    "natural_point_inside_a_boolean_point" -> JitHead.Represented(Representation.Truth, NativeValue.Truth(true)),
    "boolean_point_inside_a_natural_point" -> JitHead.Represented(Representation.BigInteger, NativeValue.Natural(0)),
    "false_through_a_natural_point" -> JitHead.Represented(Representation.Truth, NativeValue.Truth(false))
  )

  private def fallback(name: String): Term =
    fallbackPrograms.find(_._1 == name).map(_._2).getOrElse(throw IllegalArgumentException(s"no fallback point $name"))

  /** The first head the JIT gives of the program. */
  private def firstHead(program: Term): JitHead =
    val value = termValue(program)
    JitRules(configurationOf(nativesOn)).heads(JitValues.fromValue(value)).pull.result(ReadingState.fresh(firstHeadLimit)) match
      case gezi.weakhead.Computed.Done(Some((head, _)), _) => head
      case other => fail(s"no first head: $other")

  test("aFallbackPointReadsItsOperandTypedInItsDomainAndUntypedOutside") {
    fallbackPrograms.foreach((name, program, plain) =>
      val reference = referenceRead(plain).outcome
      assert(reference match
        case Bounded.Finished(found) => found.nonEmpty
        case _                       => false, s"$name: $reference")
      val read = jitRead(nativesOn, program)
      assertEquals(read.outcome, reference, name)
      assertEquals(counts(read.jitState).decodings, 0L, name)
    )
    assert(counts(jitRead(nativesOn, fallback("typed_numeral")).jitState).nativeCalls > 0)
    expectedConstantHeads.foreach((name, expected) => assertEquals(firstHead(fallback(name)), expected, name))
    assertEquals(counts(jitRead(nativesOn, fallback("successor_of_an_untyped_numeral")).jitState).callsOf(successorNative), 0L)
    Vector("item_inside_the_element" -> 1L, "item_outside_the_element" -> 0L).foreach((name, calls) =>
      assertEquals(counts(jitRead(nativesOn, fallback(name)).jitState).callsOf(consNative), calls, name)
    )
  }

  /** The normal-form readings of the fixtures under the JIT with the
    * budget, natives on, the state kept from one to the next or dropped
    * before each (budget_readings/4).
    */
  private def budgetReadings(
      fixtures: Vector[Fixture],
      budget: Int,
      dropped: Boolean
  ): Vector[Bounded[Vector[Instruction]]] =
    val values = fixtures.map(fixtureValue)
    val jit = Jit(configurationOf(nativesOn, budget))
    values
      .foldLeft((Vector.empty[Bounded[Vector[Instruction]]], NoJitState: JitState)) { case ((readings, state), value) =>
        val read = normalFormsSpent(Mode.Jit(jit), value, normalFormLimit, if dropped then NoJitState else state)
        (readings :+ read.outcome, read.jitState)
      }
      ._1

  test("aFallbackPointReadsAlikeCompiledAndInterpreted") {
    val programs = (fallbackPrograms.map(_._2) ++ twoSlotPrograms.map(_._2)).map(Fixture.Written(_))
    val large = budgetReadings(programs, 10000, dropped = false)
    assertEquals(budgetReadings(programs, 0, dropped = false), large)
    assertEquals(budgetReadings(programs, 3, dropped = true), large)
  }

  private lazy val mixedPoint: Term =
    choice(choice(identity(zero), successor(zero)), choice(identity(zero), successor(zero)) ∥ natType)
  private lazy val mixedPlain: Term = choice(identity(zero), successor(zero))

  private lazy val decodedPointPrograms: Vector[(String, Term, Term)] = Vector(
    ("successor_of_a_mixed_point", successor(mixedPoint) ∥ natType, successor(mixedPlain)),
    (
      "successor_of_an_untyped_point",
      successor(choice(successor(zero), successor(zero) ∥ natType)) ∥ natType,
      successor(successor(zero))
    ),
    (
      "successor_of_a_typed_and_untyped_point",
      successor(
        choice(
          choice(successor(zero ∥ natType), successor(successor(zero))),
          choice(successor(zero ∥ natType), successor(successor(zero))) ∥ natType
        )
      ) ∥ natType,
      successor(choice(successor(zero), successor(successor(zero))))
    ),
    ("filter_by_over_a_mixed_point", filterBy(natType)(successor(mixedPoint)), successor(mixedPlain)),
    ("two_successors_over_a_mixed_point", successor(successor(mixedPoint)) ∥ natType, successor(successor(mixedPlain))),
    (
      "cell_over_a_mixed_point",
      cons(mixedPoint)(nil ∥ listType(natType)) ∥ listType(natType),
      cons(mixedPlain)(nil)
    )
  )

  test("aDecodePointDecodesAFallbackPointThatTakesTheUntypedPath") {
    decodedPointPrograms.foreach((name, program, plain) =>
      val reference = referenceRead(plain).outcome
      assert(reference match
        case Bounded.Finished(found) => found.nonEmpty
        case _                       => false, s"$name: $reference")
      assertEquals(jitRead(nativesOn, program).outcome, reference, name)
    )
  }

  /** The cost of a unit of each step of a family is linear: the steps a
    * unit adds over the larger span are at most a quarter more than over the
    * smaller (the cost checks of jit_natives.plt, which measured
    * inferences).
    */
  private def costsLinear(costs: Vector[(Int, Long)]): Boolean = costs match
    case Vector((small, smallCost), (middle, middleCost), (large, largeCost)) =>
      (largeCost - middleCost).toDouble / (large - middle) <= 1.25 * (middleCost - smallCost).toDouble / (middle - small)
    case other => throw IllegalArgumentException(s"three sizes are measured, not ${other.size}")

  /** The work of the JIT's reading of the program, which must finish with
    * one normal form: its steps and its reads of syntax
    * (`JitCounts.syntaxReads`), which together stand in for the inferences
    * the Prolog test measured. The checks of decode points read the syntax
    * of a chain without a step, so steps alone cannot see a chain walked
    * again.
    */
  private def workOf(program: Term): Long =
    val read = jitRead(nativesOn, program)
    assert(read.outcome match
      case Bounded.Finished(Vector(_)) => true
      case _                           => false, s"${read.outcome}")
    read.steps + counts(read.jitState).syntaxReads

  test("aListsTailIsKeptAsWrittenAndFilteredOnce") {
    val one = successor(zero)
    val lists = listType(natType)
    val list = cons(choice(one, one ∥ natType))(cons(choice(falseTerm, falseTerm ∥ natType))(choice(nil, nil ∥ lists)))
    val tailsHead: Term = λ(_ => λ(tail => tail(zero)(λ(item => λ(_ => item)))))
    val lazyTail = choice(list, list ∥ lists)(zero)(tailsHead)
    val lazyTailPlain = cons(one)(cons(falseTerm)(nil))(zero)(tailsHead)
    val reference = referenceRead(lazyTailPlain).outcome
    assert(reference match
      case Bounded.Finished(Vector(_)) => true
      case _                           => false, s"$reference")
    assertEquals(jitRead(nativesOn, lazyTail).outcome, reference)
    def doublesFiltered(power: Int): Term =
      if power == 0 then successor(zero) ∥ natType else double(doublesFiltered(power - 1))
    val accumulatedKept: Term = λ(_ => λ(accumulated => accumulated))
    def filteredFold(power: Int): Term =
      listFold(zero)(accumulatedKept)(natFold(nil ∥ lists)(λ(rest => cons(zero ∥ natType)(rest ∥ lists)))(doublesFiltered(power)))
    val foldCosts = Vector(6, 7, 8).map(power => (1 << power) -> workOf(filteredFold(power)))
    println(s"the filtered fold's steps and reads of syntax by cells: $foldCosts")
    assert(costsLinear(foldCosts), s"$foldCosts")
    // The chain is read once, at its decode point, by reads of its syntax,
    // which take no step: the work of reading its head or the whole list,
    // steps and reads of syntax, is linear in its conses. Kept unread, each
    // tail a decode point over the rest, the rest of the chain would be read
    // again at each cell, and the reads of syntax would grow quadratically.
    def filteredChain(count: Int): Term =
      (1 to count).foldLeft(nil ∥ lists)((chain, _) => cons(zero ∥ natType)(chain))
    Vector("head" -> λ(head => λ(_ => head)), "whole" -> accumulatedKept).foreach((reading, step) =>
      val chainCosts = Vector(250, 500, 1000).map(count => count -> workOf(listFold(zero)(step)(filteredChain(count) ∥ lists)))
      println(s"the filtered chain's steps and reads of syntax by conses, read $reading: $chainCosts")
      assert(costsLinear(chainCosts), s"$reading: $chainCosts")
    )
  }

  /** Depth levels of successor over fallback points in the shape the
    * refinement writes, built in the IR with each level shared, and the IR of
    * successor^depth (cons zero nil) (nested_fallback_term/3).
    */
  private def nestedFallbackTerm(depth: Int): (Value, Instruction) =
    val successorInstruction = libraryInstruction("successor")
    val natTypeInstruction = libraryInstruction("nat_type")
    val base = termInstruction(cons(zero)(nil))
    val term = (1 to depth).foldLeft(base) { (inner, _) =>
      val filteredInner = Instruction.Parallel(inner, natTypeInstruction)
      val point = Instruction.Choice(inner, filteredInner)
      val application = Instruction.Apply(successorInstruction, point)
      val filteredApplication = Instruction.Parallel(application, natTypeInstruction)
      Instruction.Choice(application, filteredApplication)
    }
    val plain = termInstruction((1 to depth).foldLeft(cons(zero)(nil))((program, _) => successor(program)))
    (term, plain)

  test("nestedFallbackPointsAreReadOnce") {
    val jit = Jit(configurationOf(nativesOn))
    val costs = Vector(8, 16, 32).map(depth =>
      val (nestedValue, plain) = nestedFallbackTerm(depth)
      val plainValue = instructionValue(plain)
      val reference = normalFormsSpent(Mode.TablingWeakHead, plainValue, normalFormLimit).outcome
      val read = normalFormsSpent(Mode.Jit(jit), nestedValue, normalFormLimit)
      assertEquals(read.outcome, reference, s"depth $depth")
      depth -> read.steps
    )
    println(s"nested fallback points' steps by depth: $costs")
    val Vector((_, small), (_, middle), (_, large)) = costs: @unchecked
    assert((large - middle).toDouble / 16 <= (middle - small).toDouble / 8, s"$costs")
  }

  /** The normal forms the JIT reads of the value under the library, from a
    * fresh state, and the costs the reading counted: its native calls,
    * decodings and encodings (counted_reading/5).
    */
  private def countedReading(library: StandardLibrary, value: Value): (Bounded[Vector[Instruction]], JitCounts) =
    val read = normalFormsSpent(Mode.Jit(Jit(configurationOf(library))), value, normalFormLimit)
    (read.outcome, counts(read.jitState))

  /** The instruction of the compiled fixture of the name. */
  private def compiledInstruction(name: String): Instruction =
    compiledFixtures.find(_._1 == name).map(_._2).getOrElse(fail(s"no compiled fixture $name"))

  // Natives on, reading the compiled X2, refined, calls the natives; X2 as
  // written writes no filter, and calls no native and decodes nothing,
  // though its zero and successor are bound to natives: an untyped Scott
  // constructor is evaluated by its library term: the backend accepts only a
  // type-filtered constructor, never an untyped Scott constructor. The counts are printed, a reading.
  test("theNativesAreCalled") {
    val refined = Fixture.Interned(compiledInstruction("compiled(x2, refined)"))
    val written = Fixture.Interned(compiledInstruction("compiled(x2, written)"))
    def counted(library: StandardLibrary, fixture: Fixture): JitCounts =
      val value = fixtureValue(fixture)
      val (reading, found) = countedReading(library, value)
      assert(reading.finished, s"$fixture: $reading")
      found
    val refinedCounts = counted(nativesOn, refined)
    val writtenCounts = counted(nativesOn, written)
    println(
      s"X2 compiled: ${refinedCounts.nativeCalls} native calls, ${refinedCounts.decodings} decodings; " +
        s"X2 as written: ${writtenCounts.nativeCalls} native calls, ${writtenCounts.decodings} decodings"
    )
    assert(refinedCounts.nativeCalls > 0)
    assertEquals((writtenCounts.nativeCalls, writtenCounts.decodings), (0L, 0L))
  }

  // Natives on, a typed run computes in the representation and encodes only
  // at its end, with no encoding or decoding midway: the
  // compiled successor^8 zero builds its natural by big_integer's
  // constructor 0 (zero) and seven calls of its constructor 1 (successor)
  // and encodes the eight layers under its root,
  // the root's successor taking its library term's head since its operand is a
  // decode point not yet represented (a constructor is not strict in its
  // field, `Jit.nativeAppliedHeads`),
  // and the compiled even (double (double (successor zero))) builds its
  // literal, calls natural_double twice and natural_even once, and encodes
  // one layer, its boolean answer. Neither decodes, and the reference's
  // read-out by membership confirms their normal forms.
  stoppableTest("aTypedRunEncodesOnlyAtItsEnd") { stopped =>
    Vector(
      (numeral(8), Map(zeroNative -> 1L, successorNative -> 7L), 8L),
      (
        even(doubles(2, numeral(1))),
        Map(
          zeroNative -> 1L,
          successorNative -> 1L,
          NativeName.Function("natural_double") -> 2L,
          NativeName.Function("natural_even") -> 1L
        ),
        1L
      )
    ).foreach { (program, natives, layers) =>
      val (_, _, refined) = programCompiled(program, StopSignal.completedWith(stopped))
      val (reading, counted) = countedReading(nativesOn, refined)
      val normalForms = reading match
        case Bounded.Finished(found @ Vector(_)) => found
        case other                               => fail(s"not one normal form: $other")
      normalForms.foreach(normalForm =>
        assertEquals(referenceReads(refined, normalForm, confirmationLimit), Confirmation.Confirmed)
      )
      assertEquals(counted.callsByNative.filter(_._2 > 0), natives)
      assertEquals(counted.decodings, 0L)
      assertEquals(counted.encodings, layers)
    }
  }

  // Natives on, untyped true and false, and successor applied to untyped
  // true, call no native and decode nothing; true and false under a
  // boolean_type filter call a native or decode.
  test("onlyFilteredBooleansReachTheNatives") {
    def programOf(name: String): Term =
      booleanPrograms.find(_._1 == name).map(_._2).getOrElse(throw IllegalArgumentException(s"no boolean program $name"))
    Vector("true_alone", "false_alone", "successor_of_true").foreach(name =>
      val read = jitRead(nativesOn, programOf(name))
      assert(read.outcome.finished, name)
      assertEquals((counts(read.jitState).nativeCalls, counts(read.jitState).decodings), (0L, 0L), name)
    )
    Vector("true_filtered", "false_filtered").foreach(name =>
      val read = jitRead(nativesOn, programOf(name))
      assert(read.outcome.finished, name)
      assert(counts(read.jitState).nativeCalls + counts(read.jitState).decodings > 0, name)
    )
  }

  /** The one normal form the reference reads of the program: the reading
    * must finish with exactly one (jit_natives.plt:1295 and :1306,
    * `finished([NormalForm])`).
    */
  private def referenceNormalForm(program: Term): Instruction =
    referenceRead(program).outcome match
      case Bounded.Finished(Vector(normalForm)) => normalForm
      case other                                => fail(s"the reference did not finish with one normal form: $other")

  test("aDecodePointReadsTheSameAnswersWhereverItStands") {
    val zeroNormalForm = referenceNormalForm(zero)
    decodePointPrograms.foreach((name, program) =>
      assertEquals(jitRead(nativesOn, program).outcome, Bounded.Finished(Vector(zeroNormalForm)), name)
    )
  }

  test("anOutputFilterOnAFunctionIsADecodePoint") {
    val oneNormalForm = referenceNormalForm(successor(zero))
    outputFilterPrograms.foreach((name, program) =>
      val read = jitRead(nativesOn, program)
      assertEquals(read.outcome, Bounded.Finished(Vector(oneNormalForm)), name)
      assert(counts(read.jitState).nativeCalls + counts(read.jitState).decodings > 0, name)
    )
  }

  test("theAnswersWithNativesDoNotDependOnTheBudget") {
    val named = fixtures ++
      nonNumberPrograms.map((name, program) => name -> Fixture.Written(program)) ++
      randomTerms.map(drawnTerm => drawnTerm.text -> Fixture.Written(drawnTerm.term))
    val terms = named.map(_._2)
    val large = budgetReadings(terms, 10000, dropped = false)
    val none = budgetReadings(terms, 0, dropped = false)
    val small = budgetReadings(terms, 3, dropped = true)
    named.indices.foreach(index =>
      assertEquals(none(index), large(index), named(index)._1)
      assertEquals(small(index), large(index), named(index)._1)
    )
  }

  /** The library term of the key, the member of its own file
    * `<directory>/<key>` of the fixture of `tests/standard_library_fixtures`
    * read by projection (`StandardLibrary.entryMember`), as a closed HOAS
    * term: the instruction the fixture's knowledge names, with no table from
    * paths to terms.
    */
  private def fixtureTerm(fixture: String, directory: String, key: String): Term =
    val root = LibraryFiles.fixture(fixture)
    Term.closed(StandardLibrary.entryMember(root, root.resolve(s"$directory/$key.lambdalattice"), Expansions.none)._1)

  // The set of another backend leaves the JIT answering the reference's
  // heads: the native is not the JIT's and the parallel is no decode point.
  test("anotherBackendsSetLeavesTheJitAnsweringTheReference") {
    val library = LibraryFiles.compiled("tests/standard_library_fixtures/other_backend/compiler/other_backend_set.lambdalattice", Vector(BackendChecks))
    val otherSuccessor = fixtureTerm("other_backend", "library/other_backend_set", "successor")
    val boundedType = fixtureTerm("other_backend", "library/other_backend_set", "bounded_type")
    headsAgree(library, "native_of_another_backend", otherSuccessor(identity))
    headsAgree(library, "representation_of_another_backend", otherSuccessor(identity) ∥ boundedType)
    val value = termValue(otherSuccessor(identity) ∥ boundedType)
    val read = headsRead(Mode.Jit(Jit(configurationOf(library))), value, headsLimit)
    assert(read.outcome.finished)
    assertEquals((counts(read.jitState).nativeCalls, counts(read.jitState).decodings), (0L, 0L))
  }

  /** The vouching check of a native specialization of the representation on
    * the library term (specialization_vouched/3): for every value the check draws,
    * the reference reads one normal form of the value and, of the value
    * filtered by the criterion, by membership, exactly it. The first value
    * that fails, with its key and the two readings, or none.
    */
  private def specializationVouched(library: StandardLibrary, family: String, criterion: Instruction): Option[(Int, Bounded[Vector[Instruction]], Bounded[Vector[Instruction]])] =
    val facts = BackendFacts.of(library)
    val zeroInstruction = facts.zero
    val filter =
      if family == "list" then Instruction.Apply(criterion, libraryInstruction("nat_type"))
      else criterion
    val values: Vector[(Int, Instruction)] = family match
      case "big_integer" =>
        (0 to 100).toVector.map(natural =>
          natural -> (0 until natural).foldLeft(zeroInstruction: Instruction)((term, _) => Instruction.Apply(facts.successor, term))
        )
      case "boolean" => Vector(1 -> facts.trueDefine, 0 -> facts.falseDefine)
      case "list" =>
        (0 to 6).toVector.map(length =>
          length -> (0 until length).foldLeft(facts.nil: Instruction)((tail, _) =>
            Instruction.Apply(Instruction.Apply(facts.cons, zeroInstruction), tail)
          )
        )
      case other => fail(s"no codec: $other")
    values.view.flatMap((key, value) =>
      val plainValue = instructionValue(value)
      val filteredValue = instructionValue(Instruction.Parallel(value, filter))
      val valueReading = normalFormsSpent(Mode.TablingWeakHead, plainValue, normalFormLimit).outcome
      val parallelReading = membershipNormalForms(filteredValue, normalFormLimit)
      (valueReading, parallelReading) match
        case (Bounded.Finished(Vector(normalForm)), Bounded.Finished(Vector(found))) if found == normalForm => None
        case _ => Some((key, valueReading, parallelReading))
    ).headOption

  test("theShippedNativeSpecializationsAreVouchedFor") {
    val declarations = nativesOn.index.combinatorProperties.collect {
      case gezi.standardlibrary.CombinatorProperty(instruction, Property.NativeSpecialization(family)) => (instruction, family)
    }
    assert(declarations.contains((libraryInstruction("nat_type"), "big_integer")))
    assert(declarations.contains((libraryInstruction("boolean_type"), "boolean")))
    assert(declarations.contains((libraryInstruction("list_type"), "list")))
    declarations.foreach((criterion, family) =>
      assertEquals(specializationVouched(nativesOn, family, criterion), None, s"$family on $criterion")
    )
  }

  // In the fixture wrong_declaration, two_naturals = zero + successor zero is
  // declared native_specialization(big_integer); the check passes k = 0 and
  // k = 1 and fails at k = 2.
  test("theVouchingCheckRejectsAWrongNativeSpecialization") {
    val library = LibraryFiles.compiled("tests/standard_library_fixtures/wrong_declaration/compiler/two_naturals_backend.lambdalattice", Vector(BackendChecks))
    val twoNaturals = termInstruction(fixtureTerm("wrong_declaration", "library/two_naturals_library", "two_naturals"))
    specializationVouched(library, "big_integer", twoNaturals) match
      case Some((2, Bounded.Finished(Vector(_)), Bounded.Finished(Vector()))) => ()
      case other => fail(s"not rejected at 2: $other")
  }

  /** The compilation of the library with natives (`nativesOn`), the native
    * route's schedule on X2 and the read of its refined term, the fixture
    * `compiled(x2, refined)` (natives_run_on_the_fixtures/0 on that fixture
    * alone), which `theNativesWriteNoFile` runs in a child JVM: the count of
    * the reading's native calls.
    */
  private[jit] def nativesRunOnTheRefinedX2(): Long =
    val x2 = compiledPrograms.collectFirst { case ("x2", program) => program }.getOrElse(fail("no program x2"))
    val (_, _, refined) = programCompiled(x2, StopSignal.NeverStopped)
    counts(fixtureRead(nativesOn, Fixture.Interned(refined)).jitState).nativeCalls

  // The natives write no file: run in a fresh working directory, the
  // compilation of the library with natives, the native route's schedule on
  // X2 and the read of its refined term, which calls the natives, leave it
  // empty, and the tree of Gezi is the same before the library is compiled
  // and after the fixture is read. The reading runs in a child JVM whose
  // working directory is the fresh one (`JitTesting.readInAFreshDirectory`).
  // One fixture, not every one: the child read the 15 compiled terms and
  // the 29 hand-written programs, and with the parent's own compilation of
  // the 15 the test took 20.3 s (2026-11-14). The library's compilation and
  // the schedule run as they did; a write by a native that X2's reading
  // does not call is no longer seen here.
  test("theNativesWriteNoFile") {
    val run = readInAFreshDirectory("gezi.jit.nativesRunOnTheRefinedX2")
    val nativeCalls = run.output.trim match
      case s"native calls reading compiled(x2, refined): $calls" => calls.toLong
      case other                                                => fail(s"the child JVM printed $other")
    assert(nativeCalls > 0)
    assertEquals(run.written, Vector.empty)
    assertEquals(run.after, run.before)
  }

/** The reading of `JitNativesTest.theNativesWriteNoFile`, the main class of
  * the child JVM that runs it in a fresh working directory: it prints the
  * count of the native calls.
  */
@main def nativesRunOnTheRefinedX2(): Unit =
  println(s"native calls reading compiled(x2, refined): ${JitNativesTest().nativesRunOnTheRefinedX2()}")
