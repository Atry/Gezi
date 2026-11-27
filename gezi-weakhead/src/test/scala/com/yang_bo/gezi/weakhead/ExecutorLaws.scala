package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Configured
import hedgehog.Result
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.hotspot.Budget
import com.yang_bo.gezi.hotspot.ExecutionDependencies
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.hotspot.Executor
import com.yang_bo.gezi.hotspot.Progress
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.ir.Apply
import com.yang_bo.gezi.ir.Choice
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Parallel
import com.yang_bo.gezi.ir.Thunk
import com.yang_bo.gezi.saturation.StopSignal
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.NativeSpecializer

/** The laws of an executor (`com.yang_bo.gezi.hotspot.Executor`, `com.yang_bo.gezi.hotspot.Budget`)
  * that an executor of the baseline is checked against, on a closed term of the
  * generators of the tests that use them: the resume law, honest costs, of
  * steps and of the counts of applications, and the exact count of applications
  * on Church numerals. The residual law is vacuous while `exported` is `None`,
  * so it has no check here.
  */
object ExecutorLaws:

  given NoFacts.type = NoFacts

  /** The steps an uninterrupted execution may take; a term whose reading takes
    * more is read as not finishing, and its laws hold vacuously.
    */
  val largeSteps: Long = 20000

  /** The budget of the first execution of a split reading, doubled at every
    * resumption until the reading finishes.
    */
  val firstSteps: Long = 3

  /** The term defunctionalized and interned, and dependencies with an empty
    * cache service.
    */
  def interned(
      term: DeBruijnTerm
  ): (Configured[NoFacts.type], ExecutionDependencies) =
    val instruction = Defunctionalization.thunkInstruction[NoFacts.type](term)
    (
      instruction,
      ExecutionDependencies(BaselineCaches.provider(), ExpansionSource.fresh())
    )

  /** The resume law (4.2): a reading interrupted by small budgets and resumed,
    * each resumption with twice the budget of the one before, finds the normal
    * forms the uninterrupted reading finds, in the same order; and the
    * uninterrupted reading finds what `NormalForms.normalForms` reads under the
    * mode; and the first suspension resumed twice reads alike (`resumedTwice`).
    * Holds vacuously for a term whose uninterrupted reading does not finish
    * within `largeSteps`, and its clause on the normal-form reader for a term
    * the reader does not finish within `largeSteps`: the executor and the
    * reader count their steps apart, and whether a reading halts within a
    * budget may differ, only what a reading that halts finds may not (whether a
    * reading halts may vary, what it finds when it halts may not: with
    * `HEDGEHOG_SEED=40665768259069` the JIT executor finished a term holding
    * top with no normal form while the reader under the same mode ran past
    * `largeSteps`).
    */
  def resumeLaw[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      mode: Mode,
      term: DeBruijnTerm,
      stop: StopSignal
  ): Result =
    val (instruction, dependencies) = interned(term)
    val (_, _, whole) = executor.executed(
      instruction,
      dependencies,
      Budget(largeSteps, countedUnits = false, stop)
    )
    whole.suspension match
      case Some(_) => Result.success
      case None    =>
        val (afterFirst, firstDependencies, first) = executor.executed(
          instruction,
          dependencies,
          Budget(firstSteps, countedUnits = false, stop)
        )
        val split = resumedToTheEnd(
          afterFirst,
          firstDependencies,
          first,
          firstSteps,
          first.found,
          stop
        )
        val readerAgrees = NormalForms
          .normalForms(mode, com.yang_bo.gezi.ir.Value.of(instruction))
          .result(
            ReadingState.fresh(
              largeSteps,
              com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
            )
          ) match
          case Computed.Done(normalForms, _) =>
            Result.diff(normalForms, whole.found)(
              EvaluatorTesting.sameInstructions
            )
          case Computed.Stopped(_) => Result.success
        Result
          .all(
            List(
              Result.diff(split, whole.found)(
                EvaluatorTesting.sameInstructions
              ),
              readerAgrees,
              resumedTwice(afterFirst, firstDependencies, first, stop)
            )
          )
          .log(
            s"the term: ${com.yang_bo.gezi.frontend.Lambdalattice.text(term, Map.empty)}"
          )

  /** The residual law (`com.yang_bo.gezi.hotspot.Executor`): a suspension exported as a
    * residual r (`exported`) leaves the term equal to the normal forms found so
    * far chosen with r, so the normal forms found before the suspension
    * together with those r reads to the end are the normal forms the whole term
    * reads. Checked on a term whose whole reading finishes within `largeSteps`,
    * for a first call of `firstSteps` that suspends; an export of nothing
    * passes, as the law allows. Its purpose is to catch a residual that drops a
    * normal form the term has, or adds one it has not.
    */
  def residualLaw[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      term: DeBruijnTerm,
      stop: StopSignal
  ): Result =
    val (instruction, dependencies) = interned(term)
    val (_, _, whole) = executor.executed(
      instruction,
      dependencies,
      Budget(largeSteps, countedUnits = false, stop)
    )
    whole.suspension match
      case Some(_) => Result.success
      case None    =>
        val (afterFirst, firstDependencies, first) = executor.executed(
          instruction,
          dependencies,
          Budget(firstSteps, countedUnits = false, stop)
        )
        first.suspension match
          case None             => Result.success
          case Some(suspension) =>
            afterFirst.exported(suspension, firstDependencies)._2 match
              case None           => Result.success
              case Some(residual) =>
                val (_, _, residualRead) = executor.executed(
                  residual,
                  dependencies,
                  Budget(largeSteps, countedUnits = false, stop)
                )
                residualRead.suspension match
                  case Some(_) =>
                    Result.failure.log(
                      "the residual does not finish within the steps the whole term finishes in"
                    )
                  case None =>
                    Result
                      .diff(
                        (first.found ++ residualRead.found).toSet,
                        whole.found.toSet
                      )(_ == _)
                      .log(
                        s"the term: ${com.yang_bo.gezi.frontend.Lambdalattice.text(term, Map.empty)}"
                      )

  /** A suspension resumed twice by the same executor under the same
    * dependencies and budget finds the same normal forms and spends the same
    * steps (a suspension may be resumed more than once), so that a suspension
    * that holds a continuation usable once breaks the law.
    */
  private def resumedTwice[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      dependencies: ExecutionDependencies,
      progress: Progress[NoFacts.type, Suspension],
      stop: StopSignal
  ): Result =
    progress.suspension match
      case None             => Result.success
      case Some(suspension) =>
        val budget = Budget(2 * firstSteps, countedUnits = false, stop)
        val (_, _, once) = executor.resumed(suspension, dependencies, budget)
        val (_, _, twice) = executor.resumed(suspension, dependencies, budget)
        Result.all(
          List(
            Result.diff(twice.found, once.found)(
              EvaluatorTesting.sameInstructions
            ),
            Result.diff(twice.spent, once.spent)(_ == _)
          )
        )

  @tailrec
  private def resumedToTheEnd[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      dependencies: ExecutionDependencies,
      progress: Progress[NoFacts.type, Suspension],
      steps: Long,
      found: Vector[Configured[NoFacts.type]],
      stop: StopSignal
  ): Vector[Configured[NoFacts.type]] =
    progress.suspension match
      case None             => found
      case Some(suspension) =>
        val doubled = 2 * steps
        val (after, afterDependencies, next) = executor.resumed(
          suspension,
          dependencies,
          Budget(doubled, countedUnits = false, stop)
        )
        resumedToTheEnd(
          after,
          afterDependencies,
          next,
          doubled,
          found ++ next.found,
          stop
        )

  /** Counting is unobservable (`com.yang_bo.gezi.hotspot.Budget`: counting is done only
    * when asked, and asking changes nothing else): the term executed within the
    * budget with counted units and without finds the same normal forms,
    * suspends alike and spends the same steps, and so does the suspension,
    * resumed within `largeSteps` each way; and the executors the two calls
    * return keep alike what `keptAlike` compares (`readingTablesAlike` for the
    * weak head's tables; nothing for the JIT, whose compiled closures compare
    * by identity). Its purpose is to catch a count that leaks into the reading:
    * a step charged for it, a table keyed by it, a branch taken on it.
    */
  def countingUnobservableLaw[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      term: DeBruijnTerm,
      steps: Long,
      stop: StopSignal,
      keptAlike: (
          Executor[NoFacts.type, Suspension],
          Executor[NoFacts.type, Suspension]
      ) => Result
  ): Result =
    val (instruction, dependencies) = interned(term)
    val (afterCounted, countedDependencies, counted) = executor.executed(
      instruction,
      dependencies,
      Budget(steps, countedUnits = true, stop)
    )
    val (afterPlain, _, plain) = executor.executed(
      instruction,
      dependencies,
      Budget(steps, countedUnits = false, stop)
    )
    val resumedAlike = (counted.suspension, plain.suspension) match
      case (Some(countedSuspension), Some(plainSuspension)) =>
        val (_, _, countedNext) = afterCounted.resumed(
          countedSuspension,
          countedDependencies,
          Budget(largeSteps, countedUnits = true, stop)
        )
        val (_, _, plainNext) = afterPlain.resumed(
          plainSuspension,
          dependencies,
          Budget(largeSteps, countedUnits = false, stop)
        )
        progressAlike(countedNext, plainNext)
      case _ => Result.success
    Result
      .all(
        List(
          progressAlike(counted, plain),
          resumedAlike,
          keptAlike(afterCounted, afterPlain)
        )
      )
      .log(s"the term: ${com.yang_bo.gezi.frontend.Lambdalattice.text(term, Map.empty)}")

  /** Two reading executors that keep the same tables: the same complete tables
    * and the same incomplete ones, each with its status and answers, and the
    * same heads marked unverified. A stopped producer's rest is a stream, a
    * closure that compares by identity, so the producers are not compared.
    */
  def readingTablesAlike(
      left: Executor[NoFacts.type, ReadingSuspension[NoFacts.type]],
      right: Executor[NoFacts.type, ReadingSuspension[NoFacts.type]]
  ): Result =
    (left, right) match
      // A type test on the executor's class, its configuration a wildcard; the tables of the two are compared as the
      // sets and maps they are.
      case (
            leftReading: ReadingExecutor[?],
            rightReading: ReadingExecutor[?]
          ) =>
        Result.all(
          List(
            Result.diff(
              leftReading.tables.complete,
              rightReading.tables.complete
            )(_ == _),
            Result.diff(leftReading.tables.open, rightReading.tables.open)(
              _ == _
            ),
            Result.diff(leftReading.unverified, rightReading.unverified)(_ == _)
          )
        )
      case _ => Result.failure.log(s"not reading executors: $left, $right")

  /** Two progresses alike but for their counts of applications. */
  private def progressAlike[Suspension](
      counted: Progress[NoFacts.type, Suspension],
      plain: Progress[NoFacts.type, Suspension]
  ): Result =
    Result.all(
      List(
        Result.diff(counted.found, plain.found)(
          EvaluatorTesting.sameInstructions
        ),
        Result.diff(counted.suspension.isDefined, plain.suspension.isDefined)(
          _ == _
        ),
        Result.diff(counted.spent.steps, plain.spent.steps)(_ == _),
        Result.diff(plain.spent.applications, Map.empty)(_ == _)
      )
    )

  /** Honest counts (4.3, of applications): the term executed within the budget
    * with counted units counts only `Code` units, each count positive, each
    * code one the term's instruction reaches (`reachedCodes`) or one of the
    * codes the reader makes itself that `readerCodes` lists (the packs under
    * `ContinuationReading.Packed`, `packCodes`), and two executions count
    * alike; with `withinSteps`, the counts sum to at most the steps spent, a
    * check for the weak head's machines, where each count comes with a step of
    * its own, the one that evaluates the thunk or applies the head, or the call
    * of the instance right after it (`WeakHead`, APPLICATIONS COUNTED), and not
    * for the JIT, whose compiled clauses enter instances within one step
    * (`com.yang_bo.gezi.jit.Jit`, the same section). Its purpose is to catch a count of a
    * code the reading never entered, a count taken twice for one entry, and a
    * count that depends on anything but the reading.
    */
  def honestCountsLaw[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      term: DeBruijnTerm,
      steps: Long,
      stop: StopSignal,
      withinSteps: Boolean,
      readerCodes: Set[Code]
  ): Result =
    val (instruction, dependencies) = interned(term)
    val (_, _, first) = executor.executed(
      instruction,
      dependencies,
      Budget(steps, countedUnits = true, stop)
    )
    val (_, _, second) = executor.executed(
      instruction,
      dependencies,
      Budget(steps, countedUnits = true, stop)
    )
    val reached = reachedCodes(instruction) ++ readerCodes
    val counts = first.spent.applications
    Result
      .all(
        List(
          Result.diff(second.spent.applications, counts)(_ == _),
          Result
            .assert(counts.values.forall(_ > 0))
            .log(s"the counts: $counts"),
          Result
            .assert(counts.keys.forall(reached.contains))
            .log(s"the counts: $counts"),
          if withinSteps then
            Result
              .assert(counts.values.sum <= first.spent.steps)
              .log(
                s"${counts.values.sum} counted in ${first.spent.steps} steps"
              )
          else Result.success
        )
      )
      .log(s"the term: ${com.yang_bo.gezi.frontend.Lambdalattice.text(term, Map.empty)}")

  /** The codes of every thunk the instruction holds, at any depth: of its thunk
    * layers, and of the thunks nested in those codes, whose instances are the
    * only thunks a reading of the instruction makes.
    */
  def reachedCodes[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C): Set[Code] =
    @tailrec
    def walked(
        instructions: List[Configured[C]],
        codes: List[Code],
        seenInstructions: Set[Configured[C]],
        found: Set[Code]
    ): Set[Code] =
      codes match
        case code :: laterCodes =>
          if found.contains(code) then
            walked(instructions, laterCodes, seenInstructions, found)
          else
            walked(
              instructions,
              codeThunks(code) ++ laterCodes,
              seenInstructions,
              found + code
            )
        case Nil =>
          instructions match
            case Nil                                              => found
            case next :: later if seenInstructions.contains(next) =>
              walked(later, Nil, seenInstructions, found)
            case next :: later =>
              next.layer match
                case Thunk(code, _, fillings) =>
                  walked(
                    fillings.toList ++ later,
                    List(code),
                    seenInstructions + next,
                    found
                  )
                case Apply(function, argument) =>
                  walked(
                    function :: argument :: later,
                    Nil,
                    seenInstructions + next,
                    found
                  )
                case Parallel(left, right) =>
                  walked(
                    left :: right :: later,
                    Nil,
                    seenInstructions + next,
                    found
                  )
                case Choice(left, right) =>
                  walked(
                    left :: right :: later,
                    Nil,
                    seenInstructions + next,
                    found
                  )
                case _ => walked(later, Nil, seenInstructions + next, found)
    walked(List(instruction), Nil, Set.empty, Set.empty)

  /** The codes of the packs `WeakHead.pack` makes for the arities it keeps, and
    * of the thunks nested in them: closed terms the reader makes under
    * `ContinuationReading.Packed`, whose instances a program that applies a
    * pack's tuple to its last argument enters (`WeakHead`, APPLICATIONS
    * COUNTED).
    */
  val packCodes: Set[Code] =
    (0 to WeakHead.keptPackArity).toSet.flatMap(arity =>
      WeakHead.pack(arity) match
        case Value.Thunk(code, _, _) => codesUnder(code)
        case other                   =>
          throw IllegalStateException(s"a pack is a thunk, not $other")
    )

  /** The code and the codes of the thunks nested in it, at any depth. */
  private def codesUnder(code: Code): Set[Code] =
    @tailrec
    def walked(pending: List[Code], found: Set[Code]): Set[Code] =
      pending match
        case Nil                                   => found
        case next :: later if found.contains(next) => walked(later, found)
        case next :: later => walked(codeThunks(next) ++ later, found + next)
    walked(List(code), Set.empty)

  /** The codes of the thunks nested in the code, one layer of thunks deep. */
  private def codeThunks(code: Code): List[Code] =
    @tailrec
    def walked(pending: List[Code], found: List[Code]): List[Code] =
      pending match
        case Nil           => found
        case next :: later =>
          next.layer match
            case Thunk(inner, _, fillings) =>
              walked(fillings.toList ++ later, inner :: found)
            case Apply(function, argument) =>
              walked(function :: argument :: later, found)
            case Parallel(left, right) => walked(left :: right :: later, found)
            case Choice(left, right)   => walked(left :: right :: later, found)
            case _                     => walked(later, found)
    walked(List(code), Nil)

  /** The program of the exact count: the Church numeral n applied to the box
    * `λy p. p y p` and to the identity,
    * `(λf x. f (… (f x))) (λy p. p y p) (λa. a)`, whose normal form is the box
    * applied n times, `λp. p (λp. p (… λa. a) p) p`. Its reading applies the
    * box n times, once for each `f` of the numeral's body: the weak head reads
    * `f M` to the head `λp. p M p`, and the reader of normal forms reads `M`
    * under the binder `p`, the next application, once. The numeral's codes and
    * the identity's are entered as well; the box's code applies a slot to two
    * arguments, which no code of the numeral or of the identity does
    * (`exactCountLaw` checks that it is none of theirs), so the box's count is
    * exactly n.
    */
  def iteratedBox(n: Int): DeBruijnTerm =
    DeBruijnTerm.Apply(DeBruijnTerm.Apply(churchNumeral(n), box), identity)

  /** `λy p. p y p`. */
  val box: DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm
            .Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Variable(1)),
          DeBruijnTerm.Variable(0)
        )
      )
    )

  /** `λa. a`. */
  private val identity: DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** The Church numeral n, `λf x. f (… (f x))`. */
  private def churchNumeral(n: Int): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        (0 until n).foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)(
          (body, _) => DeBruijnTerm.Apply(DeBruijnTerm.Variable(1), body)
        )
      )
    )

  /** The exact count: `iteratedBox(n)` executed with counted units finishes and
    * counts n applications of the box's code, the code of `box`'s own thunk,
    * which the interner makes one object wherever it occurs, and that code is
    * no code the numeral or the identity reaches. Its purpose is to catch a
    * machine that misses an entry (a last hole filled, a thunk with no hole) or
    * counts one twice.
    */
  def exactCountLaw[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      n: Int,
      stop: StopSignal
  ): Result =
    val (instruction, dependencies) = interned(iteratedBox(n))
    val boxCode =
      Defunctionalization.thunkInstruction[NoFacts.type](box).layer match
        case Thunk(code, _, _) => code
        case other             =>
          throw IllegalStateException(
            s"the box's instruction is a thunk, not $other"
          )
    val others = reachedCodes(
      Defunctionalization.thunkInstruction[NoFacts.type](churchNumeral(n))
    ) ++ reachedCodes(
      Defunctionalization.thunkInstruction[NoFacts.type](identity)
    )
    val (_, _, progress) = executor.executed(
      instruction,
      dependencies,
      Budget(largeSteps, countedUnits = true, stop)
    )
    Result
      .all(
        List(
          Result.diff(others.contains(boxCode), false)(_ == _),
          Result.diff(progress.suspension.isEmpty, true)(_ == _),
          Result.diff(
            progress.spent.applications.getOrElse(boxCode, 0L),
            n.toLong
          )(_ == _)
        )
      )
      .log(s"the counts: ${progress.spent.applications}")

  /** Honest costs (4.3): an execution spends no more steps than its budget; a
    * finished execution's steps s are the least budget it finishes in, so that
    * within s it finishes having spent s and within s - 1 it is suspended
    * having spent s - 1; a suspended execution spent its whole budget. The
    * budget of a step is the evaluator's count (`Budget` of `weakhead`), so a
    * reported step count that the budget did not charge breaks the law.
    */
  def honestCostsLaw[Suspension](
      executor: Executor[NoFacts.type, Suspension],
      term: DeBruijnTerm,
      steps: Long,
      stop: StopSignal
  ): Result =
    val (instruction, dependencies) = interned(term)
    val (_, _, progress) = executor.executed(
      instruction,
      dependencies,
      Budget(steps, countedUnits = false, stop)
    )
    val spent = progress.spent.steps
    progress.suspension match
      case Some(_) => Result.diff(spent, steps)(_ == _)
      case None    =>
        val (_, _, exact) = executor.executed(
          instruction,
          dependencies,
          Budget(spent, countedUnits = false, stop)
        )
        val exactHolds = Result.all(
          List(
            Result.assert(spent <= steps),
            Result.diff(exact.suspension.isEmpty, true)(_ == _),
            Result.diff(exact.spent.steps, spent)(_ == _),
            Result.diff(exact.found, progress.found)(
              EvaluatorTesting.sameInstructions
            )
          )
        )
        if spent == 0 then exactHolds
        else
          val (_, _, short) = executor.executed(
            instruction,
            dependencies,
            Budget(spent - 1, countedUnits = false, stop)
          )
          Result.all(
            List(
              exactHolds,
              Result.diff(short.suspension.isDefined, true)(_ == _),
              Result.diff(short.spent.steps, spent - 1)(_ == _)
            )
          )
