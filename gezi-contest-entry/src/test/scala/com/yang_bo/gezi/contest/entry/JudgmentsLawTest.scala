package com.yang_bo.gezi.contest.entry

import java.nio.file.Paths
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.ProgramPurity
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.jit.BackendChecks
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.JitConfiguration
import com.yang_bo.gezi.jit.TableCost
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.weakhead.NoJitState
import com.yang_bo.gezi.weakhead.Reading
import scala.util.Random

/** The laws of the framework's judgment (`Judgments.judged`) on generated
  * closed programs: on a pure program T with one normal form N0 and a candidate
  * N that is another program's normal form, the display is N when N = N0 and
  * `0` otherwise; a refuted N is never among T's normal forms; and a program
  * that is a choice or a parallel of such programs is never refuted. Purpose:
  * catch a refutation of a member, which voids an entry, and a refutation drawn
  * from a reading that cannot refute (a program with a choice or a parallel).
  *
  * The inputs are generated from fixed seeds by a generator adapted from one of
  * commit 3c9fd3084 (`RepetitionSharingLawTest`), as the deleted
  * `TrapRefutationLawTest` of `contest-entries-solo` was (`git show
  * c78b37577:lambda_jit/contest-entries-solo/src/test/scala/lambdajit/contest/entries/solo/TrapRefutationLawTest.scala`).
  */
class JudgmentsLawTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  given com.yang_bo.gezi.ir.NoFacts.type = com.yang_bo.gezi.ir.NoFacts

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of JudgmentsLawTest, "a judgment on a pure program with one normal form displays the candidate or no normal form", takes 8.206 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  /** The framework's evaluator over the standard library with no module
    * enabled: the library of the fixture tests/library_fixtures/no_knowledge,
    * whose knowledge is top (`StandardLibrary.compiledAt`, Gezi's directory the
    * visible subtree): the generated programs are pure λ terms and use no
    * library file.
    */
  private val evaluator =
    val buildRoot = Paths.get(sys.props("gezi.buildRoot"))
    val library = StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/no_knowledge.lambdalattice"),
      Vector(BackendChecks)
    )
    Defaults.jit(
      BackendFacts.of(library),
      JitOptions(
        DispatchOption.Fallback,
        BackendOption.Closure,
        GranularityOption.PredicatePerCode,
        instanceTable = false,
        instanceTableTrial = TableCost.trial,
        instanceRetention = InstanceRetentionOption.Generations(
          JitConfiguration.defaultInstanceTableGeneration
        ),
        budget = JitConfiguration.defaultBudget,
        checkpoints = CheckpointOption.Profitable,
        nativeBlocks = NativeBlocksOption.None,
        lookahead = LookaheadOption.Lazily,
        instanceReuse = InstanceReuseOption.WithinVersion
      ),
      GroupBlocksOption.None,
      com.yang_bo.gezi.ir.StorageAccess.granted()
    )

  /** The executor the readings run on, the JIT as the entries read with it
    * (`Defaults.executor`), and its dependencies.
    */
  private val executor = com.yang_bo.gezi.weakhead.ReadingExecutor(
    com.yang_bo.gezi.weakhead.Mode.Jit(evaluator),
    evaluator.readingConfiguration,
    NoJitState
  )
  private val dependencies = com.yang_bo.gezi.hotspot.ExecutionDependencies(
    Defaults.caches(),
    com.yang_bo.gezi.hotspot.ExpansionSource.fresh()
  )

  /** The steps each reading may take, the steps that stand for one second. */
  private val limit = Reading.budgetSteps(1)

  /** A random HOAS term over the bound variables of the environment, at most
    * `depth` deep; each body draws from a seed of its own, so that the front
    * end, which calls a body once, gives the same term whenever it is called.
    */
  private def generated(
      seed: Long,
      depth: Int,
      environment: Vector[Term]
  ): Term =
    val random = Random(seed)
    val choice = if depth == 0 then 0 else random.nextInt(3)
    choice match
      case 0 if environment.nonEmpty =>
        environment(random.nextInt(environment.size))
      case 1 if environment.nonEmpty =>
        Term.Application(
          generated(random.nextLong(), depth - 1, environment),
          generated(random.nextLong(), depth - 1, environment)
        )
      case _ =>
        val bodySeed = random.nextLong()
        Term.Abstraction(variable =>
          generated(bodySeed, depth - 1, environment :+ variable)
        )

  private def normalForms(
      program: DeBruijnTerm,
      stop: StopSignal
  ): Option[Set[DeBruijnTerm]] =
    Judgments
      .read(
        executor,
        dependencies,
        Defunctionalization.thunkInstruction(program)(using com.yang_bo.gezi.ir.NoFacts),
        limit,
        stop
      )
      .normalForms

  private def judgment(
      candidate: DeBruijnTerm,
      program: DeBruijnTerm,
      stop: StopSignal
  ): Judgment =
    Judgments
      .judged(executor, dependencies, candidate, program, limit, stop)
      .judgment

  /** Generated closed pure programs, each with its one normal form when the
    * reading finds exactly one and it is pure.
    */
  private def withOneNormalForm(
      random: Random,
      count: Int,
      stop: StopSignal
  ): Vector[(DeBruijnTerm, DeBruijnTerm)] =
    Vector
      .fill(count)(
        generated(random.nextLong(), 4, Vector.empty).deBruijnTerm(Map.empty)
      )
      .flatMap(program =>
        normalForms(program, stop) match
          case Some(found)
              if found.size == 1 && found.forall(ProgramPurity.pure) =>
            found.map((program, _))
          case _ => Set.empty
      )

  stoppableTest(
    "a judgment on a pure program with one normal form displays the candidate or no normal form"
  ) { stopped =>
    val programs = withOneNormalForm(
      Random(20261107),
      200,
      StopSignal.completedWith(stopped)
    )
    assert(
      programs.size >= 10,
      s"only ${programs.size} generated programs have one normal form"
    )
    val candidates = programs.map(_._2).distinct
    programs.foreach { (program, normalForm) =>
      candidates.foreach { candidate =>
        val output = DeBruijnTerm.Parallel(candidate, program)
        val expected = if candidate == normalForm then
          OutputDisplay.shown(candidate)
        else OutputDisplay.NoNormalForm
        assertEquals(
          Judgments.displayed(
            output,
            candidate,
            judgment(candidate, program, StopSignal.completedWith(stopped))
          ),
          expected,
          s"$candidate ∥ $program"
        )
      }
    }
  }

  stoppableTest(
    "a refuted candidate is never among the program's normal forms"
  ) { stopped =>
    val programs = withOneNormalForm(
      Random(20261108),
      200,
      StopSignal.completedWith(stopped)
    )
    val candidates = programs.map(_._2).distinct
    val choices = programs.zip(programs.drop(1)).map {
      case ((first, _), (second, _)) => DeBruijnTerm.Choice(first, second)
    }
    val refuted = (programs.map(_._1) ++ choices).flatMap { program =>
      candidates
        .filter(candidate =>
          judgment(
            candidate,
            program,
            StopSignal.completedWith(stopped)
          ) == Judgment.Refuted
        )
        .map((_, program))
    }
    assert(
      refuted.nonEmpty,
      "no generated judgment was refuted, so the law tests nothing"
    )
    refuted.foreach { (candidate, program) =>
      assert(
        !normalForms(program, StopSignal.completedWith(stopped))
          .exists(_.contains(candidate)),
        s"$candidate refuted on $program, yet among its normal forms"
      )
    }
  }

  /** A judgment cell gives the candidate and the program as constants (the
    * runner's `PipeLines.cellTerm`): the judgment of the two as constants is
    * the judgment of them written out, every judgment among them. Purpose:
    * catch a judgment that compares a constant candidate with the normal forms
    * read back, which never proves, or that decides the purity of a constant
    * program on the constant, which never refutes (the judgment points read
    * unknown on main, 2026-11-22).
    */
  stoppableTest(
    "a judgment of a candidate and a program given as constants is the judgment of them written out"
  ) { stopped =>
    val programs = withOneNormalForm(
      Random(20261122),
      200,
      StopSignal.completedWith(stopped)
    )
    val candidates = programs.map(_._2).distinct
    val judgments = programs.flatMap((program, _) =>
      candidates.map(candidate =>
        val constants = judgment(
          DeBruijnTerm.Constant(
            Defunctionalization.thunkInstruction(candidate)(using
              com.yang_bo.gezi.ir.NoFacts
            )
          ),
          DeBruijnTerm.Constant(
            Defunctionalization.thunkInstruction(program)(using com.yang_bo.gezi.ir.NoFacts)
          ),
          StopSignal.completedWith(stopped)
        )
        (
          candidate,
          program,
          constants,
          judgment(candidate, program, StopSignal.completedWith(stopped))
        )
      )
    )
    assert(
      judgments.exists(_._4 == Judgment.Proved),
      "no generated judgment was proved, so the law tests nothing"
    )
    assert(
      judgments.exists(_._4 == Judgment.Refuted),
      "no generated judgment was refuted, so the law tests nothing"
    )
    judgments.foreach { (candidate, program, constants, writtenOut) =>
      assertEquals(constants, writtenOut, s"$candidate ∥ $program")
    }
  }

  stoppableTest(
    "a judgment on a choice or a parallel of programs is never refuted"
  ) { stopped =>
    val programs = withOneNormalForm(
      Random(20261109),
      200,
      StopSignal.completedWith(stopped)
    )
    programs.zip(programs.drop(1)).foreach {
      case ((first, firstForm), (second, secondForm)) =>
        val choice = DeBruijnTerm.Choice(first, second)
        val parallel = DeBruijnTerm.Parallel(first, second)
        Vector(firstForm, secondForm).foreach { candidate =>
          assertNotEquals(
            judgment(candidate, choice, StopSignal.completedWith(stopped)),
            Judgment.Refuted,
            s"$candidate ∥ $choice"
          )
          assertNotEquals(
            judgment(candidate, parallel, StopSignal.completedWith(stopped)),
            Judgment.Refuted,
            s"$candidate ∥ $parallel"
          )
        }
    }
  }

  /** The count `reading_steps` a reading reports is the evaluator steps the
    * reading spent: the same as `Budget.spent` of the framework's reading of
    * the same program under the same limit, read directly, and at least the
    * limit when the reading stopped (no cancel is requested here). Purpose:
    * catch a count that is not the reading's steps (zero, the limit, a count of
    * another reading), since whether a program is compiled is read from it, a
    * compiled reading spending few steps however much its blocks compute.
    */
  stoppableTest("a reading reports the evaluator steps it spent") { stopped =>
    val random = Random(20261110)
    val programs = Vector.fill(200)(
      generated(random.nextLong(), 4, Vector.empty).deBruijnTerm(Map.empty)
    )
    val readings = programs.map { program =>
      val instruction =
        Defunctionalization.thunkInstruction(program)(using com.yang_bo.gezi.ir.NoFacts)
      val reported = Judgments.read(
        executor,
        dependencies,
        instruction,
        limit,
        StopSignal.completedWith(stopped)
      )
      val direct = com.yang_bo.gezi.weakhead.NormalForms
        .normalForms(com.yang_bo.gezi.weakhead.Mode.Jit(evaluator), instruction)
        .result(
          com.yang_bo.gezi.weakhead.ReadingState
            .fresh(0, evaluator.readingConfiguration)
            .copy(budget =
              com.yang_bo.gezi.weakhead.Budget
                .stoppedBy(limit, StopSignal.completedWith(stopped))
            )
        )
      val spent = direct match
        case com.yang_bo.gezi.weakhead.Computed.Done(_, after) => after.budget.spent
        case com.yang_bo.gezi.weakhead.Computed.Stopped(after) => after.budget.spent
      val counts = reported.reports.collect {
        case Count("reading_steps", value) => value
      }
      (program, reported, counts, spent)
    }
    assert(
      readings.exists(_._2.normalForms.isDefined),
      "no generated reading finished, so the law tests nothing"
    )
    readings.foreach { (program, reported, counts, spent) =>
      assertEquals(counts, Vector(spent), s"$program")
      if reported.normalForms.isEmpty then
        assert(spent >= limit, s"$program stopped after $spent of $limit steps")
    }
  }
