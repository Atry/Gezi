package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.Budget
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.ExpansionSource
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramCompiler
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import gezi.weakhead.Reading
import gezi.weakhead.ReadingExecutor

private given billboardConsumedLawTestNoFacts: NoFacts.type = NoFacts

/** The law of a billboard block whose value a context consumes: a billboard
  * call applied to the three branches of a binary natural, each giving `true`,
  * reads after the entry's lemma rounds, its block computed, as the tabled weak
  * head reads the program itself, which is `true` whether or not the rods reach
  * the target. Its purpose is to catch a block replaced by a term that is not
  * ≃_O to it, such as `top` where the target is not reached: the call has no
  * normal form there, but the context still has the answer `true`, which `top`
  * loses.
  */
class BillboardConsumedLawTest extends GeneratedProperties:

  // The first case reads the entry's data and compiles its knowledge, past the 3 s default: the setup of
  // OrderedCompositionsEntrySnapshotTest, the same fixture, took 29 to 39 s on 2 CPUs at nice 10.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(120, "s")

  private lazy val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private def field(file: String, arity: Int, position: Int): Configured[NoFacts.type] =
    StandardLibrary.entryFields(buildRoot, buildRoot.resolve(file), Expansions.none, arity)._1(position)

  private val binaryFile = "corpora/library/binary/natural.lambdalattice"
  private val listFile = "corpora/library/native_types/list.lambdalattice"

  private lazy val billboard = field("corpora/library/plover_compositions/plover_billboard.lambdalattice", 2, 0)
  private lazy val binaryZero = field(binaryFile, 5, 0)
  private lazy val binaryEven = field(binaryFile, 5, 1)
  private lazy val binaryOdd = field(binaryFile, 5, 2)
  private lazy val nil = field(listFile, 4, 0)
  private lazy val cons = field(listFile, 4, 1)

  private lazy val compilation =
    val (data, afterEntry) = EntryData.at(
      buildRoot,
      buildRoot.resolve("tests/plover_fixtures/ordered_compositions_entry.lambdalattice"),
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
    ) match
      case generic: GenericEntry[?] => generic.compilation
      case other                 => throw AssertionError(s"the fixture's entry is not the generic entry: $other")

  private def applied(function: Configured[NoFacts.type], arguments: Configured[NoFacts.type]*): Configured[NoFacts.type] =
    arguments.foldLeft(function)(NoFacts.application(_, _))

  private def binary(value: Int): Configured[NoFacts.type] =
    if value == 0 then binaryZero
    else applied(if value % 2 == 1 then binaryOdd else binaryEven, binary(value / 2))

  private def list(values: List[Int]): Configured[NoFacts.type] = values.foldRight(nil)((value, rest) => applied(cons, binary(value), rest))

  private val truth: Term = λ(yes => λ(_ => yes))

  private lazy val trueBranch = Defunctionalization.thunkInstruction(truth.deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)
  private lazy val fieldIgnored = Defunctionalization.thunkInstruction(λ(_ => truth).deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)

  /** The normal forms of the tabled weak head's reading, none when it stopped. */
  private def reading(program: Configured[NoFacts.type], stop: StopSignal): Option[Set[DeBruijnTerm]] =
    val (_, _, progress) = ReadingExecutor.tablingWeakHead.executed(
      program,
      ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
      Budget(Reading.budgetSteps(1), countedUnits = false, stop)
    )
    Option.when(progress.suspension.isEmpty)(progress.found.map(Defunctionalization.instructionTerm).toSet)

  // KNOWN FAILURE until https://github.com/Atry/private-overlay/issues/2238: the specialized spelling makes a program's
  // typed constants storages at construction (a binary natural's, a list's), and the narrow blocks do not yet take
  // storages (#2238, "块入口直接收到存储"): a constant storage is of no narrow kind and does not decode as a literal, so
  // no block is compiled.
  stoppableProperty("a consumed billboard block reads as the program itself".fail) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      rods <- Gen.list(Gen.int(Range.linear(1, 6)), Range.linear(0, 4)).forAll
      target <- Gen.int(Range.linear(0, 8)).forAll
    yield
      val program = applied(billboard, list(rods), binary(target), trueBranch, fieldIgnored, fieldIgnored)
      val (compiled, result) = ProgramCompiler.compiledProgram(compilation, program, false, stop)
      val expected = reading(program, stop)
      Result
        .all(
          List(
            Result.assert(result.flatMap(_.program).isDefined).log("the block was not computed"),
            Result.assert(expected.exists(_.nonEmpty)).log("the program itself has no normal form"),
            Result.diff(reading(compiled, stop), expected)(_ == _)
          )
        )
        .log(s"the rods $rods and the target $target")
  }
