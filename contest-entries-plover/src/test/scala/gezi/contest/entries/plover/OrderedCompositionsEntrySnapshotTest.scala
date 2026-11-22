package gezi.contest.entries.plover

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Paths
import scala.jdk.CollectionConverters.*
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.ExchangeText
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramCompiler
import gezi.narrowblocks.lists.NarrowBlockCompilation
import gezi.saturation.StopSignal
import snapshot4s.generated.snapshotConfig

/** What the lemma round of the ordered compositions makes of one dice program
  * in each spelling: how many narrow blocks it forms, whether they are
  * computed and, for the direct spelling, the program after them. Its purpose
  * is to catch a recognition that stops matching, a block that no longer
  * reaches the native, and a change in what the respelled programs reach. The
  * inputs, `dice-programs.tsv`, are the programs the judge's point generator
  * draws for `repeated_cses_dice_combinations_sum_4` from the seed 20261031 at
  * R = 1 and 4.
  */
class OrderedCompositionsEntrySnapshotTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:
  // Measured on 2 CPUs at nice 10 beside other sessions' runs: 29 to 39 s, the entry's setup and four programs' lemma
  // rounds, and one run past 60 s while the sbt server on the same CPUs was still reloading the build.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(120, "s")

  stoppableTest("the blocks of a dice program in each spelling") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val buildRoot = Paths.get(sys.props("gezi.buildRoot"))
    val fixtures = buildRoot.resolve("tests/plover_fixtures")
    val (data, afterEntry) =
      EntryData.at(buildRoot, fixtures.resolve("ordered_compositions_entry.lambdalattice"), Defaults.entryDataState)
    val entry = GenericEntryProvider.initialized(
      data,
      ExecutorModules.registered(buildRoot),
      ExtractorModules.registered(buildRoot),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )
    val compilation = entry match
      case generic: GenericEntry => generic.compilation
    val blockCompilation = NarrowBlockCompilation(compilation.index, compilation.natives)
    val programs = Files.readAllLines(buildRoot.resolve("contest-entries-plover/src/test/resources/dice-programs.tsv"), StandardCharsets.UTF_8).asScala.toVector
    val lines = programs.map { line =>
      val Vector(name, text) = line.split("\t", -1).toVector: @unchecked
      val program = ExchangeText.term(text).fold(reason => fail(s"$name: $reason"), identity)
      val (_, result) = ProgramCompiler.compiledProgram(compilation, program, false, stop)
      val blocks = result.flatMap(_.extracted).toVector.flatMap(blockCompilation.blocks).size
      val computed = result.flatMap(_.program)
      val shown = if name.startsWith("direct") then computed.fold("")(term => s" program=${ExchangeText.line(term)}") else ""
      s"$name blocks=$blocks computed=${computed.isDefined}$shown"
    }
    assertFileSnapshot(lines.mkString("", "\n", "\n"), "ordered-compositions/dice.txt")
  }
