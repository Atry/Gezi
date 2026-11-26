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

/** What the first lemma round makes of one dice program, one edit distance
  * program, one longest common subsequence program, one smallest team program
  * and two billboard programs, one whose target the rods reach and one whose
  * target they do not, in each spelling: how many narrow blocks it forms,
  * whether they are
  * computed and, for the direct dice spelling, the program after them. Its
  * purpose is to catch a recognition that stops matching, as a library term
  * that is no longer the IR term the program writes does, a block that no
  * longer reaches the native, and a change in what the respelled programs
  * reach. The inputs are the programs the judge's point generator draws:
  * `dice-programs.tsv` for `repeated_cses_dice_combinations_sum_4` from the
  * seed 20261031 at R = 1 and 4, `edit-distance-programs.tsv` for
  * `repeated_library_edit_distances_small`,
  * `longest-common-subsequence-programs.tsv` for
  * `repeated_library_longest_common_subsequences_small` and
  * `smallest-team-programs.tsv` for `repeated_library_smallest_teams_small`,
  * each at R = 1, from round 29's published points, and
  * `billboard-programs.tsv` for `repeated_library_billboards_small` at R = 1,
  * `reached` from round 29's published points and `unreached` from round 30's.
  * `trailing-zeros-programs.tsv` holds the direct spelling alone, of
  * `repeated_cses_trailing_zeros_number_8` and `_number_1000000000`, at R = 1
  * from the seed 20261031, and `divisor-sums-programs.tsv` likewise, of
  * `repeated_cses_sum_of_divisors_number_10` and `_number_1000000000000`, and
  * `rectangle-cutting-programs.tsv` likewise, of
  * `repeated_cses_rectangle_cutting_sides_3_by_4` and `_sides_500_by_500`, and
  * `money-sums-programs.tsv` likewise, of `repeated_cses_money_sums_coins_4` and
  * `_coins_100`, and `modular-tower-programs.tsv` likewise, of
  * `repeated_cses_exponentiation_two_numbers_small` and `_numbers_1000000000`,
  * and `book-shop-programs.tsv` likewise, of `repeated_cses_book_shop_books_4`
  * and `_books_7`, and `minimizing-coins-programs.tsv` likewise, of
  * `repeated_cses_minimizing_coins_target_6` and `_target_8`.
  */
class OrderedCompositionsEntrySnapshotTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:
  // Measured on 2 CPUs at nice 10 beside other sessions' runs: 29 to 39 s, the entry's setup and four programs' lemma
  // rounds, and one run past 60 s while the sbt server on the same CPUs was still reloading the build.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(120, "s")

  private lazy val buildRoot = Paths.get(sys.props("gezi.buildRoot"))
  private lazy val fixtures = buildRoot.resolve("tests/plover_fixtures")
  private lazy val (data, afterEntry) =
    EntryData.at(buildRoot, fixtures.resolve("ordered_compositions_entry.lambdalattice"), Defaults.entryDataState)
  private lazy val entry = GenericEntryProvider.initialized(
    data,
    ExecutorModules.registered(buildRoot),
    ExtractorModules.registered(buildRoot),
    NativesProvider.loaded,
    ArticleDestination.Discarded,
    afterEntry,
    Defaults.caches()
  )
  private lazy val compilation = entry match
    case generic: GenericEntry[?] => generic.compilation
  private lazy val blockCompilation = NarrowBlockCompilation(compilation.index, compilation.natives, gezi.weakhead.ReadingConfiguration.withoutFacts)
  private def blockLines(resource: String, directProgramShown: Boolean, stop: StopSignal): String =
    val programs = Files.readAllLines(buildRoot.resolve(s"contest-entries-plover/src/test/resources/$resource"), StandardCharsets.UTF_8).asScala.toVector
    val lines = programs.map { line =>
      val Vector(name, text) = line.split("\t", -1).toVector: @unchecked
      val program = ExchangeText.term(text).fold(reason => fail(s"$name: $reason"), identity)
      val (_, result) = ProgramCompiler.compiledProgram(compilation, program, false, stop)
      val blocks = result.flatMap(_.extracted).toVector.flatMap(blockCompilation.blocks).size
      val computed = result.flatMap(_.program)
      val shown =
        if directProgramShown && name.startsWith("direct") then computed.fold("")(term => s" program=${ExchangeText.line(term)}")
        else ""
      s"$name blocks=$blocks computed=${computed.isDefined}$shown"
    }
    lines.mkString("", "\n", "\n")

  stoppableTest("the blocks of a dice program in each spelling") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    assertFileSnapshot(blockLines("dice-programs.tsv", true, stop), "ordered-compositions/dice.txt")
    assertFileSnapshot(blockLines("edit-distance-programs.tsv", false, stop), "ordered-compositions/edit-distance.txt")
    assertFileSnapshot(
      blockLines("longest-common-subsequence-programs.tsv", false, stop),
      "ordered-compositions/longest-common-subsequence.txt"
    )
    assertFileSnapshot(blockLines("smallest-team-programs.tsv", false, stop), "ordered-compositions/smallest-team.txt")
    assertFileSnapshot(blockLines("billboard-programs.tsv", false, stop), "ordered-compositions/billboard.txt")
    assertFileSnapshot(blockLines("trailing-zeros-programs.tsv", false, stop), "ordered-compositions/trailing-zeros.txt")
    assertFileSnapshot(blockLines("divisor-sums-programs.tsv", false, stop), "ordered-compositions/divisor-sums.txt")
    assertFileSnapshot(blockLines("rectangle-cutting-programs.tsv", false, stop), "ordered-compositions/rectangle-cutting.txt")
    assertFileSnapshot(blockLines("money-sums-programs.tsv", false, stop), "ordered-compositions/money-sums.txt")
    assertFileSnapshot(blockLines("book-shop-programs.tsv", false, stop), "ordered-compositions/book-shop.txt")
    assertFileSnapshot(blockLines("minimizing-coins-programs.tsv", false, stop), "ordered-compositions/minimizing-coins.txt")
  }

  // KNOWN FAILURE until https://github.com/Atry/private-overlay/issues/2238: the specialized spelling makes a program's
  // typed constants storages at construction (a binary natural's, a list's), and the narrow blocks do not yet take
  // storages (#2238, "块入口直接收到存储"): a constant storage is of no narrow kind and does not decode as a literal, so
  // no block is compiled.
  stoppableTest("the blocks of a modular tower program in each spelling".fail) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    assertFileSnapshot(blockLines("modular-tower-programs.tsv", false, stop), "ordered-compositions/modular-tower.txt")
  }
