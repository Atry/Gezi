package gezi.jmh.pipeline

import java.nio.file.Files
import java.nio.file.Path
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryData
import gezi.contest.entry.Interaction
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term.λ
import gezi.hotspot.ExpansionSource
import gezi.ir.NativeSpecializer
import gezi.jit.NativesProvider
import gezi.programfamilies.FixedPointLines
import gezi.saturation.StopSignal
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode as BenchmarkModeKind
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup

/** The inputs of `ArticleDestinationBenchmark`: the framework's fixture entry
  * (`contest-entries-fixture`, read by the generic entry, as
  * `CompiledRunInputs` reads it) loaded twice, once with its articles discarded
  * and once with them written to a temporary directory, and one cell whose
  * Output is `CompiledRunInputs.recursiveCount` at
  * `CompiledRunInputs.smallSize`. The fields are lazy vals, built in the first
  * warm-up iteration of each fork; the cell is run once through each entry
  * there, and the written entry's first run must leave an article in its
  * directory, so that the written benchmark times a round that writes one.
  */
@State(Scope.Benchmark)
class ArticleDestinationInputs:

  /** The cell `λs. λk. k s P`, P the recursive count. */
  lazy val cell: DeBruijnTerm =
    λ(state =>
      λ(continuation =>
        continuation(state)(
          CompiledRunInputs.recursiveCount(CompiledRunInputs.smallSize)
        )
      )
    )
      .deBruijnTerm(Map.empty)

  lazy val discarded: Entry[?] =
    ArticleDestinationInputs.entry(ArticleDestination.Discarded)

  lazy val directory: Path =
    Files.createTempDirectory("article_destination_benchmark")

  lazy val written: Entry[?] =
    val entry =
      ArticleDestinationInputs.entry(ArticleDestination.Written(directory))
    ArticleDestinationBenchmark.run(entry, cell)
    if !Files.exists(directory.resolve("round-1.art")) then
      throw IllegalStateException(
        s"the written entry's run of the cell wrote no article into $directory"
      )
    entry

object ArticleDestinationInputs:

  /** The fixture entry, its articles sent to the destination. */
  def entry(articles: ArticleDestination): Entry[?] =
    val entryDirectory =
      FixedPointLines.buildRoot.resolve(CompiledRunInputs.entryDirectory)
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    GenericEntryProvider.initialized(
      data,
      gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory),
      gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory),
      NativesProvider.loaded,
      articles,
      afterEntry,
      Defaults.caches()
    )

/** What a run of a cell allocates and costs with the entry's articles
  * discarded, as the judge's scored pass runs it, and with them written, as the
  * judge's article re-read runs it: the same cell through the same fixture
  * entry (its defunctionalization, its lemma rounds, the reading of the result
  * by its executor), differing only in the article destination the entry was
  * loaded with. Under `Discarded` the rounds run unexplained
  * (`GenericEntry.answered`) and no proof, article or trace is made; under
  * `Written` the rounds record the terms they make, and the proof, the article
  * and its trace are made and written. Its purpose is the reading that export
  * off costs nothing beyond the rounds and the reading themselves
  * (https://github.com/Atry/private-overlay/issues/1561, P2 and D7), taken by
  * allocation per operation under `-prof gc`, which machine load does not
  * disturb, rather than by a long quiet timing (CONTRIBUTING.md, "Benchmarks
  * with JMH", rule 6). Each run starts from the loaded entry, so every
  * operation is the same cell's first run through that entry's executor; the
  * shared caches of the entry (`Defaults.caches`) are its own and are kept
  * across operations, as a judge's JVM keeps them across cells. Average time;
  * one fork with the serial collector and a 2 GB heap; three warm-up and five
  * measurement iterations of 2 s.
  */
@BenchmarkMode(
  Array(BenchmarkModeKind.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(
  value = 1,
  jvmArgsAppend = Array("-Xmx2g", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 3, time = 2, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 2, timeUnit = TimeUnit.SECONDS)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
class ArticleDestinationBenchmark:

  /** The cell's run with the articles discarded. */
  @Benchmark
  def discarded(input: ArticleDestinationInputs): Interaction[?] =
    ArticleDestinationBenchmark.run(input.discarded, input.cell)

  /** The cell's run with the articles written. */
  @Benchmark
  def written(input: ArticleDestinationInputs): Interaction[?] =
    ArticleDestinationBenchmark.run(input.written, input.cell)

object ArticleDestinationBenchmark:

  /** The entry's run of the cell under a fresh source, never stopped. */
  def run[C <: NativeSpecializer & Singleton](
      entry: Entry[C],
      cell: DeBruijnTerm
  ): Interaction[C] =
    entry.run(cell, ExpansionSource.fresh(), StopSignal.NeverStopped)
