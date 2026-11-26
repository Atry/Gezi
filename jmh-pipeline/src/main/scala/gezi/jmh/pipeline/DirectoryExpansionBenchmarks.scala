package gezi.jmh.pipeline

import gezi.ir.{ChoiceSpine, Configured, NoFacts}
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
import gezi.directorysugar.DirectoryTree
import gezi.programfamilies.FixedPointLines
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup

/** The configuration of the terms here: no facts. */
private given directoryExpansionBenchmarksNoFacts: NoFacts.type = NoFacts

/** The URI node of the standard library's directory, the largest a program's
  * imports expand.
  */
@State(Scope.Benchmark)
class DirectoryExpansionInputs:

  lazy val library: Configured[NoFacts.type] =
    NoFacts.uri(FixedPointLines.buildRoot.toAbsolutePath.normalize.resolve("corpora/library").toUri)

/** One small example of what the first reading of a tree pays: the expansion
  * of one directory, a partial function for each of its entries converted to
  * the IR. Its purpose is the time and, under `-prof gc`, the allocation of
  * that conversion. An expansion takes tenths of a second, so each is timed
  * once per iteration (`Mode.SingleShotTime`).
  */
@BenchmarkMode(Array(Mode.SingleShotTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(value = 1, jvmArgsAppend = Array("-Xmx2g", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 10)
@Measurement(iterations = 10)
class DirectoryExpansionBenchmarks:

  /** The library directory's unit, built from its listing. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def libraryDirectory(input: DirectoryExpansionInputs): Configured[NoFacts.type] = DirectoryTree.expansion(input.library)
