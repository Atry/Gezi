package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.programfamilies.CompiledConfiguration
import gezi.programfamilies.FrontEnd
import gezi.programfamilies.Pipeline
import gezi.programfamilies.Saturated
import gezi.backendcomparison.Compiled
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Warmup

/** The stages of Gezi's pipeline (`gezi.programfamilies.Pipeline`),
  * one benchmark each, every stage on the values the stages before it give,
  * built in the trial's setup: the knowledge files read and the library and
  * its orientations compiled, the program through the front end, the index
  * and the closure backend compiled, and the graph saturated to its End.
  * Each returns its stage's value, so that JMH consumes it. The whole
  * pipeline is the sum of the four.
  *
  * The mode is the average time of a call: a call longer than an iteration,
  * as a saturation of a size of 512 or 1,024 is, makes the iteration one
  * call. Each trial's JVM has the heap of 256 MB that the tests have
  * (`gezi/programfamilies/build.sbt`) and the serial
  * collector, so that no collection runs on threads beside the benchmark's.
  * The warm-up, two iterations of three seconds, is set from a trial of
  * fifteen warm-up iterations of one second on 2026-10-31: every
  * benchmark of a call shorter than a second had reached its plateau by the
  * sixth second, and every call longer than a second by the second call.
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 3, jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 2, time = 3, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
class PipelineBenchmarks:

  /** The knowledge files read and the configuration's library and
    * orientations compiled.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def libraryCompiled(input: LibraryInput): CompiledConfiguration =
    Pipeline.libraryCompiled(input.configuration, input.buildRoot)

  /** The item's program through the front end. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def frontEnd(input: ItemInput): FrontEnd =
    Pipeline.frontEnd(input.compiled, input.item.program)

  /** The run's input compiled by the index and the closure backend. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def indexCompiled(input: ItemInput): Compiled =
    Pipeline.indexCompiled(input.compiled, input.afterFrontEnd)

  /** The graph saturated to its End. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def saturated(input: ItemInput): Saturated =
    Pipeline.saturated(input.indexed)
