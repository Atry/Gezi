package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.programfamilies.ClassicHindleyMilner
import gezi.programfamilies.InferredType
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Warmup

/** The classic Hindley-Milner reference
  * (`gezi.programfamilies.ClassicHindleyMilner`) on the same HOAS program the
  * pipeline reads, its type schemes read in the trial's setup. It returns the
  * principal type, or nothing for a program it rejects, so that JMH consumes
  * it. The mode, the iterations, the forks and the forks' JVM are those of
  * `PipelineBenchmarks`, for the same reasons.
  */
@BenchmarkMode(
  Array(Mode.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(
  value = 3,
  jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 2, time = 3, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
class ClassicHindleyMilnerBenchmark:

  /** The principal type of the item's program. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def programType(
      input: ItemInput,
      schemes: SchemesInput
  ): Option[InferredType] =
    ClassicHindleyMilner.programType(input.item.program, schemes.schemes)
