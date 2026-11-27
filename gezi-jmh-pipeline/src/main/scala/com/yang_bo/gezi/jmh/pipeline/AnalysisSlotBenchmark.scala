package com.yang_bo.gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import com.yang_bo.gezi.egraph.ClassAnalysis
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.programfamilies.Pipeline
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.saturation.StopSignal
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Warmup

/** The analysis whose every cost is the same: the slot's bookkeeping with no
  * repair, since a union never changes a class's cost.
  */
object TrivialAnalysis extends ClassAnalysis[NoFacts.type, Unit]:
  def identity: Unit = ()
  def made(layer: LayerWith[Unit, Configured[NoFacts.type]]): Unit = ()
  def joined(left: Unit, right: Unit): Unit = ()

/** The cost of keeping a cost analysis on the e-graph: the saturation of
  * `PipelineBenchmarks.saturated`, plain and with the graph keeping the trivial
  * analysis from the pattern instructions on, so that the difference is the
  * slot's bookkeeping (a cost per node added, a join per union, the users of a
  * joined class read) and not an analysis's own work. The settings are
  * `PipelineBenchmarks`'.
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
class AnalysisSlotBenchmark:

  private given NoFacts.type = NoFacts

  /** The graph saturated to its End, keeping no analysis. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def plainSaturated(input: ItemInput): EGraph[NoFacts.type] =
    Pipeline.saturated(input.indexed).graph

  /** The graph saturated to its End, keeping the trivial analysis. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def trivialSlotSaturated(input: ItemInput): EGraph[NoFacts.type] =
    val item = input.indexed
    val run = item.input
    val initial = Saturation
      .initialGraph(
        run.store,
        item.headArityBounds,
        run.patternInstructions,
        explained = false
      )
      .analysed(TrivialAnalysis)
    val (withInputs, _) = Saturation.inputsAdded(initial, run.inputs)
    Saturation
      .saturated(
        item.program,
        item.compiled,
        BuiltInRule.beforeOptIn,
        withInputs,
        run.budget,
        StopSignal.NeverStopped
      )
      ._1
