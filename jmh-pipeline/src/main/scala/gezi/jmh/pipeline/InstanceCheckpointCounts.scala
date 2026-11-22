package gezi.jmh.pipeline

import gezi.jit.Jit
import gezi.jit.JitRunState
import gezi.weakhead.Computed
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState

/** The deterministic counts beside `InstanceCheckpointBenchmarks`, outside
  * JMH (CONTRIBUTING, Benchmarks with JMH, rule 5): for each checkpoint
  * policy, the hot point read once from a fresh state within
  * `InstanceCheckpointInputs.limit` steps, printed as its outcome, the steps
  * it spent, and the instance table's entries, hits and held instances at
  * its end. Its purpose is to measure the steps the point needs, which sets
  * the benchmark's limit, and the memory each policy keeps, which JMH's time
  * does not show.
  */
@main def instanceCheckpointCounts(): Unit =
  val input = InstanceCheckpointInputs()
  val policies: Vector[(String, Jit)] = Vector(
    "default" -> input.default,
    s"every ${InstanceCheckpointInputs.shortInterval} steps" -> input.shortInterval,
    s"every ${InstanceCheckpointInputs.longInterval} steps" -> input.longInterval
  )
  policies.foreach((name, jit) =>
    val (outcome, after) =
      NormalForms.normalForms(gezi.weakhead.Mode.Jit(jit), input.program).result(ReadingState.fresh(InstanceCheckpointInputs.limit)) match
        case Computed.Done(normalForms, after) => (s"finished(${normalForms.size})", after)
        case Computed.Stopped(after)           => ("stopped", after)
    val (entries, hits, held) = after.jitState match
      case run: JitRunState =>
        val costs = run.tableCosts.values.toVector
        (costs.map(_.entries).sum, costs.map(_.hits).sum, run.instanceTables.complete.size + run.olderInstances.size)
      case NoJitState => (0L, 0L, 0)
      case other      => throw IllegalStateException(s"the JIT left another state: $other")
    println(Vector(name, outcome, s"steps=${after.budget.spent}", s"entries=$entries", s"hits=$hits", s"held=$held").mkString("\t"))
  )
