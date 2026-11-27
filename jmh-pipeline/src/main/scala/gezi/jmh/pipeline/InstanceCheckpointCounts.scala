package gezi.jmh.pipeline

import gezi.ir.NativeSpecializer
import gezi.jit.Jit
import gezi.jit.JitRunState
import gezi.weakhead.Computed
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState

/** The deterministic counts beside `InstanceCheckpointBenchmarks`, outside JMH
  * (CONTRIBUTING, Benchmarks with JMH, rule 5): for each checkpoint policy, the
  * hot point read once from a fresh state within
  * `InstanceCheckpointInputs.limit` steps, printed as its outcome, the steps it
  * spent, and the instance table's entries, hits and held instances at its end.
  * Its purpose is to measure the steps the point needs, which sets the
  * benchmark's limit, and the memory each policy keeps, which JMH's time does
  * not show.
  */
@main def instanceCheckpointCounts(): Unit =
  countsOf(InstanceCheckpointInputs().setup)

/** The counts of each policy of the setup, whose configuration the method
  * binds.
  */
private def countsOf[C <: NativeSpecializer & Singleton](
    setup: InstanceCheckpointSetup[C]
): Unit =
  given C = setup.specializer
  val policies: Vector[(String, Jit[C])] = Vector(
    "default" -> setup.default,
    s"every ${InstanceCheckpointInputs.shortInterval} steps" -> setup.shortInterval,
    s"every ${InstanceCheckpointInputs.longInterval} steps" -> setup.longInterval
  )
  policies.foreach((name, jit) =>
    val (outcome, after) =
      NormalForms
        .normalForms(gezi.weakhead.Mode.Jit(jit), setup.program)
        .result(
          ReadingState
            .fresh(InstanceCheckpointInputs.limit, jit.readingConfiguration)
        ) match
        case Computed.Done(normalForms, after) =>
          (s"finished(${normalForms.size})", after)
        case Computed.Stopped(after) => ("stopped", after)
    val run = JitRunState.of(after, jit.configuration)
    val costs = run.tableCosts.values.toVector
    val (entries, hits, held) = (
      costs.map(_.entries).sum,
      costs.map(_.hits).sum,
      run.instanceTables.complete.size + run.olderInstances.size
    )
    println(
      Vector(
        name,
        outcome,
        s"steps=${after.budget.spent}",
        s"entries=$entries",
        s"hits=$hits",
        s"held=$held"
      ).mkString("\t")
    )
  )
