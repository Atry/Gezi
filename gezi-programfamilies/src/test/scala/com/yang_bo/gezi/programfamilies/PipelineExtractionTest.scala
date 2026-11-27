package com.yang_bo.gezi.programfamilies

import com.yang_bo.gezi.orientation.StandardOrientationCompiler
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import com.yang_bo.gezi.strategies.BaselineModules
import com.yang_bo.gezi.strategies.FixpointEgraph
import com.yang_bo.gezi.strategies.FixpointReport
import com.yang_bo.gezi.strategies.NativeRouteCompilation
import com.yang_bo.gezi.strategies.Round
import com.yang_bo.gezi.strategies.SaturationOptions
import com.yang_bo.gezi.strategies.Schedule
import com.yang_bo.gezi.strategies.CountedExtractor
import com.yang_bo.gezi.strategies.StandardIndexer
import com.yang_bo.gezi.strategies.StandardSaturator

/** The pipeline's extraction (`Pipeline.extracted`) is the extraction of a
  * round of the baseline's search strategy: on each size family at 1, 4 and 16,
  * the round `FixpointEgraph` with the configuration's enabled modules and
  * budget and the extraction options of the native route
  * (`NativeRouteCompilation.extraction`), run by `Schedule.run` on the program
  * after the front end, gives the output the pipeline extracted and ends as the
  * pipeline's saturation ended. Each family is a test of its own, named after
  * it.
  */
class PipelineExtractionTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
  given com.yang_bo.gezi.ir.NoFacts.type = com.yang_bo.gezi.ir.NoFacts

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of PipelineExtractionTest, "numeral", takes 3.365 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  private lazy val compiled: Map[String, CompiledConfiguration] =
    CompiledConfigurations.byName

  Pipeline.sizeFamilies.foreach { family =>
    stoppableTest(family.family) { stopped =>
      val configuration = compiled(family.configuration.name)
      val index = configuration.library.index
      val round = Round(
        FixpointEgraph(
          index,
          StandardSaturator(
            SaturationOptions(
              configuration.enabledLemmas,
              BuiltInRule.beforeOptIn,
              family.configuration.budget,
              BaselineLemmaEncoding,
              ClosureCompilation,
              StandardIndexer,
              StandardOrientationCompiler,
              MemoRetention.Kept,
              com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts)
            )
          ),
          CountedExtractor(
            NativeRouteCompilation.extraction,
            BaselineModules.table
          )
        ),
        None
      )
      Vector(1, 4, 16).foreach { size =>
        val afterFrontEnd =
          Pipeline.frontEnd(configuration, family.item(size).program)
        val run = Pipeline.saturated(
          Pipeline.indexCompiled(configuration, afterFrontEnd)
        )
        val extraction = Pipeline.extracted(configuration, afterFrontEnd, run)
        val scheduled = Schedule.run(
          index,
          Vector(afterFrontEnd.inputInstruction),
          Vector(round),
          StopSignal.completedWith(stopped)
        )
        assert(
          scheduled.outputs.size == extraction.outputs.size &&
            scheduled.outputs
              .lazyZip(extraction.outputs)
              .forall(com.yang_bo.gezi.ir.Configured.same(_, _)),
          s"the outputs differ at size $size"
        )
        assertEquals(
          scheduled.records.map(_.report),
          Vector(FixpointReport(run.end)),
          size
        )
      }
    }
  }
