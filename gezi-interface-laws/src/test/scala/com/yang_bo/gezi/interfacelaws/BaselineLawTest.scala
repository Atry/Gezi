package com.yang_bo.gezi.interfacelaws

import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.jit.Jit
import com.yang_bo.gezi.jit.JitConfiguration
import com.yang_bo.gezi.strategies.BaselineModules
import com.yang_bo.gezi.strategies.NativeRouteCompilation
import com.yang_bo.gezi.strategies.CountedExtractor

/** The reader law on the baseline's reader, `Jit` with one predicate per code
  * and the closure backend, as `Defaults.jit` builds it but with no dispatch,
  * since the law's terms name no library define. Its purpose is to show that
  * the law holds of the implementation a replacement is judged against.
  *
  * FIXME: one run on 2026-11-09 (branch library-directory-records, 67f8ed366)
  * https://github.com/Atry/private-overlay/issues/2006 exhausted the forked
  * JVM's heap in the reference weak_head reading of a generated closed term
  * (`JitTesting.comparison` -> `reference` -> `WeakHead.nextHead` ->
  * `choiceMembers` -> `ChoiceSpine.members`), within the reading's 200,000
  * steps; the next runs passed. The seed was lost; it is now logged before
  * every check (`GeneratedProperties.property`), so the next failure can be
  * replayed with `HEDGEHOG_SEED` and its mechanism found.
  */
class BaselineJitEvaluatorLawTest
    extends JitEvaluatorLaws(encoding =>
      Jit(
        JitConfiguration.of(
          encoding,
          instanceTable = false,
          storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
        )
      )
    )

/** The extraction laws on the baseline's extractor, `CountedExtractor` with the
  * native route's extraction and the baseline's modules
  * (`BaselineModules.table`). Its purpose is to show that the laws hold of the
  * implementation a replacement is judged against.
  */
class BaselineExtractorLawTest
    extends ExtractorLaws(
      CountedExtractor[NoFacts.type](
        NativeRouteCompilation.extraction,
        BaselineModules.table[NoFacts.type]
      ),
      CountedExtractor[LawNativeSpecializer.type](
        NativeRouteCompilation.extraction,
        BaselineModules.table[LawNativeSpecializer.type]
      )
    ):

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of BaselineExtractorLawTest, "each input has one output, in the input's class", takes 23.336 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(40, "s")

// TODO: the native block laws (`NativeBlockMechanismLaws`) are run here
// again on a mechanism that chooses a block's strategy only from a property
// proved on the e-graph and written in the term (`CONTRIBUTING.md`,
// "Types live only in the term"). The run on the deleted `BaselineNativeBlocks` reads back with
// `git show 169baa469:lambda_jit/interface-laws/src/test/scala/lambdajit/interfacelaws/BaselineLawTest.scala`.
