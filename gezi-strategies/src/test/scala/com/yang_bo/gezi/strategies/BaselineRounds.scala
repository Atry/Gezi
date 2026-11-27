package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.TermConstruction
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import com.yang_bo.gezi.orientation.StandardOrientationCompiler
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.ir.Configured

/** The baseline's implementations a test's schedule builds its rounds from,
  * named here once for the tests of the modules below `contest-entry`, which
  * cannot see `com.yang_bo.gezi.contest.entry.Defaults`: the standard saturator and the
  * counted extractor (the latter with the native route's extraction and the
  * baseline's modules), the baseline's lemma encoding, the standard indexer and
  * the closure backend.
  */
object BaselineRounds:

  val modules: RoundModules[NoFacts.type] = modulesOf(NoFacts)

  /** The same implementations in the configuration of the specializer, its
    * terms built by its construction.
    */
  def modulesOf[C <: NativeSpecializer & Singleton](
      specializer: C
  ): RoundModules[C] = RoundModules[C](
    StandardSaturator[C](_),
    CountedExtractor(
      NativeRouteCompilation.extraction,
      BaselineModules.table[C]
    ),
    BaselineLemmaEncoding,
    StandardIndexer.of[C],
    ClosureCompilation,
    StandardOrientationCompiler,
    TermConstruction(specializer)
  )

  /** The saturation options of the lemmas the round's knowledge term writes
    * (`StandardLibrary.lemmas`; a round read off the tests' rounds entry,
    * `StrategyTesting.round`), the built-in rules and the budget, with the
    * lemma encoding, backend and indexer of `modules`.
    */
  def saturationOptions(
      library: StandardLibrary,
      round: Configured[NoFacts.type],
      builtInRules: Set[BuiltInRule],
      budget: Int
  ): SaturationOptions[NoFacts.type] =
    SaturationOptions(
      lemmas(library, round),
      builtInRules,
      budget,
      modules.lemmaEncoding,
      modules.backend,
      modules.indexer,
      modules.orientationCompiler,
      MemoRetention.Kept,
      modules.construction
    )

  /** `NativeRouteCompilation.nativeRouteSchedule` of the library with the round
    * modules `modules`: the type check enabling the lemmas the round
    * `typeCheck` writes, the erasure those of the tests' round
    * `occurrence_erasure`.
    */
  def nativeRouteSchedule[C <: NativeSpecializer & Singleton](
      library: StandardLibrary,
      typeCheck: Configured[NoFacts.type],
      budget: Int
  )(using
      specializer: C
  ): Vector[Round[C]] =
    NativeRouteCompilation.nativeRouteSchedule(
      StandardLibraryIndex.crossed(library.index, specializer),
      lemmas(library, typeCheck),
      lemmas(library, StrategyTesting.round("occurrence_erasure")),
      budget,
      modulesOf(specializer)
    )

  /** The lemmas the round's knowledge term writes, read under a fresh state. */
  def lemmas(
      library: StandardLibrary,
      round: Configured[NoFacts.type]
  ): Vector[LemmaIdentifier] =
    library.lemmas(round, KnowledgeReading.startingState)._1
