package gezi.strategies

import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.ir.BuiltInRule
import gezi.ir.Instruction
import gezi.ir.LemmaIdentifier
import gezi.knowledgereading.KnowledgeReading
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.standardlibrary.StandardLibrary

/** The baseline's implementations a test's schedule builds its rounds from,
  * named here once for the tests of the modules below `contest-entry`, which
  * cannot see `gezi.contest.entry.Defaults`: the standard saturator and
  * the counted extractor (the latter with the native route's extraction and the
  * baseline's modules), the baseline's lemma encoding, the standard indexer
  * and the closure backend.
  */
object BaselineRounds:

  val modules: RoundModules = RoundModules(
    StandardSaturator(_),
    CountedExtractor(NativeRouteCompilation.extraction, BaselineModules.table),
    BaselineLemmaEncoding,
    StandardIndexer,
    ClosureCompilation,
    StandardOrientationCompiler
  )

  /** The saturation options of the lemmas the round's knowledge term writes
    * (`StandardLibrary.lemmas`; a round read off the tests' rounds entry,
    * `StrategyTesting.round`), the built-in rules and the budget, with the
    * lemma encoding, backend and indexer of `modules`.
    */
  def saturationOptions(
      library: StandardLibrary,
      round: Instruction,
      builtInRules: Set[BuiltInRule],
      budget: Int
  ): SaturationOptions =
    SaturationOptions(lemmas(library, round), builtInRules, budget, modules.lemmaEncoding, modules.backend, modules.indexer, modules.orientationCompiler, MemoRetention.Kept)

  /** `NativeRouteCompilation.nativeRouteSchedule` of the library with the
    * round modules `modules`: the type check enabling the lemmas the round
    * `typeCheck` writes, the erasure those of the tests' round
    * `occurrence_erasure`.
    */
  def nativeRouteSchedule(library: StandardLibrary, typeCheck: Instruction, budget: Int): Vector[Round] =
    NativeRouteCompilation.nativeRouteSchedule(
      library.index,
      lemmas(library, typeCheck),
      lemmas(library, StrategyTesting.round("occurrence_erasure")),
      budget,
      modules
    )

  /** The lemmas the round's knowledge term writes, read under a fresh state. */
  def lemmas(library: StandardLibrary, round: Instruction): Vector[LemmaIdentifier] =
    library.lemmas(round, KnowledgeReading.startingState)._1
