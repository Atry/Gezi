package gezi.contest.modules.solo

/** The reusable modules of `contest-modules-solo-extraction`: a cost model
  * that remembers a stateless model's candidates within one extraction
  * (`RememberingCostModel`, through the extraction's memo,
  * `gezi.extraction.CostModel.Memo`), the framework's narrow blocks'
  * extraction under it (`RememberingNarrowBlockExtractor`), and the extractor
  * module that an entry's data selects it by (`RememberingExtractionModule`,
  * its selector `corpora/modules/solo_remembering_extraction`). They change
  * the extraction's cost, never its outputs: a remembered call's candidates
  * are the ones the stateless model gives for the same arguments.
  *
  * Beside it, the native route's extraction (`NativeRouteExtractionModule`,
  * its selector `corpora/modules/solo_native_route_extraction`): the lemma
  * rounds of `gezi.narrowblocks.LemmaRoute`, their last round extracted with
  * the typed versions attracted (`SpecializationAttraction`, then
  * `Compression`), and the program refined into fallback points
  * (`gezi.jit.StandardRefinement`), so that the JIT checks a typed call's
  * argument at run time and calls the native bound to the callee. It changes
  * the extracted program: the narrow blocks' extraction keeps no typed
  * version.
  */
package object extraction
