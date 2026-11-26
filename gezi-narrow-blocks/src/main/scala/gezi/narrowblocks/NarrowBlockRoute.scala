package gezi.narrowblocks

import gezi.ir.Instruction
import gezi.jit.NativeBackend
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.NormalityModule

/** One implementation of the narrow blocks, which a round's extractor data
  * chooses (`gezi.contest.entry.ExtractorImplementation`, mapped by
  * `gezi.contest.entry.Defaults.route`): the modules that spell a round's
  * extraction and its write-backs, and the route of the lemma rounds, whose
  * last round's extraction has its blocks compiled and run. The default is
  * `LemmaRoute`; `gezi.narrowblocks.lists.LemmaRoute` is the opt-in copy
  * with lists and booleans ([[gezi.narrowblocks.lists]]), kept beside it
  * until the copy beats it everywhere: a general improvement is opt-in by
  * copy on write, and the old version is deleted only once the new one is
  * better everywhere.
  */
trait NarrowBlockRoute:

  /** The modules of a round's extraction and of its write-backs: the narrow
    * blocks over the natives first, then the size.
    */
  def extractorModules(natives: NativeBackend): Vector[NormalityModule]

  /** The lemma rounds on one shared graph, then the last round's extraction
    * with its narrow blocks computed (`LemmaRoute.compiledRounds`).
    */
  def compiledRounds(
      index: StandardLibraryIndex,
      rounds: Vector[PreparedLemmaCompilation],
      natives: NativeBackend,
      program: Instruction,
      explained: Boolean,
      stop: StopSignal
  ): LemmaRoundsResult
