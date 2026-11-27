package gezi.narrowblocks

import gezi.ir.{Configured, NativeSpecializer}
import gezi.jit.NativeBackend
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.NormalityModule

/** One implementation of the narrow blocks, which a round's extractor data
  * chooses (`gezi.contest.entry.ExtractorImplementation`, mapped by
  * `gezi.contest.entry.Defaults.route`): the modules that spell a round's
  * extraction and its write-backs, and the route of the lemma rounds, whose
  * last round's extraction has its blocks compiled and run. The default is
  * `LemmaRoute`; `gezi.narrowblocks.lists.LemmaRoute` is the opt-in copy with
  * lists and booleans ([[gezi.narrowblocks.lists]]), kept beside it until the
  * copy beats it everywhere: a general improvement is opt-in by copy on write,
  * and the old version is deleted only once the new one is better everywhere.
  */
trait NarrowBlockRoute:

  /** The modules of a round's extraction and of its write-backs: the narrow
    * blocks over the natives first, then the size.
    */
  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: gezi.weakhead.ReadingConfiguration[C]
  ): Vector[NormalityModule[C]]

  /** The lemma rounds on one shared graph, then the last round's extraction
    * with its narrow blocks computed (`LemmaRoute.compiledRounds`); `encoding`
    * is the specializer of the rounds' configuration, its backend facts, which
    * a route that refines its output by them reads.
    */
  def compiledRounds[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      rounds: Vector[PreparedLemmaCompilation[C]],
      natives: NativeBackend,
      encoding: gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C]
