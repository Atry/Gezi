package com.yang_bo.gezi.narrowblocks

import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.strategies.NormalityModule

/** One implementation of the narrow blocks, which a round's extractor data
  * chooses (`com.yang_bo.gezi.contest.entry.ExtractorImplementation`, mapped by
  * `com.yang_bo.gezi.contest.entry.Defaults.route`): the modules that spell a round's
  * extraction and its write-backs, and the route of the lemma rounds, whose
  * last round's extraction has its blocks compiled and run. The default is
  * `LemmaRoute`; `com.yang_bo.gezi.narrowblocks.lists.LemmaRoute` is the opt-in copy with
  * lists and booleans ([[com.yang_bo.gezi.narrowblocks.lists]]), kept beside it until the
  * copy beats it everywhere: a general improvement is opt-in by copy on write,
  * and the old version is deleted only once the new one is better everywhere.
  */
trait NarrowBlockRoute:

  /** The modules of a round's extraction and of its write-backs: the narrow
    * blocks over the natives first, then the size.
    */
  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: com.yang_bo.gezi.weakhead.ReadingConfiguration[C]
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
      encoding: com.yang_bo.gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C]
