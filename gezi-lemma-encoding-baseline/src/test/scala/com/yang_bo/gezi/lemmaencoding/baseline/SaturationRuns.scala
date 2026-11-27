package com.yang_bo.gezi.lemmaencoding.baseline

import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.orientation.LemmaSides
import com.yang_bo.gezi.orientation.OrientationCompilation
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.saturation.Run
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.standardlibrary.StandardLibrary

/** The e-graph saturated from inputs under the lemmas of knowledge modules of a
  * compiled library, through the framework's orientation compiler, index,
  * closure compilation and saturation: what the Prolog tests ran with
  * `fixpoint_egraph_run/3` and the options `lemmas(Modules)` and
  * `budget(Budget)`.
  */
object SaturationRuns:

  /** The run of the inputs, instructions of closed terms over the library's
    * instructions, under the lemmas the knowledge term writes, such as a
    * round's read off a fixture file by projection (`StandardLibrary.lemmas`,
    * read under a fresh state), with the budget in instances that change the
    * graph.
    */
  def saturated(
      library: StandardLibrary,
      knowledge: Configured[NoFacts.type],
      inputInstructions: Vector[Configured[NoFacts.type]],
      budget: Int,
      stop: StopSignal
  )(using NoFacts.type): Run[NoFacts.type] =
    val lemmas = library.index
      .enabledEquations(
        library.lemmas(knowledge, KnowledgeReading.startingState)._1
      )
      .map(BaselineLemmaEncoding.encoded(library.index, _))
    val store = library.store
    val compiled = OrientationCompilation.compiled(
      lemmas.map(lemma =>
        LemmaSides(lemma.lemma, lemma.metavariables, lemma.left, lemma.right)
      ),
      store
    )
    val program = Indexing.program(
      compiled.orientations,
      Indexing.codesMet(
        compiled.orientations,
        compiled.patternInstructions ++ inputInstructions
      )
    )
    Saturation.run(
      program,
      ClosureCompilation.compiled(program),
      BuiltInRule.beforeOptIn,
      store,
      Orientations.headArityBounds(compiled.orientations),
      compiled.patternInstructions,
      inputInstructions,
      budget,
      explained = false,
      stop
    )

  /** The layers of the live members of the class, over the roots of their
    * classes (`fixpoint_egraph_member/4`).
    */
  def classLayers(
      graph: EGraph[NoFacts.type],
      root: Int
  ): Vector[LayerWith[Int, Configured[NoFacts.type]]] =
    (0 until graph.nodeCount).toVector
      .filter(node => graph.live(node) && graph.root(node) == root)
      .map(node => graph.layer(node).map(graph.root))
