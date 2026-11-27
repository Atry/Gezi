package gezi.lemmaencoding.baseline

import gezi.saturation.StopSignal
import gezi.ematching.closures.ClosureCompilation
import gezi.egraph.EGraph
import gezi.ematching.indexing.Indexing
import gezi.orientation.LemmaSides
import gezi.orientation.OrientationCompilation
import gezi.orientation.Orientations
import gezi.saturation.Run
import gezi.saturation.Saturation
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.LayerWith
import gezi.ir.NoFacts
import gezi.knowledgereading.KnowledgeReading
import gezi.standardlibrary.StandardLibrary

/** The e-graph saturated from inputs under the lemmas of knowledge modules
  * of a compiled library, through the framework's orientation compiler, index,
  * closure compilation and saturation: what the Prolog tests ran with
  * `fixpoint_egraph_run/3` and the options `lemmas(Modules)` and
  * `budget(Budget)`.
  */
object SaturationRuns:

  /** The run of the inputs, instructions of closed terms over the library's
    * instructions, under the lemmas the knowledge term writes, such as a round's
    * read off a fixture file by projection (`StandardLibrary.lemmas`, read
    * under a fresh state), with the budget in instances that change the
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
      .enabledEquations(library.lemmas(knowledge, KnowledgeReading.startingState)._1)
      .map(BaselineLemmaEncoding.encoded(library.index, _))
    val store = library.store
    val compiled = OrientationCompilation.compiled(
      lemmas.map(lemma => LemmaSides(lemma.lemma, lemma.metavariables, lemma.left, lemma.right)),
      store
    )
    val program = Indexing.program(
      compiled.orientations,
      Indexing.codesMet(compiled.orientations, compiled.patternInstructions ++ inputInstructions)
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
  def classLayers(graph: EGraph[NoFacts.type], root: Int): Vector[LayerWith[Int, Configured[NoFacts.type]]] =
    (0 until graph.nodeCount).toVector
      .filter(node => graph.live(node) && graph.root(node) == root)
      .map(node => graph.layer(node).map(graph.root))
