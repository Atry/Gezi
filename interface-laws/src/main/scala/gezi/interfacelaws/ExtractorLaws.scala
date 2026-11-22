package gezi.interfacelaws

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.MemoRetention
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.BuiltInRule
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.jit.DeBruijnTermAsTerm
import gezi.jit.JitTesting
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.standardlibrary.SplitMix
import gezi.strategies.BaselineRounds
import gezi.strategies.Extractor
import gezi.strategies.SaturationOptions
import gezi.strategies.StandardSaturator
import gezi.strategies.StrategyTesting
import gezi.ir.NoinlineLeaf

/** The laws of the extraction interface `Extractor`, run on any
  * implementation: a suite that extends this class with the extractor checks
  * it ([[gezi.interfacelaws]]). The graphs are the baseline saturator's runs of
  * generated closed terms with choices and parallels, put through the front
  * end with the occurrence tagging, under the native route's library, the
  * Prolog backend's preset with closure_application and occurrence_erasure
  * (`ExtractorLaws.knowledgeFile`), and a generated budget. The tagging is what
  * makes the runs merge: MEASURED 2026-11-03 on 200 single terms of about
  * 12 nodes at budget 200, untagged terms under closure_application merged
  * no class in any run, and tagged ones under the native route's knowledge
  * of that date (its six knowledge files, before the backend's preset)
  * merged classes in all 200. (1) Each input has one output, and each
  * output is spelled in its input's class (`ExtractorLaws.spelledIn`): the
  * extractor answers a term the graph proves equal to its input, which makes a
  * round sound. (2) On a run with no knowledge module, where no lemma
  * instance merges two classes, each output is its input. A run of budget 0
  * is not such a run: the saturation adds one instance before it reads the
  * budget (MEASURED 2026-11-03: every tagged term above ended
  * `BudgetExhausted(1)` at budget 0, its graph one class merged). Their
  * purpose is to catch an extractor that answers a term of another class (an
  * unsound rewrite), drops or reorders an output, or changes a term the
  * saturation left alone.
  */
abstract class ExtractorLaws(extractor: Extractor) extends GeneratedProperties:

  private lazy val library = StrategyTesting.compiled(ExtractorLaws.knowledgeFile)

  private def inputs: Gen[Vector[Instruction]] =
    Gen
      .long(Range.linear(0L, Long.MaxValue))
      .list(Range.linear(1, 4))
      .map(_.toVector.map(seed =>
        StrategyTesting.programInput(library, DeBruijnTermAsTerm.term(JitTesting.randomLatticeApplication(12, SplitMix(seed))._1))
      ))

  /** The lemmas of the knowledge of the runs, read once: the knowledge of
    * the runs is the library's own (`ExtractorLaws.knowledgeFile`), so its
    * lemmas are every lemma the library holds, read off its index in the
    * order of their numbers, as `StandardLibrary.lemmas` gives a knowledge
    * term's.
    */
  private lazy val knowledgeLemmas: Vector[LemmaIdentifier] =
    library.index.lemmaSides.map(_.lemma).distinct.sortBy(_.number)

  private def run(inputs: Vector[Instruction], lemmas: Vector[LemmaIdentifier], budget: Int, stop: StopSignal): Run =
    StandardSaturator(
      SaturationOptions(
        lemmas,
        BuiltInRule.all,
        budget,
        BaselineRounds.modules.lemmaEncoding,
        BaselineRounds.modules.backend,
        BaselineRounds.modules.indexer,
        BaselineRounds.modules.orientationCompiler,
        MemoRetention.Kept
      )
    ).saturated(library.index, inputs, explained = false, stop)

  stoppableProperty("each input has one output, in the input's class") { stopped =>
    for
      written <- inputs.forAll
      budget <- Gen.int(Range.linear(0, ExtractorLaws.largestBudget)).forAll
    yield
      val saturated = run(written, knowledgeLemmas, budget, StopSignal.completedWith(stopped))
      val outputs = extractor.extracted(library.index, saturated.graph, saturated.inputNodes, written, StopSignal.completedWith(stopped))
      Result.all(
        Result.diff(outputs.length, written.length)(_ == _) ::
          outputs.zip(saturated.inputNodes).toList.map((output, inputNode) =>
            Result.assert(ExtractorLaws.spelledIn(saturated.graph, output, saturated.graph.root(inputNode)))
              .log(s"output $output, run ended ${saturated.end}")
          )
      )
  }

  stoppableProperty("on a run with no knowledge module each output is its input") { stopped =>
    for written <- inputs.forAll
    yield
      val saturated = run(written, Vector.empty, ExtractorLaws.largestBudget, StopSignal.completedWith(stopped))
      Result.diff(extractor.extracted(library.index, saturated.graph, saturated.inputNodes, written, StopSignal.completedWith(stopped)), written)(_ == _)
  }

object ExtractorLaws:

  /** The file of the knowledge of the runs, relative to Gezi's root:
    * the native route's library, the choice of the Prolog backend's preset
    * (its backend and the native typing of the types it represents) with
    * closure_application and occurrence_erasure, the one field of the file's
    * tuple. Native typing is enabled through the preset only.
    */
  val knowledgeFile: String = "tests/library_fixtures/presets.lambdalattice"

  /** The largest budget of a run, in instances. */
  val largestBudget: Int = 200

  /** Whether the graph proves the term equal to the class, read without
    * changing the graph: the term's instruction has a node in the class, or some
    * live node whose root is the class (as `Extraction.productions` reads
    * the graph) has one of the term's layers, each child of the node in the
    * class its counterpart in the term is spelled in. A noinline term has
    * two layers: the leaf the graph makes for it and, when it is not opaque,
    * its own.
    *
    * Adding the term to the graph and comparing roots is not this test when
    * the run ended on its budget, for two reasons, each MEASURED 2026-11-03
    * at seed 30267446634265:
    * - The unions, merges and deltas still pending leave the signatures
    *   stale, so a spelled layer the class holds is not found and the term
    *   is added as new nodes in a class of its own: at budget 3 and again 39
    *   the output read off the input's class 31 was added as node 118 over a
    *   new node 117.
    * - A spelled thunk can be, by hash consing, a noinline library name,
    *   which the graph adds as its leaf, in the leaf's class: at 3,000 inputs
    *   and budget 3, the extractor spelled the class 39 by its node
    *   `Thunk(code, Vector(Ignored), Vector(24))`, an instruction equal to a
    *   noinline name whose leaf is node 13, of class 13, a class the run had
    *   not yet united with 39.
    */
  def spelledIn(graph: EGraph, term: Instruction, classRoot: Int): Boolean =
    val nodesByRoot = graph.liveNodes.groupBy(_.root)
    def layers(term: Instruction): Vector[Layer[Instruction]] =
      val leaf = if graph.store.noinline.contains(term) then Vector(NoinlineLeaf(term)) else Vector.empty
      if term.opaque then leaf else leaf :+ term.layered
    def spelled(term: Instruction, classRoot: Int): Boolean =
      graph.instructionNode(term).exists(node => graph.root(node) == classRoot) ||
        layers(term).exists(layer =>
          nodesByRoot.getOrElse(classRoot, Vector.empty).exists(live =>
            live.layer.map(_ => ()) == layer.map(_ => ()) &&
            live.layer.children.lazyZip(layer.children).forall((child, childTerm) => spelled(childTerm, child))
          )
        )
    spelled(term, classRoot)
