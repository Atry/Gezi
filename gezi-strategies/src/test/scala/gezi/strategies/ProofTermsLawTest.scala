package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.proofs.OpentheoryArticle
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** The law of the proof's terms (`GraphProof`), each node's term the term
  * made (`EGraph.madeLayer`), on four families of generated rounds: the
  * baseline's first-order rounds, the higher-order saturator's, and the
  * higher-order saturator's that open bodies and write them back, with the
  * β rule off and on.
  *
  * Purpose: catch a proof term that holds an eigenvariable outside its
  * opening: a written-back thunk whose term holds an eigenvariable of the
  * opening it was written back from (the term of a node made over a class
  * root instead of the node made, the defect of terms read over roots), or
  * an input's term that holds any eigenvariable.
  */
class ProofTermsLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private def closed(text: String): Configured[NoFacts.type] = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](Lambdalattice.term(text))(using gezi.ir.NoFacts)

  private def equation(number: Int, left: String, right: String): LemmaSides[NoFacts.type] =
    LemmaSides(LemmaIdentifier(number), closed(left), closed(right))

  private def index(lemmas: Vector[LemmaSides[NoFacts.type]]): StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(NoFacts, Vector.empty, lemmas, Vector.empty, Vector.empty)

  private val firstOrderLemmas = Vector(
    equation(0, "λa. λb. (a + b)", "λa. λb. (b + a)"),
    equation(1, "λa. λb. λc. ((a + b) + c)", "λa. λb. λc. (a + (b + c))"),
    equation(2, "λa. (a + a)", "λa. a"),
    equation(3, "λa. λb. (λx. λy. x) a b", "λa. λb. a")
  )
  private val higherOrderLemmas = Vector(equation(0, "λk. λa. (λx. λz. k x) a", "λk. λa. λz. k a"))
  private val openingLemmas = Vector(equation(0, "λa. λb. (λx. λy. x) a b", "λa. λb. a"))

  /** The instances a round may add: the budgets of `RewriteTraceLawTest`'s
    * rounds of the same families. FIXME (2026-11-14): the write-back https://github.com/Atry/private-overlay/issues/1962
    * families' 16 is not measured; measure the most a generated round adds
    * and set twice that, with the measurement.
    */
  private def options(lemmas: Vector[LemmaSides[NoFacts.type]], rules: Set[BuiltInRule], budget: Int): SaturationOptions[NoFacts.type] =
    SaturationOptions(lemmas.map(_.lemma), rules, budget, BaselineLemmaEncoding, ClosureCompilation, StandardIndexer.of[gezi.ir.NoFacts.type], StandardOrientationCompiler, MemoRetention.Kept, gezi.ir.TermConstruction(gezi.ir.NoFacts))

  private val closedText: Gen[String] = HoasGenerators.closedTerm.map(LambdalatticeText.text)

  private val firstOrderPrograms: Gen[String] =
    Gen.choice1(
      closedText.list(Range.linear(2, 4)).map(_.map(member => s"($member)").mkString(" + ")),
      for
        context <- closedText
        first <- closedText
        second <- closedText
      yield s"($context) + (λk. λl. k) ($first) ($second)"
    )

  private val higherOrderPrograms: Gen[String] =
    for
      constant <- closedText
      argument <- closedText
    yield s"(λx. λz. x ($constant)) ($argument)"

  /** A closure whose body calls K on a closed term and its variable: at the
    * head, as an argument, or twice applied to itself, whose opening makes a
    * layer over the body's nodes that the closed write-back makes again (the
    * witness of a term read over the first maker's nodes).
    */
  private val openingPrograms: Gen[String] =
    for
      constant <- closedText
      other <- closedText
      shape <- Gen.element1(0, 1, 2)
    yield shape match
      case 0 => s"λz. (λk. λl. k) ($constant) z"
      case 1 => s"λz. z ((λk. λl. k) ($constant) z) ($other)"
      case _ => s"λz. (λk. λl. k) ($constant) z ((λk. λl. k) ($constant) z)"

  private val writeBack = Some(LocalExtraction(Vector(Compression.at[gezi.ir.NoFacts.type]), _ => Set.empty, SpellingRetention.KeptWithinAPass))

  private def isEigenvariable(instruction: Configured[NoFacts.type]): Boolean =
    instruction.opaque && instruction.toString.contains("eigenvariable")

  private def holds(term: Configured[NoFacts.type], leaves: Set[Configured[NoFacts.type]]): Boolean =
    leaves.contains(term) || (!term.opaque && term.layer.children.exists(holds(_, leaves)))

  private def holdsEigenvariable(term: Configured[NoFacts.type]): Boolean =
    isEigenvariable(term) || (!term.opaque && term.layer.children.exists(holdsEigenvariable))

  /** The problems of a round's graph: written-back thunks whose terms hold
    * their own eigenvariables, and an input term that holds any.
    */
  private def problems(
      lemmas: Vector[LemmaSides[NoFacts.type]],
      saturator: Saturator[NoFacts.type],
      graph: EGraph[NoFacts.type],
      inputTerm: Configured[NoFacts.type],
      input: Int
  ): Vector[String] =
    val libraryIndex = index(lemmas)
    val proof = GraphProof.proof(graph, Vector((inputTerm, inputTerm)), saturator.lemmas(libraryIndex))
    val terms = OpentheoryArticle.derivation(libraryIndex, inputTerm, inputTerm, proof).nodeTerm
    val escaped = graph.unions.collect(union =>
      union.justification match
        case Justification.Abstraction(eigenvariables, _, _) => (union.second, eigenvariables.map(terms).toSet)
    ).collect { case (written, leaves) if holds(terms(written), leaves) => s"the written-back thunk ${terms(written)} holds $leaves" }
    val inputs = Option.when(holdsEigenvariable(terms(input)))(s"the input's term ${terms(input)} holds an eigenvariable")
    escaped ++ inputs

  private def law(lemmas: Vector[LemmaSides[NoFacts.type]], saturator: Saturator[NoFacts.type], programs: Gen[String], stop: StopSignal) =
    programs.forAllWithLog(identity).map(program =>
      val input = closed(program)
      val run = saturator.saturated(index(lemmas), Vector(input), explained = true, stop)
      val Vector(inputNode) = run.inputNodes: @unchecked
      val found = problems(lemmas, saturator, run.graph, input, inputNode)
      Result.assert(found.isEmpty).log(found.mkString("\n"))
    )

  stoppableProperty("first-order rounds: no proof term holds an eigenvariable outside its opening") { stopped =>
    law(firstOrderLemmas, StandardSaturator(options(firstOrderLemmas, BuiltInRule.beforeOptIn, 24)), firstOrderPrograms, StopSignal.completedWith(stopped))
  }

  stoppableProperty("higher-order rounds: no proof term holds an eigenvariable outside its opening") { stopped =>
    law(higherOrderLemmas, HigherOrderSaturator(options(higherOrderLemmas, Set.empty, 8), None, None, gezi.saturation.OpeningCriterionChoice.CallsAHead), higherOrderPrograms, StopSignal.completedWith(stopped))
  }

  stoppableProperty("write-back rounds: no proof term holds an eigenvariable outside its opening") { stopped =>
    law(openingLemmas, HigherOrderSaturator(options(openingLemmas, Set.empty, 16), writeBack, None, gezi.saturation.OpeningCriterionChoice.CallsAHead), openingPrograms, StopSignal.completedWith(stopped))
  }

  stoppableProperty("write-back rounds with the β rule: no proof term holds an eigenvariable outside its opening") { stopped =>
    law(openingLemmas, HigherOrderSaturator(options(openingLemmas, BuiltInRule.beforeOptIn, 16), writeBack, None, gezi.saturation.OpeningCriterionChoice.CallsAHead), openingPrograms, StopSignal.completedWith(stopped))
  }
