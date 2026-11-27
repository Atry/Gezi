package gezi.strategies

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.egraph.EGraph
import gezi.frontend.Term
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Parallel
import gezi.generatedinputs.GeneratedProperties
import gezi.saturation.End
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions

/** The law of the choice rule of the HM judgments (wren_choice_typing,
  * corpora/compiler/wren_choice_preset.lambdalattice): a program that is a
  * choice of generated numerals, `n1 + … + nk`, reaches a fixed point whose
  * choice C is judged, its class holding `C + (C ∥ (unify … + type_of C))`,
  * under the choice preset's type check, and
  * none under the Prolog backend's, whose HM judges names and applications
  * but no choice. Derived before the run: each numeral is judged by the
  * schemes of its constructors, so the choice's members are each a judged
  * term `x + (x ∥ t)`, which `unions_choice_typed` matches, a nested choice
  * after its inner one; no other lemma of either round writes a parallel over
  * a choice, the program calling no function a typed version filters. Its
  * purpose is to catch a choice rule that does not fire on the judged
  * members HM writes, and so a group of values `(m1 + … + mk) ∥ T` that HM
  * does not reach.
  */
class ChoiceTypingTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  // Measured 2026-11-24 on cores 0-5 (load 2.0 to 2.2): the property's ten samples take 13.1 s, each saturating the
  // program twice under a type check of the HM baseline (as ScottEliminationTypingTest's do); the bound is twice that.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(27, "s")

  /** The library of the choice preset, its first field with
    * occurrence_erasure (tests/library_fixtures/wren_choice_preset.lambdalattice).
    */
  private lazy val library: StandardLibrary =
    LibraryFiles.compiled("tests/library_fixtures/wren_choice_preset.lambdalattice", Vector.empty)

  /** The budget of a run, in instances. */
  private val budget = 20000

  private lazy val choiceOptions =
    BaselineRounds.saturationOptions(library, StrategyTesting.round("wren_choice_type_check"), BuiltInRule.beforeOptIn, budget)

  private lazy val backendOptions =
    BaselineRounds.saturationOptions(library, StrategyTesting.round("prolog_backend_type_check"), BuiltInRule.beforeOptIn, budget)

  /** zero and successor, by projection of tests/jit_fixtures/elimination_terms.lambdalattice. */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary.entryMembers(
      LibraryFiles.buildRoot,
      TermTable("tests/jit_fixtures/elimination_terms.lambdalattice", Vector("candidate", "list_type", "zero", "successor", "true", "boolean_not", "eliminated_as")),
      Expansions.none
    )._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => choiceOptions, _ => backendOptions, _ => terms)

  private def term(key: String): StrategyTesting.ProgramTerm =
    Term.closed(terms.getOrElse(key, throw IllegalArgumentException(s"no fixture member $key")))

  private def numeral(value: Int): StrategyTesting.ProgramTerm = (1 to value).foldLeft(term("zero"))((inner, _) => term("successor")(inner))

  /** Whether the class of the node is judged: it holds a choice of the
    * class itself and a class that holds a parallel over it, `C + (C ∥ Y)`,
    * the form of a judgment (equal to C by absorption, while `C ∥ Y` keeps a
    * class of its own).
    */
  private def judged(graph: EGraph[NoFacts.type], node: Int): Boolean =
    val root = graph.root(node)
    graph.classMembers(root).map(_.layer).exists {
      case gezi.ir.Choice(left, right) =>
        graph.root(left) == root && graph.classMembers(graph.root(right)).map(_.layer).exists {
          case Parallel(filtered, _) => graph.root(filtered) == root
          case _                     => false
        }
      case _ => false
    }

  stoppableProperty(
    "a choice of numerals is judged under the choice rule and not under the backend's type check",
    _.copy(testLimit = SuccessCount(10))
  ) { stopped =>
    for values <- Gen.int(Range.linear(0, 3)).list(Range.linear(2, 3)).forAll
    yield
      val input = StrategyTesting.programInput(library, values.map(numeral).reduceRight(_ + _))
      def saturated(options: SaturationOptions[NoFacts.type]) =
        FixpointEgraph.saturated(library.index, Vector(input), options, explained = false, StopSignal.completedWith(stopped))
      val choice = saturated(choiceOptions)
      val backend = saturated(backendOptions)
      val Vector(choiceInput) = choice.inputNodes: @unchecked
      val Vector(backendInput) = backend.inputNodes: @unchecked
      Result.all(
        List(
          Result.assert(choice.end.isInstanceOf[End.FixedPoint]).log(s"the choice run ended ${choice.end}"),
          Result.assert(backend.end.isInstanceOf[End.FixedPoint]).log(s"the backend run ended ${backend.end}"),
          Result.assert(judged(choice.graph, choiceInput)).log("the choice is not judged under the choice rule"),
          Result.assert(!judged(backend.graph, backendInput)).log("the choice is judged under the backend's type check")
        )
      )
  }
