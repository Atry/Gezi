package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.Apply
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTable
import com.yang_bo.gezi.weakhead.Expansions

/** The law of the candidacies from eliminations (wren_scott_elimination,
  * corpora/compiler/wren_elimination_preset.lambdalattice): a closure that
  * eliminates its parameter as a list, `λxs. xs a (λh t. b)`, with no list
  * built anywhere in the program, reaches a fixed point holding a list
  * candidacy under the elimination preset's type check whenever b types the
  * head h as a representation's value (`successor h`, `boolean_not h`): a list
  * candidacy reads its head as an item candidate (prolog_backend_shapes'
  * `shapes_list_candidate`). Where b does not type the head, the elimination is
  * ambiguous (the cons arm also reads as the unary naturals' one field
  * returning a function, whose field candidacy can make the head an item
  * candidate), and a list candidacy may or may not be there: an ambiguous
  * typing keeps every reading as a candidate, refuted and repelled where the
  * type's own structure contradicts it, so the law asks nothing there. Under
  * the Prolog backend's type check, whose application rule gives the parameter
  * a function type and whose candidacies are read from constructors only, it
  * holds none. Its purpose is to catch an elimination lemma that does not fire
  * on its shape, and a candidacy that does not reach through the mark
  * `eliminated_as`.
  */
class ScottEliminationTypingTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private type Program = TermOf[Configured[NoFacts.type]]

  // Measured 2026-11-23 on cores 4-7 (load 3 to 4): the property's ten samples take about 8 s, each saturating the
  // program twice under a type-check round of the HM baseline; the bound is twice that. The two runs a sample makes
  // are the law's two halves, and ten samples reach the arms' ten combinations.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(16, "s")

  /** The library of the elimination preset, its first field with
    * occurrence_erasure
    * (tests/library_fixtures/wren_elimination_preset.lambdalattice).
    */
  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(
      "tests/library_fixtures/wren_elimination_preset.lambdalattice",
      Vector.empty
    )

  /** The budget of a run, in instances. */
  private val budget = 20000

  private lazy val eliminationOptions =
    BaselineRounds.saturationOptions(
      library,
      StrategyTesting.round("wren_elimination_type_check"),
      BuiltInRule.beforeOptIn,
      budget
    )

  private lazy val applicationOptions =
    BaselineRounds.saturationOptions(
      library,
      StrategyTesting.round("prolog_backend_type_check"),
      BuiltInRule.beforeOptIn,
      budget
    )

  /** candidate, list_type, zero and true, by projection of
    * tests/jit_fixtures/elimination_terms.lambdalattice.
    */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        LibraryFiles.buildRoot,
        TermTable(
          "tests/jit_fixtures/elimination_terms.lambdalattice",
          Vector(
            "candidate",
            "list_type",
            "zero",
            "successor",
            "true",
            "boolean_not",
            "eliminated_as"
          )
        ),
        Expansions.none
      )
      ._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => eliminationOptions,
      _ => applicationOptions,
      _ => terms
    )

  private def term(key: String): Program =
    Term.closed(
      terms.getOrElse(
        key,
        throw IllegalArgumentException(s"no fixture member $key")
      )
    )

  /** What the nil arm gives: a constant. */
  private enum NilArm:
    case Zero
    case True

  /** What the cons arm gives of its head h and tail t: `successor h` and
    * `boolean_not h` type the head as a natural and a boolean, h, t and zero do
    * not.
    */
  private enum ConsArm:
    case Successor
    case Not
    case Head
    case Tail
    case Zero

  extension (arm: ConsArm)
    private def typesTheHead: Boolean =
      arm == ConsArm.Successor || arm == ConsArm.Not

  private val nilArm: Gen[NilArm] = Gen.element1(NilArm.Zero, NilArm.True)
  private val consArm: Gen[ConsArm] = Gen.element1(
    ConsArm.Successor,
    ConsArm.Not,
    ConsArm.Head,
    ConsArm.Tail,
    ConsArm.Zero
  )

  private def program(nil: NilArm, cons: ConsArm): Program =
    val constant = nil match
      case NilArm.Zero => term("zero")
      case NilArm.True => term("true")
    Term.λ(list =>
      list(constant)(
        Term.λ(head =>
          Term.λ(tail =>
            cons match
              case ConsArm.Successor => term("successor")(head)
              case ConsArm.Not       => term("boolean_not")(head)
              case ConsArm.Head      => head
              case ConsArm.Tail      => tail
              case ConsArm.Zero      => term("zero")
          )
        )
      )
    )

  /** Whether a class of the graph holds `candidate (list_type e) t`. */
  private def listCandidacy(graph: EGraph[NoFacts.type]): Boolean =
    val candidate = graph.instructionNode(terms("candidate")).map(graph.root)
    val listType = graph.instructionNode(terms("list_type")).map(graph.root)
    def applications(node: Int): Vector[(Int, Int)] =
      graph.classMembers(node).map(_.layer).collect {
        case Apply(function, argument) =>
          (graph.root(function), graph.root(argument))
      }
    (candidate, listType) match
      case (Some(candidateClass), Some(listTypeClass)) =>
        (0 until graph.nodeCount).exists(node =>
          graph.root(node) == node && applications(node).exists((partial, _) =>
            applications(partial).exists((head, criterion) =>
              head == candidateClass && applications(criterion).exists(
                (criterionHead, _) => criterionHead == listTypeClass
              )
            )
          )
        )
      case _ => false

  stoppableProperty(
    "a closure that eliminates its parameter as a list, its head typed, gets a list candidacy from its eliminations alone",
    _.copy(testLimit = SuccessCount(10))
  ) { stopped =>
    for
      nil <- nilArm.forAll
      cons <- consArm.forAll
    yield
      val input = StrategyTesting.programInput(library, program(nil, cons))
      def saturated(options: SaturationOptions[NoFacts.type]) =
        FixpointEgraph.saturated(
          library.index,
          Vector(input),
          options,
          explained = false,
          StopSignal.completedWith(stopped)
        )
      val elimination = saturated(eliminationOptions)
      val application = saturated(applicationOptions)
      Result.all(
        List(
          Result
            .assert(elimination.end.isInstanceOf[End.FixedPoint])
            .log(s"the elimination run ended ${elimination.end}"),
          Result
            .assert(application.end.isInstanceOf[End.FixedPoint])
            .log(s"the application run ended ${application.end}"),
          Result
            .assert(!cons.typesTheHead || listCandidacy(elimination.graph))
            .log(
              "no list candidacy under the elimination preset, though the head is typed"
            ),
          Result
            .assert(!listCandidacy(application.graph))
            .log("a list candidacy under the application rule")
        )
      )
  }

  /** The law that an ambiguous elimination keeps every reading. In
    * `λxs. xs zero (λh t. h)` the cons arm, a function of two fields, also
    * reads as one field returning a function, so the chain has both the lists'
    * shape and the unary naturals' (two arms, the second of one field). Derived
    * before the run from the elimination lemmas: under the elimination preset's
    * type check, both mark the parameter's type, and the binary naturals'
    * lemma, which needs three arms, does not, so the graph holds exactly two
    * `eliminated_as` marks over two distinct structures. Its purpose is to
    * catch a change that resolves a typing ambiguity by dropping a reading: an
    * ambiguous typing keeps every reading as a candidate, refuted by the type's
    * own structure and repelled at the call where it fails, never only one.
    */
  stoppableTest(
    "an ambiguous elimination keeps both readings, the lists' and the unary naturals'"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val program =
      Term.λ(list => list(term("zero"))(Term.λ(head => Term.λ(_ => head))))
    val input = StrategyTesting.programInput(library, program)
    val graph = FixpointEgraph
      .saturated(
        library.index,
        Vector(input),
        eliminationOptions,
        explained = false,
        stop
      )
      .graph
    val mark = graph
      .instructionNode(terms("eliminated_as"))
      .map(graph.root)
      .getOrElse(fail("the graph holds no eliminated_as"))
    val structures = (0 until graph.nodeCount).toVector
      .collect(
        Function.unlift(node =>
          graph.layer(node) match
            case Apply(partial, structure) =>
              graph
                .classMembers(graph.root(partial))
                .map(_.layer)
                .collectFirst {
                  case Apply(head, _) if graph.root(head) == mark =>
                    graph.root(structure)
                }
            case _ => None
        )
      )
      .distinct
    assertEquals(structures.size, 2, s"the structures marked: $structures")
  }
