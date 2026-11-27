package gezi.strategies

import hedgehog.Gen
import hedgehog.Result
import gezi.egraph.Justification
import gezi.egraph.EGraph
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{NoinlineLeaf, Thunk}

/** The law of the abstraction rule's record (`Justification.Abstraction`), on
  * generated rounds of the higher-order saturator that opens bodies and writes
  * them back: a closure that calls K = λx. λy. x on a closed term and its
  * variable, whose body the lemma `K a b = a` rewrites, once opened, to the
  * closed term. K's first argument is closed so that the body's class does not
  * join the eigenvariable's, which would leave the eigenvariable not alone in
  * its class and block the write-back (`BodyOpening.eigenvariablesFree`).
  *
  * Purpose: catch a write-back that records another body, other eigenvariables
  * or another spelling than its own, which a trace would then replay at the
  * wrong nodes: each recorded eigenvariable is an opaque leaf alone in its
  * class, as many as the closure's holes; the recorded spelling is in the
  * recorded body's class; and the body is not the closure's class.
  */
class AbstractionRecordLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private def closed(text: String): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
      Lambdalattice.term(text)
    )(using gezi.ir.NoFacts)

  private val lemmas: Vector[LemmaSides[NoFacts.type]] = Vector(
    LemmaSides(
      LemmaIdentifier(0),
      closed("λa. λb. (λx. λy. x) a b"),
      closed("λa. λb. a")
    )
  )

  private val index: StandardLibraryIndex[NoFacts.type] = StandardLibraryIndex(
    NoFacts,
    Vector.empty,
    lemmas,
    Vector.empty,
    Vector.empty
  )

  /** The instances a round may add: the openings, write-backs and lemma
    * instances of a closure with one call of K are a handful. FIXME
    * (2026-11-13): the number is not measured yet; measure the most a
    * https://github.com/Atry/private-overlay/issues/1962 generated round adds
    * and set twice that, with the measurement here.
    */
  private val budget: Int = 16

  private val saturator: HigherOrderSaturator[NoFacts.type] =
    HigherOrderSaturator(
      SaturationOptions(
        lemmas.map(_.lemma),
        Set.empty,
        budget,
        BaselineLemmaEncoding,
        ClosureCompilation,
        StandardIndexer.of[gezi.ir.NoFacts.type],
        StandardOrientationCompiler,
        MemoRetention.Kept,
        gezi.ir.TermConstruction(gezi.ir.NoFacts)
      ),
      Some(
        LocalExtraction(
          Vector(Compression.at[gezi.ir.NoFacts.type]),
          _ => Set.empty,
          SpellingRetention.KeptWithinAPass
        )
      ),
      None,
      gezi.saturation.OpeningCriterionChoice.CallsAHead
    )

  private val closedText: Gen[String] =
    HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** A closure whose body calls K on a closed term and its variable, at the
    * head or as an argument.
    */
  private val programs: Gen[String] =
    for
      constant <- closedText
      other <- closedText
      shape <- Gen.element1(0, 1)
    yield
      if shape == 0 then s"λz. (λk. λl. k) ($constant) z"
      else s"λz. z ((λk. λl. k) ($constant) z) ($other)"

  private def holes(graph: EGraph[NoFacts.type], node: Int): Option[Int] =
    graph.layer(node) match
      case Thunk(_, holes, _) => Some(holes.size)
      case _                  => None

  stoppableProperty(
    "an abstraction's record names its own eigenvariables, body and spelling"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val graph = saturator
          .saturated(
            index,
            Vector(closed(program)),
            explained = true,
            StopSignal.completedWith(stopped)
          )
          .graph
        val records = graph.unions.collect(union =>
          union.justification match
            case Justification.Abstraction(eigenvariables, body, spelling) =>
              (union.first, eigenvariables, body, spelling)
        )
        val problems = records.flatMap(
          (closure, eigenvariables, body, spelling) =>
            Vector(
              Option.when(
                holes(graph, closure).forall(_ != eigenvariables.size)
              )(
                s"union ${closure}: ${eigenvariables.size} eigenvariables for a closure of ${holes(graph, closure)} holes"
              ),
              Option.when(
                !eigenvariables.forall(leaf =>
                  graph.classMembers(leaf).map(_.node) == Vector(leaf) && (graph
                    .layer(leaf) match
                    case NoinlineLeaf(_) => true
                    case _               => false)
                )
              )(
                s"union ${closure}: an eigenvariable of $eigenvariables is no leaf alone in its class"
              ),
              Option.when(graph.root(spelling) != graph.root(body))(
                s"union ${closure}: the spelling $spelling is not in the body's class"
              ),
              Option.when(graph.root(body) == graph.root(closure))(
                s"union ${closure}: the body is the closure's class"
              )
            ).flatten
        )
        Result
          .all(
            List(
              Result
                .assert(records.nonEmpty)
                .log("the round wrote no body back"),
              Result.assert(problems.isEmpty).log(problems.mkString("\n"))
            )
          )
          .log(s"${records.size} write-backs")
      )
  }
