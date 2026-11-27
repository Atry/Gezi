package gezi.strategies

import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BindingNormalForm
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.ir.Thunk
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** The laws of the e-graph's respelling in explanation mode: a saturation in
  * explanation mode and the same saturation without it agree apart from the
  * made duplicates, every thunk with holes is made in the front end's spelling
  * in both, and making a thunk that is not its own spelling twice, or once as
  * it is and once as its spelling, gives one node. The replay of the
  * explanation-mode graph's proofs is `RewriteTraceLawTest`'s.
  *
  * The inputs hold a β residual that is not its own spelling
  * (`ResidualPrograms`), so that every sample respells; the laws assert it, so
  * that a generator that drifts empties no law silently.
  *
  * Purpose: catch a respelling that explanation mode does differently (a made
  * duplicate of a respelled layer born outside its class, a lookup of the
  * made-nodes table by the layer before its respelling), which would change the
  * classes a proof reads, or a layer made in another spelling, which no index
  * orientation matches.
  */
class ExplanationRespellingLawTest extends GeneratedProperties:

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

  private val saturator: StandardSaturator[NoFacts.type] = StandardSaturator(
    SaturationOptions(
      lemmas.map(_.lemma),
      BuiltInRule.beforeOptIn,
      16,
      BaselineLemmaEncoding,
      ClosureCompilation,
      StandardIndexer.of[gezi.ir.NoFacts.type],
      StandardOrientationCompiler,
      MemoRetention.Kept,
      gezi.ir.TermConstruction(gezi.ir.NoFacts)
    )
  )

  private def counts(graph: EGraph[NoFacts.type]): Vector[Long] =
    val live = graph.liveNodes
    Vector(
      live.size.toLong,
      live.map(_.root).distinct.size.toLong,
      graph.joiningUnionCount.toLong,
      graph.respellingCounts.layersRespelled
    )

  private def unspelled(graph: EGraph[NoFacts.type]): Vector[Int] =
    (0 until graph.nodeCount).toVector.filter(node =>
      graph.madeLayer(node) match
        case Thunk(code, holes, fillings) if holes.nonEmpty =>
          BindingNormalForm.respelled(code, holes, fillings.size).nonEmpty
        case _ => false
    )

  property(
    "a saturation with and without explanation agrees apart from its made duplicates"
  ) {
    for
      thunk <- ResidualPrograms.thunks.forAll
      argument <- HoasGenerators.instruction.forAll
    yield
      // The residual itself and the application that leaves it: the graph respells the one and the β rule the other.
      val program = NoFacts.choice(
        ResidualPrograms.residual(thunk, argument),
        NoFacts.application(thunk, argument)
      )
      def graph(explained: Boolean): EGraph[NoFacts.type] =
        saturator
          .saturated(
            index,
            Vector(program),
            explained,
            StopSignal.completedWith(scala.concurrent.Future.never)
          )
          .graph
      val explained = graph(true)
      val plain = graph(false)
      Result.all(
        List(
          Result
            .assert(explained.respellingCounts.layersRespelled > 0)
            .log("the input respells nothing: the generator drifted"),
          Result
            .diff(counts(explained), counts(plain))(_ == _)
            .log(
              "live nodes, classes, joining unions, layers respelled: explained, then plain"
            ),
          Result
            .assert(unspelled(explained).isEmpty)
            .log(s"explained: unspelled made layers ${unspelled(explained)}"),
          Result
            .assert(unspelled(plain).isEmpty)
            .log(s"plain: unspelled made layers ${unspelled(plain)}")
        )
      )
  }

  property(
    "a thunk made twice as it is, or once as it is and once as its spelling, is one node"
  ) {
    for
      thunk <- ResidualPrograms.thunks.forAll
      argument <- HoasGenerators.instruction.forAll
    yield
      val residual = ResidualPrograms.residual(thunk, argument)
      residual.layer match
        case Thunk(code, holes, fillings) if holes.nonEmpty =>
          BindingNormalForm.respelled(code, holes, fillings.size) match
            case Some((spelledCode, spelledHoles, overPlaceholders)) =>
              // The spelling's fillings are codes over the slots of the thunk's own fillings: their instances.
              val spelling = NoFacts.thunkOrInstance(
                spelledCode,
                spelledHoles,
                overPlaceholders.map(filling =>
                  NoFacts.instance(filling, fillings)
                )
              )
              val empty = EGraph.empty(
                Store(Set.empty, gezi.ir.TermConstruction(gezi.ir.NoFacts)),
                Map.empty,
                explained = true
              )
              val (once, first) = empty.instructionAdded(residual)
              val (twice, second) = once.instructionAdded(residual)
              val (_, third) = twice.instructionAdded(spelling)
              Result
                .diff(
                  Vector(first, second, third),
                  Vector(first, first, first)
                )(_ == _)
                .log(s"$residual and its spelling $spelling")
            case None =>
              Result.failure.log(
                s"the residual $residual is its own spelling: the generator drifted"
              )
        case other =>
          Result.failure.log(s"no residual thunk with holes: $other")
  }
