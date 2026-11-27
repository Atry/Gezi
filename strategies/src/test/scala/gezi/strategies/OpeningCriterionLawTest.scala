package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import snapshot4s.generated.snapshotConfig
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.saturation.BodyOpening
import gezi.saturation.End
import gezi.saturation.OpeningCriterion
import gezi.saturation.OpeningCriterionChoice
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** The laws of the narrower opening criterion
  * (`OpeningCriterion.CallsAHeadWithMatchingArguments`), a lossy option beside
  * the default, on generated closures that call a head `H` with a first
  * argument and a second one of a generated kind: the closure's own variable, a
  * closed choice, a closed parallel, another closed term, a part of the code
  * that holds the variable, a closed application that reduces to a choice, or
  * the variable beside a part of the body that unites its class with a
  * structured term (an identity applied to it, under β; the variable chosen
  * with itself, under an idempotence lemma).
  *
  *   1. The closures it opens are among those `CallsAHead` opens, for a
  *      generated left side's spine of the head: the criterion is the default's
  *      conjoined with its own test, which this law keeps so.
  *   2. A round under it adds no more instances than the same round under the
  *      default, for a generated left side's spine of the head and an
  *      idempotence lemma `M + M = M`, whose left side heads no spine with a
  *      name, where both reach their fixed point.
  *   3. A snapshot records the instances of the two rounds on the shapes the
  *      criterion may lose, read from the code (`OpeningCriterion`); on its
  *      samples the two counts are equal (2026-11-21).
  *
  * Purpose: catch a criterion that opens a closure the default does not, or
  * that opens more than the default in effect (an instance the default's round
  * does not add); and show, on the witnesses, what the option gives up for the
  * closures it does not open.
  */
class OpeningCriterionLawTest extends GeneratedProperties with SeededSnapshots:

  private given NoFacts.type = NoFacts

  private def closed(text: String): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
      Lambdalattice.term(text)
    )(using gezi.ir.NoFacts)

  /** The head: a closed term no generated program spells otherwise. */
  private val headText = "(λh1. λh2. λh3. λh4. h4 h3 h2 h1)"
  private val head = closed(headText)

  /** The right side's head, which no program holds, so that the backward
    * orientation matches nothing in a body.
    */
  private val markerText = "(λm1. λm2. λm3. λm4. λm5. m5 m1 m2 m3 m4)"

  /** One argument of the head's spine in a left side: its text over its own
    * metavariables (`binders`), and as a pattern.
    */
  private final case class SpineArgument(
      text: String,
      binders: Vector[String],
      pattern: Pattern[NoFacts.type]
  )

  private def spineArgument(kind: Int, position: Int): SpineArgument =
    val (first, second) = (s"a$position", s"b$position")
    kind match
      case 0 => SpineArgument(first, Vector(first), Pattern.Metavariable(0))
      case 1 =>
        SpineArgument(
          s"($first + $second)",
          Vector(first, second),
          Pattern.Choice(Pattern.Metavariable(1), Pattern.Metavariable(2))
        )
      case 2 =>
        SpineArgument(
          s"($first ∥ $second)",
          Vector(first, second),
          Pattern.Parallel(Pattern.Metavariable(1), Pattern.Metavariable(2))
        )
      case _ =>
        SpineArgument(
          s"($first $second)",
          Vector(first, second),
          Pattern.Apply(Pattern.Metavariable(1), Pattern.Metavariable(2))
        )

  /** A spine of the head's two arguments as a left side may write it: each
    * argument a metavariable, a choice, a parallel or an application.
    */
  private val spines: Gen[Vector[SpineArgument]] =
    for
      first <- Gen.int(Range.constant(0, 3))
      second <- Gen.int(Range.constant(0, 3))
    yield Vector(spineArgument(first, 0), spineArgument(second, 1))

  /** The lemma `H arguments = M binders`, its left side the spine, its right
    * side the marker applied to the spine's metavariables and identities after
    * them.
    */
  private def headLemma(
      spine: Vector[SpineArgument]
  ): LemmaSides[NoFacts.type] =
    val binders = spine.flatMap(_.binders)
    val lambdas = binders.map(binder => s"λ$binder.").mkString(" ")
    val markerArguments =
      (binders ++ Vector.fill(4 - binders.size)("(λu. u)")).mkString(" ")
    LemmaSides(
      LemmaIdentifier(0),
      closed(s"$lambdas $headText ${spine.map(_.text).mkString(" ")}"),
      closed(s"$lambdas $markerText $markerArguments")
    )

  private val idempotence =
    LemmaSides(LemmaIdentifier(1), closed("λm. (m + m)"), closed("λm. m"))

  private def index(
      lemmas: Vector[LemmaSides[NoFacts.type]]
  ): StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      lemmas,
      Vector.empty,
      Vector.empty
    )

  /** The round's instances: twice the most a generated program's round took
    * under the default (MEASURED 2026-11-21, the second law's run of 20 samples
    * at a budget of 64: 0 instances 14 times, 2 five times, 4 once, every round
    * at its fixed point, the narrower round's count the same on every sample).
    */
  private val budget = 8

  private def options(
      lemmas: Vector[LemmaSides[NoFacts.type]]
  ): SaturationOptions[NoFacts.type] =
    SaturationOptions(
      lemmas.map(_.lemma),
      BuiltInRule.beforeOptIn,
      budget,
      BaselineLemmaEncoding,
      ClosureCompilation,
      StandardIndexer.of[gezi.ir.NoFacts.type],
      StandardOrientationCompiler,
      MemoRetention.Kept,
      gezi.ir.TermConstruction(gezi.ir.NoFacts)
    )

  private val closedText: Gen[String] =
    HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** `λz. H first second`, the second argument of one of eight kinds, the last
    * two beside a part of the body that unites z's class.
    */
  private val programs: Gen[String] =
    for
      first <- closedText
      left <- closedText
      right <- closedText
      kind <- Gen.element1(0, 1, 2, 3, 4, 5, 6, 7)
    yield kind match
      case 0 => s"λz. $headText ($first) z"
      case 1 => s"λz. $headText ($first) (($left) + ($right))"
      case 2 => s"λz. $headText ($first) (($left) ∥ ($right))"
      case 3 => s"λz. $headText ($first) ($left)"
      case 4 => s"λz. $headText ($first) (z + ($right))"
      case 5 => s"λz. $headText ($first) ((λw. w) (($left) + ($right)))"
      case 6 => s"λz. (((λw. w) z) + $headText ($first) z)"
      case _ => s"λz. ((z + z) ∥ $headText ($first) z)"

  private val writeBack = Some(
    LocalExtraction(
      Vector(Compression.at[gezi.ir.NoFacts.type]),
      _ => Set.empty,
      SpellingRetention.KeptWithinAPass
    )
  )

  property(
    "the closures the narrower criterion opens are among those the default opens"
  ) {
    for
      program <- programs.forAllWithLog(identity)
      spine <- spines.forAll
    yield
      val (graph, _) = EGraph
        .empty(
          Store(Set.empty, gezi.ir.TermConstruction(gezi.ir.NoFacts)),
          Map.empty,
          explained = false
        )
        .instructionAdded(closed(program))
      val heads = Map(head -> 2)
      val scope =
        BodyOpening.classesUnder(graph, graph.liveNodes.map(_.root), Set.empty)
      def openedClosures(criterion: OpeningCriterion[NoFacts.type]): Set[Int] =
        BodyOpening
          .opened(graph, Vector.empty, 8, scope, heads, Set.empty, criterion)
          ._2
          .map(opening => graph.root(opening.closure))
          .toSet
      val narrower = openedClosures(
        OpeningCriterion.CallsAHeadWithMatchingArguments(
          Map(head -> Vector(spine.map(_.pattern)))
        )
      )
      val default =
        openedClosures(OpeningCriterion.CallsAHead[gezi.ir.NoFacts.type]())
      Result
        .assert(narrower.subsetOf(default))
        .log(s"opened by the narrower criterion only: ${narrower -- default}")
  }

  /** The instances of the round under the choice, when it reaches its fixed
    * point.
    */
  private def instances(
      lemmas: Vector[LemmaSides[NoFacts.type]],
      program: String,
      choice: OpeningCriterionChoice,
      stop: StopSignal
  ): Option[Int] =
    val run =
      HigherOrderSaturator(options(lemmas), writeBack, None, choice).saturated(
        index(lemmas),
        Vector(closed(program)),
        explained = false,
        stop
      )
    run.end match
      case End.FixedPoint(_) => Some(run.graph.instanceKeys.size)
      case _                 => None

  stoppableProperty(
    "a round with the narrower opening adds no more instances than the default"
  ) { stopped =>
    for
      program <- programs.forAllWithLog(identity)
      spine <- spines.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val lemmas = Vector(headLemma(spine), idempotence)
      (
        instances(lemmas, program, OpeningCriterionChoice.CallsAHead, stop),
        instances(
          lemmas,
          program,
          OpeningCriterionChoice.CallsAHeadWithMatchingArguments,
          stop
        )
      ) match
        case (Some(default), Some(narrower)) =>
          Result
            .assert(narrower <= default)
            .log(s"instances: default $default, narrower $narrower")
        case _ => Result.success
  }

  /** The shapes the option may lose, read from the code: `H a (b + c)` where
    * the body's own steps give z's class a choice, and `H a (f y)` where they
    * give it an application, each with a generated first argument.
    */
  private val witnesses: Gen[(Vector[SpineArgument], String)] =
    for
      first <- closedText
      application <- Gen.boolean
    yield
      if application then
        (
          Vector(spineArgument(0, 0), spineArgument(3, 1)),
          s"λz. (((λw. w) z) + $headText ($first) z)"
        )
      else
        (
          Vector(spineArgument(0, 0), spineArgument(1, 1)),
          s"λz. ((z + z) ∥ $headText ($first) z)"
        )

  stoppableTest(
    "the witnesses: the instances of the default's round and of the narrower one's"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    assertSeededSnapshot(
      witnesses,
      20261121L,
      8,
      "opening-criterion/witnesses.txt"
    )(
      (spine, program) => s"${spine.map(_.text).mkString(" ")} in $program",
      { case (default, narrower) => s"default $default, narrower $narrower" }
    ) { (spine, program) =>
      val lemmas = Vector(headLemma(spine), idempotence)
      (
        instances(lemmas, program, OpeningCriterionChoice.CallsAHead, stop),
        instances(
          lemmas,
          program,
          OpeningCriterionChoice.CallsAHeadWithMatchingArguments,
          stop
        )
      )
    }
  }
