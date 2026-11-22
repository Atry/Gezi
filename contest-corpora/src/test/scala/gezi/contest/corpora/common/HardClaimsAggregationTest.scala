package gezi.contest.corpora.common

import gezi.contest.corpora.claims.Template
import java.nio.file.Paths

/** The hard corpus over every group's files, built once for the suites. */
object HardCorpusFixture:

  /** The root of the build, which it passes to the forked test JVM. */
  val corpus: HardCorpus = HardCorpus(
    Paths.get(
      sys.props.getOrElse(
        "gezi.buildRoot",
        throw IllegalStateException("the build passes gezi.buildRoot to the forked test JVM")
      )
    ),
    gezi.weakhead.Expansions.none,
    gezi.hotspot.baselines.BaselineCaches.provider()
  )

  /** The claims tables and the families' facts with their fields decoded.
    * A field is decoded once, when first asked for (`ProblemField.text`), and
    * the claims of any one point scan every row of the tables they read and
    * every family's facts, the decodings all points share: so the claims of
    * one point decode them. MEASURED 2026-11-19 (a scratch probe after the
    * corpus was built, run alone): the first point's claims took 4.5 s, of
    * which `hardIntended` 3.4 s, `cycles` 0.7 s and `unreadFiniteHeads` 0.5 s;
    * every later point's, of fibonacci or of binary, 0.01 to 0.02 s.
    * MEASURED 2026-11-20 (a scratch probe, CPUs 0 to 7, the load 2 to 4):
    * 3.38 s with each decoding from a fresh reading state, 2.69 s twice with
    * each from its family's state, which shares the complete tables of what
    * the decodings read alike (`ProblemField`).
    * A decoding is the library's `from_cbor` reading a literal's bits one
    * argument at a time, about 2,500 evaluator steps for a text of a dozen
    * bytes: linear in the bits, the weak head's cost per step a constant
    * factor.
    */
  lazy val claimsDecoded: Vector[(String, Template)] =
    claims(corpus.binary.points.map(_._1).headOption.getOrElse(throw IllegalStateException("the binary corpus has no point")))

  /** The kinds and templates of the point's claims (`hard_claim/4`'s
    * `Role-Template`), in order.
    */
  def claims(point: String): Vector[(String, Template)] =
    corpus.hardClaims(point).map(claim => claim.kind -> claim.template)

  /** The template of the point's one intended head
    * (`contest_hard_answers:hard_intended(Point, head, Intended)`).
    */
  def intendedHead(point: String): Template =
    corpus.claimsGroup.answers.hardIntended(point).filter(_.outcome == gezi.contest.corpora.claims.IntendedOutcome.Head) match
      case Vector(intended) => Template.of(intended.value)
      case found            => throw AssertionError(s"$point intends ${found.size} heads")

  /** The test of the merge family's `.plt` files: every point poses exactly
    * one scored claim, its intended head; and, when `planned`, no point is
    * retired (`\+ hard_role(Point, retired)`).
    */
  def assertOneScoredClaim(suite: munit.FunSuite, points: Vector[String], planned: Boolean): Unit =
    suite.assert(points.nonEmpty)
    points.foreach(point =>
      suite.assertEquals((point, claims(point)), (point, Vector("scored" -> intendedHead(point))))
      if planned then suite.assertNotEquals((point, corpus.claimsGroup.answers.hardRole(point)), (point, Some("retired")))
    )

/** A suite that reads `HardCorpusFixture.corpus`: the corpus is its shared
  * fixture (`FailFastSuite.sharedFixtures`), built in `beforeAll` under a
  * longer `fixtureTimeout`, so that no test is charged for it and the run
  * order does not decide which suite overruns.
  *
  * MEASURED 2026-11-20 (a scratch probe forcing the corpus in a new test
  * JVM, CPUs 0 to 7, the 1-minute load 2 to 4): 9.05, 8.62 and 8.58 s, the
  * last two after a problem field was decoded from its family's state
  * (4cb3691fa); 1.5 times 8.62 s is within the default `fixtureTimeout` of
  * 15 s, which the suite keeps. On 2026-11-19 at the load 13 to 19 it took
  * 18.6 to 27.3 s, JFR putting 92% of it in `KnowledgeReading.run`, the
  * weak-head readings of the problem tables.
  */
trait HardCorpusSuite extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures :+ (_ => HardCorpusFixture.corpus)

/** A suite that reads the claims of hard points: besides the corpus, its
  * shared fixture is `HardCorpusFixture.claimsDecoded`, so that the
  * decodings every point's claims share are not charged to whichever test
  * asks first.
  */
trait HardClaimsSuite extends HardCorpusSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures :+ (_ => HardCorpusFixture.claimsDecoded)

  // The corpus's build (8.62 s, HardCorpusSuite) and the decodings (2.69 s, claimsDecoded), measured 2026-11-20, 1.5
  // times, rounded up to 5 s.
  override val fixtureTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_merge_binary.plt`), over every group's files. */
class ContestMergeBinaryClaimsTest extends HardClaimsSuite:
  test("everyPointPosesOneScoredClaim") {
    HardCorpusFixture.assertOneScoredClaim(this, HardCorpusFixture.corpus.binary.points.map(_._1), planned = false)
  }

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_merge_fibonacci.plt`). */
class ContestMergeFibonacciClaimsTest extends HardClaimsSuite:
  test("everyPointPosesOneScoredClaim") {
    HardCorpusFixture.assertOneScoredClaim(this, HardCorpusFixture.corpus.fibonacci.points.map(_._1), planned = false)
  }

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_merge_meanings.plt`). */
class ContestMergeMeaningsClaimsTest extends HardClaimsSuite:
  test("everyPointPosesOneScoredClaimAndIsPlanned") {
    val points = HardCorpusFixture.corpus.meanings.points.map(_._1)
    HardCorpusFixture.assertOneScoredClaim(this, points, planned = true)
  }

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_merge_dynamic.plt`). */
class ContestMergeDynamicClaimsTest extends HardClaimsSuite:
  test("everyPointPosesOneScoredClaimAndIsPlanned") {
    val dynamic = HardCorpusFixture.corpus.dynamic
    val points = dynamic.gridPoints.map(_._1) ++ dynamic.subsetPoints.map(_._1) ++ dynamic.lcsPoints.map(_._1)
    HardCorpusFixture.assertOneScoredClaim(this, points, planned = true)
  }

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_merge_graph.plt`): one scored claim, `boolean(true)`. */
class ContestMergeGraphClaimsTest extends HardClaimsSuite:
  test("everyPointPosesOneScoredClaim") {
    val points = HardCorpusFixture.corpus.graph.points.map(_._1)
    assert(points.nonEmpty)
    points.foreach(point =>
      assertEquals((point, HardCorpusFixture.claims(point)), (point, Vector("scored" -> Template.BooleanTemplate(true))))
    )
  }

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_merge_datalog.plt`): one scored claim, `boolean(true)`. */
class ContestMergeDatalogClaimsTest extends HardClaimsSuite:
  test("everyPointPosesOneScoredClaim") {
    val points = HardCorpusFixture.corpus.datalog.points.map(_._1)
    assert(points.nonEmpty)
    points.foreach(point =>
      assertEquals((point, HardCorpusFixture.claims(point)), (point, Vector("scored" -> Template.BooleanTemplate(true))))
    )
  }

/** The claim test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_empty_set_reachability.plt`): every public point
  * poses one scored claim, `boolean(true)`.
  */
class ContestEmptySetReachabilityClaimsTest extends HardClaimsSuite:
  test("everyPublicPointPosesOneScoredClaim") {
    val points = gezi.contest.corpora.reductions.EmptySetReachability
      .points(HardCorpusFixture.corpus.reductionGroup)
      .map(_._1)
    assert(points.nonEmpty)
    points.foreach(point =>
      assertEquals((point, HardCorpusFixture.claims(point)), (point, Vector("scored" -> Template.BooleanTemplate(true))))
    )
  }

/** The first test of the deleted Prolog test (`git show d32e69ff0^:lambda_jit/tests/contest_mixin_traps.plt`), the half that reads
  * `hard_claim/4`: each of the sixteen points poses both Booleans as traps,
  * each proved `no_yield`.
  */
class ContestMixinTrapsClaimsTest extends HardClaimsSuite:
  test("theSixteenPointsPoseBothBooleansAsTraps") {
    val points = HardCorpusFixture.corpus.mixinTraps.trapPoints
    assertEquals(points.length, 16)
    points.foreach(point =>
      assertEquals(
        (point, HardCorpusFixture.corpus.hardClaims(point).map(claim => (claim.kind, claim.template, claim.proof.written))),
        (
          point,
          Vector(
            ("trap", Template.BooleanTemplate(true), "proved(no_yield)"),
            ("trap", Template.BooleanTemplate(false), "proved(no_yield)")
          )
        )
      )
    )
  }
