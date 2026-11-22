package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import gezi.weakhead.Mode
import gezi.contest.corpora.common.DeBruijnTerms
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.GeneratedProperties
import snapshot4s.generated.snapshotConfig

/** The tests of a repeated variant (`Repeated.scala`).
  *
  * The law, whose purpose is to catch a variant whose program does not
  * apply the family's function to its inputs as the family's own points do
  * (a wrong function, a site given another input, results out of order, an
  * input dropped or repeated): on generated seeds and repetitions R from 1
  * to 6, the normal forms the reference evaluator reads of the repeated
  * program are the Scott lists, in order, of the normal forms of the R
  * single-input programs, one list for each choice of one normal form per
  * single program, and every single program has one unless the suite says
  * otherwise (`everySingleProgramAnswers`). The mode is the one
  * the family's existing reading test uses, and tabling(weak_head) for a family with
  * none unless its class says otherwise; every reading gets
  * `Decoding.limit`, 20,000,000 steps, as the reading tests do, and a
  * reading it stops fails the law. Seeds and R are drawn uniformly, 30 of
  * them per variant; a failure is shrunk at most 8 times, since every
  * shrink reads R + 2 or more programs again and munit stops a test after
  * 30 seconds. The law reads the programs of `lawVariant`, which is the
  * variant itself unless a suite draws the law's data from a smaller range
  * (a suite that does says why in its Scaladoc).
  *
  * The snapshot, whose purpose is to show in review any change of what a
  * seed draws or of the program built from it: the draws and the program's
  * lambdalattice text for the seed 20261031 and R = 3, always of the variant
  * itself, whose ranges the points draw from.
  */
abstract class RepeatedVariantSuite(variant: RepeatedVariant, mode: Mode, snapshotName: String)
    extends GeneratedProperties
    with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of RepeatedVariantSuite (slowest of its subclasses: ReductionProblemsFibonacciRepeatedTest), "the repeated program's normal forms are the Scott lists of the single programs' normal forms", takes 37.600 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(60, "s")

  private val group = ReductionTesting.group

  /** The variant whose programs the law reads: the same function and
    * encoding as `variant`, possibly over smaller ranges.
    */
  protected def lawVariant: RepeatedVariant = variant

  /** Whether the law asks every single program to have a normal form: true
    * unless the family's sites may have none by design (a suite that says
    * false says why in its Scaladoc).
    */
  protected def everySingleProgramAnswers: Boolean = true

  /** The normal forms of the program, or why the reading stopped. */
  private def normalForms(description: String, program: Term): Either[String, Set[DeBruijnTerm]] =
    Reduction.answeredNormalForms(mode, program, Decoding.limit) match
      case NormalFormReading.Finished(forms) => Right(forms.toSet)
      case stopped                           => Left(s"the reading of $description stopped: $stopped")

  /** Every reading's normal forms, or the first stop. */
  private def allRead[Value](readings: Vector[Either[String, Value]]): Either[String, Vector[Value]] =
    readings.foldLeft(Right(Vector.empty): Either[String, Vector[Value]])((read, reading) =>
      for
        before <- read
        value <- reading
      yield before :+ value
    )

  /** Every choice of one member of each set, in order. */
  private def choices(sets: Vector[Set[DeBruijnTerm]]): Set[Vector[DeBruijnTerm]] =
    sets.foldLeft(Set(Vector.empty[DeBruijnTerm]))((prefixes, forms) =>
      for
        prefix <- prefixes
        form <- forms
      yield prefix :+ form
    )

  property(
    "the repeated program's normal forms are the Scott lists of the single programs' normal forms",
    _.copy(testLimit = 30, shrinkLimit = hedgehog.core.ShrinkLimit(8))
  ) {
    for
      seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
      repetitions <- Gen.int(hedgehog.Range.constant(1, 6)).forAll
    yield
      val read =
        for
          singles <- allRead(lawVariant.singlePrograms(group, seed, repetitions).zipWithIndex.map((program, site) =>
            normalForms(s"the single program $site", program)
          ))
          lists <- allRead(choices(singles).toVector.map(forms =>
            normalForms("a list of normal forms", SetFree.scottList(group.attractors, forms.map(DeBruijnTerms.hoas)))
          ))
          repeated <- normalForms("the repeated program", lawVariant.program(group, seed, repetitions))
        yield (singles, lists.flatten.toSet, repeated)
      val law = read match
        case Left(stop) => Result.failure.log(stop)
        case Right((singles, expected, repeated)) =>
          Result
            .assert(!everySingleProgramAnswers || singles.forall(_.nonEmpty))
            .log("every single program has a normal form")
            .and(Result.diff(repeated, expected)(_ == _))
      law.log(lawVariant.drawnText(group, seed, repetitions))
  }

  test("the program of the seed 20261031 and three repetitions") {
    val seed = 20261031L
    val program = variant.program(group, seed, 3)
    assertFileSnapshot(
      s"seed $seed, 3 repetitions\n${variant.drawnText(group, seed, 3)}\n=>\n${LambdalatticeText.text(program)}\n",
      s"repeated/$snapshotName.txt"
    )
  }

class ReductionMeaningsRepeatedTest
    extends RepeatedVariantSuite(ReductionMeaningsRepeated, Mode.TablingWeakHead, "reduction_meanings")

class ReductionInterpreterRepeatedTest
    extends RepeatedVariantSuite(ReductionInterpreterRepeated, Mode.TablingWeakHead, "reduction_interpreter")

class SetFreePremisesRepeatedTest extends RepeatedVariantSuite(SetFreePremisesRepeated, Mode.TablingWeakHead, "set_free_premises")

/** The scope loop's tests. The law draws its steps from 0 to 20 (the points'
  * range before they were widened), not from the points' 0 to 63: the law reads up to
  * six single programs and the repeated program under weak_head, and over
  * 0 to 63 it took 221 s in a run of the Repeated suites alone on CPUs 8 to
  * 11 (2026-10-31), past munit's 30 s. The function and the encoding the law
  * checks do not depend on the range; the snapshot still shows the points'
  * draws.
  */
class SetFreeScopeRepeatedTest extends RepeatedVariantSuite(SetFreeScopeRepeated, Mode.TablingWeakHead, "set_free_scope"):
  override protected def lawVariant: RepeatedVariant =
    SetFreeScopeRepeatedVariant(
      NominalRanges(Repetition.repetitionsWithin(21), Vector(NominalParameter("steps", 0 to 20)))
    )

/** The list law's tests. The law draws its doublings from 0 to 6 and R up to
  * 7 (the points' ranges before they were widened), not from the points' 0 to 12 and
  * up to 13: over those, under weak_head, the law took 30.6 s in a run of
  * the whole build's tests on CPUs 6 and 7 (2026-11-01), past munit's 30 s. The
  * function and the encoding the law checks do not depend on the range; the
  * snapshot still shows the points' draws.
  */
class SetFreeListLawsRepeatedTest
    extends RepeatedVariantSuite(SetFreeListLawsRepeated, Mode.TablingWeakHead, "set_free_list_laws"):
  override protected def lawVariant: RepeatedVariant =
    SetFreeListLawsRepeatedVariant(
      NominalRanges(Repetition.repetitionsWithin(7), Vector(NominalParameter("doublings", 0 to 6)))
    )

class ReductionProblemsFibonacciRepeatedTest
    extends RepeatedVariantSuite(ReductionProblemsRepeated.Fibonacci, Mode.TablingWeakHead, "reduction_problems_fibonacci")

class ReductionProblemsProductsRepeatedTest
    extends RepeatedVariantSuite(ReductionProblemsRepeated.Products, Mode.TablingWeakHead, "reduction_problems_products")

/** The grids' tests. The law draws its sides from 0 to 7, not from the
  * points' 0 to 9: under weak_head the paths of a grid grow fast with its
  * side, and the law took 68 s with sides up to 9 (2026-10-31) and 41.7 s
  * with sides up to 8, run alone (2026-11-01), past munit's 30 s; with sides
  * up to 7 the suite took 8.2 s on CPUs 6 and 7 at load 9 (2026-11-01). The
  * function and the encoding the
  * law checks do not depend on the range; the snapshot still shows the
  * points' draws.
  */
class ReductionProblemsGridsRepeatedTest
    extends RepeatedVariantSuite(ReductionProblemsRepeated.Grids, Mode.TablingWeakHead, "reduction_problems_grids"):
  override protected def lawVariant: RepeatedVariant =
    ReductionProblemsRepeated.GridsVariant(
      NominalRanges(Repetition.repetitionsWithin(9), Vector(NominalParameter("side", 0 to 7)))
    )

class ReductionProblemsSumsRepeatedTest
    extends RepeatedVariantSuite(ReductionProblemsRepeated.Sums, Mode.TablingWeakHead, "reduction_problems_sums")

/** The family has no reading test; its programs are read under
  * tabling(weak_head). Under weak_head the one product 7 × 6 took
  * 17,321,140 steps and 13 × 29 ran past the 20,000,000 of `Decoding.limit`,
  * while under tabling(weak_head) every product of operands up to 15 that
  * was measured took from 3,261 to 5,373 steps (2026-10-31).
  */
class ReductionMixinBinaryRepeatedTest
    extends RepeatedVariantSuite(ReductionMixinBinaryRepeated, Mode.TablingWeakHead, "reduction_mixin_binary")

class SetFreeArithmeticRepeatedTest
    extends RepeatedVariantSuite(SetFreeArithmeticRepeated, Mode.TablingWeakHead, "set_free_arithmetic")

/** The ranges the laws of the standard library's families draw from, small
  * so that weak_head reads 30 programs of up to six sites within munit's 30
  * seconds; the construction of the program does not depend on the ranges.
  */
object StandardLibraryFamilyRanges:

  /** n, m and k from 0 to 3. */
  val doublingParities: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4 * 4 * 4),
    Vector(NominalParameter("number", 0 to 3), NominalParameter("doublings", 0 to 3), NominalParameter("addend", 0 to 3))
  )

  /** Lists of 0 to 4 digits. */
  val binaryParities: NominalRanges = NominalRanges(Repetition.repetitionsWithin(31), Vector(NominalParameter("length", 0 to 4)))

  /** n odd from 1 to 11, distinct across sites; m from 0 to 1, k from 0 to 3. */
  val unsharedDoublings: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(NominalParameter("number", Range.inclusive(1, 11, 2)), NominalParameter("doublings", 0 to 1), NominalParameter("addend", 0 to 3))
  )

  /** Lists of 4 digits, distinct in all four: 2^3 = 8 lists. */
  val unsharedBinary: NominalRanges = NominalRanges(Repetition.repetitionsWithin(8), Vector(NominalParameter("length", 4 to 4)))

  /** The suffix length beyond which the lists of `unsharedBinary` differ. */
  val unsharedBinarySuffix: Int = 4

  /** Words of width 4, whose odd bases are 2^3 = 8; k from 0 to 2. */
  val unsharedWordPowers: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(8),
    Vector(NominalParameter("width", 4 to 4), NominalParameter("exponent", 0 to 2))
  )

  /** The larger operand of 3 to 6 digits, the smaller 2 digits shorter, so
    * of 1 to 4, one to four leading zeros at a trap site, at R up to 6.
    */
  val binaryDomainTraps: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(NominalParameter("bits", 3 to 6), NominalParameter("shorter_by", 2 to 2), NominalParameter("padding", 1 to 4))
  )

  /** Pairs of strings of 0 to 3 characters over the alphabet 0 and 1. */
  val longestCommonSubsequences: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(NominalParameter("length", 0 to 3), NominalParameter("character", 0 to 1))
  )

  /** One to three rods of lengths 1 to 3; 39 distinct lists, among them
    * those where two rods on one side balance a third, so that the native
    * solver's sums of several rods are checked.
    */
  val billboards: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(NominalParameter("rods", 1 to 3), NominalParameter("length", 1 to 3))
  )

  /** Pairs of strings of 0 to 3 characters each, the two lengths drawn
    * apart, over the alphabet 0 and 1.
    */
  val editDistances: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(NominalParameter("length", 0 to 3), NominalParameter("character", 0 to 1))
  )

  /** One to three skills and zero to four people, each skill held with
    * probability one half, so that some sites have no sufficient team and
    * answer the count of people plus one.
    */
  val smallestTeams: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(NominalParameter("skills", 1 to 3), NominalParameter("people", 0 to 4), NominalParameter("held", 0 to 1))
  )

  /** One to six functions of one to three steps, constants and initial
    * states of one to three digits, C = 2 and alpha = 2: the hottest
    * function is called twice and the others once, so that iterate reads a
    * zero, an even and an odd count, and a site of more than four functions
    * gives the hot variant fewer functions than the rung's. weak_head reads
    * the drawn law's points in up to a few million steps under C = 4 (one to
    * three functions, seeds 0 to 9 at R = 6: up to 3,768,400 steps, 442 ms,
    * 2026-11-02), since it reads every use of an intermediate anew; C = 2
    * keeps the law's 30 draws within munit's 30 seconds.
    */
  val hotspots: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(6),
    Vector(
      NominalParameter("functions", 1 to 6),
      NominalParameter("steps", 1 to 3),
      NominalParameter("constant_bits", 1 to 3),
      NominalParameter("initial_bits", 1 to 3),
      NominalParameter("calls", 2 to 2),
      NominalParameter("exponent", 2 to 2)
    )
  )

  /** The hotspots' variant of the calibration at the small ranges in the
    * spelling, with the top rung's name.
    */
  def hotspotsVariant(spelling: Spelling, calibration: LibraryHotspots.Calibration): LibraryHotspots =
    val calls = LibraryHotspots.rungCalls.last
    LibraryHotspots(spelling, hotspots, LibraryHotspots.familyName(calls, calibration), calibration)

  /** The ranges of `hotspots` with one or two functions and C = 4, for the
    * hot ladder's other shapes: the hot variant's counts, floor(4 / r^2)
    * for the ranks r = 1 and 2, are 4 and 1, so that the nested shape
    * splits a count into two loops of 2 and applies a count of 1 once, and
    * the inlined shape's loop reads a zero, an even and an odd digit.
    * weak_head reads every use of an intermediate anew, so its steps grow
    * with the calls in a row: at four functions and C = 4 (counts 4, 1, 1
    * and 1), a site drawn by the law (initial state 4, the count 4 last)
    * took more than `Decoding.limit` in the respelled spelling of every
    * shape, the iterated one included, and between 20,000,000 and
    * 100,000,000 steps (about 4.5 s; 2026-11-07); at C = 12 the first draw
    * of both shapes stopped. The split of a prime count is the law of
    * `LibraryHotspotsShapesTest`.
    */
  val hotspotShapes: NominalRanges = NominalRanges(
    hotspots.repetitions,
    hotspots.parameters.map(parameter =>
      parameter.name match
        case "functions" => NominalParameter("functions", 1 to 2)
        case "calls"     => NominalParameter("calls", 4 to 4)
        case _           => parameter
    )
  )

  /** The shape's hot variant at the small ranges `hotspotShapes` in the
    * spelling, with the top shaped rung's name.
    */
  def hotspotsShapedVariant(spelling: Spelling, shape: LibraryHotspots.Shape): LibraryHotspots =
    val calls = LibraryHotspots.shapedRungCalls.last
    val calibration = LibraryHotspots.Calibration.Hot
    LibraryHotspots(spelling, hotspotShapes, LibraryHotspots.shapedFamilyName(shape, calls, calibration), calibration, shape)

  /** The scaled doublings at the small ranges, with the scaled family's name and claim. */
  def unsharedDoublingsLarge(spelling: Spelling): LibraryUnsharedDoublings =
    LibraryUnsharedDoublings(spelling, unsharedDoublings, LibraryUnsharedDoublings.largeName, LibraryUnsharedDoublings.largeClaim)

  /** The scaled binary lists at the small ranges, with the scaled family's name and claim. */
  def unsharedBinaryLarge(spelling: Spelling): LibraryUnsharedBinary =
    LibraryUnsharedBinary(
      spelling,
      unsharedBinary,
      unsharedBinarySuffix,
      LibraryUnsharedBinary.largeName,
      LibraryUnsharedBinary.largeClaim
    )

class LibraryDoublingParitiesDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryDoublingParities(Spelling.Direct, StandardLibraryFamilyRanges.doublingParities),
      Mode.TablingWeakHead,
      "library_doubling_parities_direct"
    )

class LibraryDoublingParitiesRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryDoublingParities(Spelling.Respelled, StandardLibraryFamilyRanges.doublingParities),
      Mode.TablingWeakHead,
      "library_doubling_parities_respelled"
    )

class LibraryBinaryParitiesDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryBinaryParities(Spelling.Direct, StandardLibraryFamilyRanges.binaryParities),
      Mode.TablingWeakHead,
      "library_binary_parities_direct"
    )

class LibraryBinaryParitiesRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryBinaryParities(Spelling.Respelled, StandardLibraryFamilyRanges.binaryParities),
      Mode.TablingWeakHead,
      "library_binary_parities_respelled"
    )

class LibraryUnsharedDoublingsDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedDoublings(
        Spelling.Direct,
        StandardLibraryFamilyRanges.unsharedDoublings,
        LibraryUnsharedDoublings.name,
        LibraryUnsharedDoublings.claim
      ),
      Mode.TablingWeakHead,
      "library_unshared_doublings_direct"
    )

class LibraryUnsharedDoublingsRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedDoublings(
        Spelling.Respelled,
        StandardLibraryFamilyRanges.unsharedDoublings,
        LibraryUnsharedDoublings.name,
        LibraryUnsharedDoublings.claim
      ),
      Mode.TablingWeakHead,
      "library_unshared_doublings_respelled"
    )

class LibraryUnsharedBinaryDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedBinary(
        Spelling.Direct,
        StandardLibraryFamilyRanges.unsharedBinary,
        StandardLibraryFamilyRanges.unsharedBinarySuffix,
        LibraryUnsharedBinary.name,
        LibraryUnsharedBinary.claim
      ),
      Mode.TablingWeakHead,
      "library_unshared_binary_direct"
    )

class LibraryUnsharedBinaryRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedBinary(
        Spelling.Respelled,
        StandardLibraryFamilyRanges.unsharedBinary,
        StandardLibraryFamilyRanges.unsharedBinarySuffix,
        LibraryUnsharedBinary.name,
        LibraryUnsharedBinary.claim
      ),
      Mode.TablingWeakHead,
      "library_unshared_binary_respelled"
    )

/** The scaled doublings' tests. The law draws from the small ranges of
  * `StandardLibraryFamilyRanges.unsharedDoublings`: at the nominal m from
  * 12 to 16 a single site's reading is beyond `Decoding.limit`. The
  * construction does not depend on the ranges; the snapshot shows the
  * nominal draws.
  */
class LibraryUnsharedDoublingsLargeDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedDoublings.large(Spelling.Direct),
      Mode.TablingWeakHead,
      "library_unshared_doublings_large_direct"
    ):
  override protected def lawVariant: RepeatedVariant = StandardLibraryFamilyRanges.unsharedDoublingsLarge(Spelling.Direct)

/** As `LibraryUnsharedDoublingsLargeDirectRepeatedTest`, respelled. */
class LibraryUnsharedDoublingsLargeRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedDoublings.large(Spelling.Respelled),
      Mode.TablingWeakHead,
      "library_unshared_doublings_large_respelled"
    ):
  override protected def lawVariant: RepeatedVariant = StandardLibraryFamilyRanges.unsharedDoublingsLarge(Spelling.Respelled)

/** The scaled binary lists' tests. The law draws from the small ranges of
  * `StandardLibraryFamilyRanges.unsharedBinary`: at the nominal 24 digits a
  * single site's reading is beyond `Decoding.limit`. The construction does
  * not depend on the ranges; the snapshot shows the nominal draws.
  */
class LibraryUnsharedBinaryLargeDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedBinary.large(Spelling.Direct),
      Mode.TablingWeakHead,
      "library_unshared_binary_large_direct"
    ):
  override protected def lawVariant: RepeatedVariant = StandardLibraryFamilyRanges.unsharedBinaryLarge(Spelling.Direct)

/** As `LibraryUnsharedBinaryLargeDirectRepeatedTest`, respelled. */
class LibraryUnsharedBinaryLargeRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedBinary.large(Spelling.Respelled),
      Mode.TablingWeakHead,
      "library_unshared_binary_large_respelled"
    ):
  override protected def lawVariant: RepeatedVariant = StandardLibraryFamilyRanges.unsharedBinaryLarge(Spelling.Respelled)

/** The binary domain traps' tests. The law draws from the small ranges of
  * `StandardLibraryFamilyRanges.binaryDomainTraps`, so that the R + 2
  * readings of a draw stay well within `Decoding.limit`; the construction
  * does not depend on the ranges, and the snapshot shows the nominal draws.
  */
class LibraryBinaryDomainTrapsDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryBinaryDomainTraps(Spelling.Direct, LibraryBinaryDomainTraps.nominal),
      Mode.TablingWeakHead,
      "library_binary_domain_traps_direct"
    ):
  override protected def lawVariant: RepeatedVariant =
    LibraryBinaryDomainTraps(Spelling.Direct, StandardLibraryFamilyRanges.binaryDomainTraps)

/** As `LibraryBinaryDomainTrapsDirectRepeatedTest`, respelled. */
class LibraryBinaryDomainTrapsRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryBinaryDomainTraps(Spelling.Respelled, LibraryBinaryDomainTraps.nominal),
      Mode.TablingWeakHead,
      "library_binary_domain_traps_respelled"
    ):
  override protected def lawVariant: RepeatedVariant =
    LibraryBinaryDomainTraps(Spelling.Respelled, StandardLibraryFamilyRanges.binaryDomainTraps)

/** The word powers' tests. The law draws from the small ranges of
  * `StandardLibraryFamilyRanges.unsharedWordPowers`, width 4: at the nominal
  * width 32 and k from 256 to 511 a single site's reading is beyond
  * `Decoding.limit`. The construction does not depend on the ranges; the
  * snapshot shows the nominal draws.
  */
class LibraryUnsharedWordPowersDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedWordPowers(Spelling.Direct, LibraryUnsharedWordPowers.nominal),
      Mode.TablingWeakHead,
      "library_unshared_word_powers_direct"
    ):
  override protected def lawVariant: RepeatedVariant =
    LibraryUnsharedWordPowers(Spelling.Direct, StandardLibraryFamilyRanges.unsharedWordPowers)

/** As `LibraryUnsharedWordPowersDirectRepeatedTest`, respelled. */
class LibraryUnsharedWordPowersRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryUnsharedWordPowers(Spelling.Respelled, LibraryUnsharedWordPowers.nominal),
      Mode.TablingWeakHead,
      "library_unshared_word_powers_respelled"
    ):
  override protected def lawVariant: RepeatedVariant =
    LibraryUnsharedWordPowers(Spelling.Respelled, StandardLibraryFamilyRanges.unsharedWordPowers)

/** The longest common subsequences' tests, over the small ranges of
  * `StandardLibraryFamilyRanges.longestCommonSubsequences` for the law and
  * the snapshot alike: at the nominal 3000 characters a single site's
  * reading is beyond `Decoding.limit`, and the program's text, 6000
  * characters a site, would make a snapshot of megabytes. The construction
  * does not depend on the ranges.
  */
class LibraryLongestCommonSubsequencesDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryLongestCommonSubsequences(Spelling.Direct, StandardLibraryFamilyRanges.longestCommonSubsequences, LibraryLongestCommonSubsequences.name),
      Mode.TablingWeakHead,
      "library_longest_common_subsequences_direct"
    )

/** As `LibraryLongestCommonSubsequencesDirectRepeatedTest`, respelled. */
class LibraryLongestCommonSubsequencesRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryLongestCommonSubsequences(Spelling.Respelled, StandardLibraryFamilyRanges.longestCommonSubsequences, LibraryLongestCommonSubsequences.name),
      Mode.TablingWeakHead,
      "library_longest_common_subsequences_respelled"
    )

/** The billboards' tests, over the small ranges of
  * `StandardLibraryFamilyRanges.billboards` for the law and the snapshot
  * alike: the nominal ranges allow R = 1 only, while the snapshot draws
  * three sites, and a single site of 20 rods is beyond `Decoding.limit`.
  * The construction does not depend on the ranges. A trap site's single
  * program has no normal form by design (`LibraryBillboards`), so the law
  * does not ask every single program for one.
  */
class LibraryBillboardsDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryBillboards(Spelling.Direct, StandardLibraryFamilyRanges.billboards, LibraryBillboards.name),
      Mode.TablingWeakHead,
      "library_billboards_direct"
    ):
  override protected def everySingleProgramAnswers: Boolean = false

/** As `LibraryBillboardsDirectRepeatedTest`, respelled. */
class LibraryBillboardsRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryBillboards(Spelling.Respelled, StandardLibraryFamilyRanges.billboards, LibraryBillboards.name),
      Mode.TablingWeakHead,
      "library_billboards_respelled"
    ):
  override protected def everySingleProgramAnswers: Boolean = false

/** The edit distances' tests, over the small ranges of
  * `StandardLibraryFamilyRanges.editDistances` for the law and the snapshot
  * alike: at the nominal 3000 characters a single site's reading is beyond
  * `Decoding.limit`, and the program's text would make a snapshot of
  * megabytes. The construction does not depend on the ranges.
  */
class LibraryEditDistancesDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibraryEditDistances(Spelling.Direct, StandardLibraryFamilyRanges.editDistances, LibraryEditDistances.name),
      Mode.TablingWeakHead,
      "library_edit_distances_direct"
    )

/** As `LibraryEditDistancesDirectRepeatedTest`, respelled. */
class LibraryEditDistancesRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibraryEditDistances(Spelling.Respelled, StandardLibraryFamilyRanges.editDistances, LibraryEditDistances.name),
      Mode.TablingWeakHead,
      "library_edit_distances_respelled"
    )

/** The smallest teams' tests, over the small ranges of
  * `StandardLibraryFamilyRanges.smallestTeams` for the law and the snapshot
  * alike: at the nominal 60 people a single site's reading is 2^60 choices,
  * beyond `Decoding.limit`. The construction does not depend on the ranges.
  */
class LibrarySmallestTeamsDirectRepeatedTest
    extends RepeatedVariantSuite(
      LibrarySmallestTeams(Spelling.Direct, StandardLibraryFamilyRanges.smallestTeams, LibrarySmallestTeams.name),
      Mode.TablingWeakHead,
      "library_smallest_teams_direct"
    )

/** As `LibrarySmallestTeamsDirectRepeatedTest`, respelled. */
class LibrarySmallestTeamsRespelledRepeatedTest
    extends RepeatedVariantSuite(
      LibrarySmallestTeams(Spelling.Respelled, StandardLibraryFamilyRanges.smallestTeams, LibrarySmallestTeams.name),
      Mode.TablingWeakHead,
      "library_smallest_teams_respelled"
    )

/** The hotspots' tests, over the small ranges of
  * `StandardLibraryFamilyRanges.hotspots` for the law and the snapshot
  * alike: at the nominal ranges a site is up to 256 functions of 32 steps
  * called up to 10^5 times, beyond `Decoding.limit` under weak_head. The
  * construction does not depend on the ranges.
  */
class LibraryHotspotsDirectRepeatedTest
    extends RepeatedVariantSuite(
      StandardLibraryFamilyRanges.hotspotsVariant(Spelling.Direct, LibraryHotspots.Calibration.Scored),
      Mode.TablingWeakHead,
      "library_hotspots_direct"
    )

/** As `LibraryHotspotsDirectRepeatedTest`, respelled. */
class LibraryHotspotsRespelledRepeatedTest
    extends RepeatedVariantSuite(
      StandardLibraryFamilyRanges.hotspotsVariant(Spelling.Respelled, LibraryHotspots.Calibration.Scored),
      Mode.TablingWeakHead,
      "library_hotspots_respelled"
    )

/** The inlined shape's tests, over the small ranges of
  * `StandardLibraryFamilyRanges.hotspotShapes`, for the reason
  * `LibraryHotspotsDirectRepeatedTest` gives, read under tabling(weak_head).
  * weak_head substitutes the state unevaluated, so a function that reads its
  * input u times, called c times, copies it u^c times: the shaped ranges
  * call a function 4 times (the iterated ranges 2), and a draw whose
  * function reads its input 4 times (`min(s, s)`, then `min(s, i1)`) ran
  * past `Decoding.limit`'s 20,000,000 steps and finished between 20,000,000
  * and 80,000,000 steps in 2.8 s, while tabling(weak_head), which shares the
  * copies by the term's identifier, read it within the limit in 0.012 s
  * with the same normal forms (seed 585175560, R = 3, site 2, from
  * HEDGEHOG_SEED=93599013496937; 2026-11-07). Three steps may read
  * the input up to 8 times, 8^4 copies.
  */
class LibraryHotspotsInlinedDirectRepeatedTest
    extends RepeatedVariantSuite(
      StandardLibraryFamilyRanges.hotspotsShapedVariant(Spelling.Direct, LibraryHotspots.Shape.Inlined),
      Mode.TablingWeakHead,
      "library_hotspots_inlined_direct"
    )

/** As `LibraryHotspotsInlinedDirectRepeatedTest`, respelled. */
class LibraryHotspotsInlinedRespelledRepeatedTest
    extends RepeatedVariantSuite(
      StandardLibraryFamilyRanges.hotspotsShapedVariant(Spelling.Respelled, LibraryHotspots.Shape.Inlined),
      Mode.TablingWeakHead,
      "library_hotspots_inlined_respelled"
    )

/** The nested shape's tests, over the small ranges of
  * `StandardLibraryFamilyRanges.hotspotShapes`, for the reason
  * `LibraryHotspotsDirectRepeatedTest` gives, read under tabling(weak_head)
  * for the reason `LibraryHotspotsInlinedDirectRepeatedTest` gives: the
  * nested loop applies the function as many times.
  */
class LibraryHotspotsNestedDirectRepeatedTest
    extends RepeatedVariantSuite(
      StandardLibraryFamilyRanges.hotspotsShapedVariant(Spelling.Direct, LibraryHotspots.Shape.Nested),
      Mode.TablingWeakHead,
      "library_hotspots_nested_direct"
    )

/** As `LibraryHotspotsNestedDirectRepeatedTest`, respelled. */
class LibraryHotspotsNestedRespelledRepeatedTest
    extends RepeatedVariantSuite(
      StandardLibraryFamilyRanges.hotspotsShapedVariant(Spelling.Respelled, LibraryHotspots.Shape.Nested),
      Mode.TablingWeakHead,
      "library_hotspots_nested_respelled"
    )
