package gezi.contest.corpora.reductions

import gezi.ir.{Configured, NoFacts}
import gezi.frontend.Term

// The CSES families of the fourth batch, built as the first batch's are (`CsesFamily`, `CsesFamilies.scala`), each
// rung in both spellings.

/** CSES 1712, Exponentiation II, `exponentiation_two a b c`: a to the power (b
  * to the power c), modulo 10^9 + 7, 0^0 being 1. A site is the three numbers,
  * drawn from the parameters `base`, `exponentBase` and `exponentPower`, all
  * written at every rung.
  */
final class ExponentiationTwo(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[ExponentiationTwo.Site](spelling, rung):

  val problem: String = "exponentiation_two"

  val claim: String =
    "gezi.contest.corpora.reductions.ExponentiationTwoReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[ExponentiationTwo.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.exponentiationTwo(
          site.base.toLong,
          site.exponentBase.toLong,
          site.exponentPower.toLong
        )
      )
    )

  protected def site(draws: Draws): (ExponentiationTwo.Site, Draws) =
    val (base, afterBase) = CsesFamily.drawnParameter(draws, nominal, "base")
    val (exponentBase, afterExponentBase) =
      CsesFamily.drawnParameter(afterBase, nominal, "exponentBase")
    val (exponentPower, after) =
      CsesFamily.drawnParameter(afterExponentBase, nominal, "exponentPower")
    (ExponentiationTwo.Site(base, exponentBase, exponentPower), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.exponentiationTwo

  def arguments(
      problems: CsesProblems,
      site: ExponentiationTwo.Site
  ): Vector[ProblemTerm] =
    Vector(
      CsesEncodings.natural(site.base),
      CsesEncodings.natural(site.exponentBase),
      CsesEncodings.natural(site.exponentPower)
    )

  /** A solution that reduces the exponent b^c modulo 10^9 + 7, the modulus of
    * the answer, where Fermat's little theorem reduces it modulo 10^9 + 6
    * (`ExponentiationTwo.reducedByTheModulus`).
    */
  def wrongAnswers(
      site: ExponentiationTwo.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        ExponentiationTwo.reducedByTheModulus(
          site.base,
          site.exponentBase,
          site.exponentPower
        )
      )
    )

/** The sites, the wrong reduction and the ladder of `ExponentiationTwo`. */
object ExponentiationTwo:

  /** The numbers a, b and c of a site. */
  final case class Site(base: Int, exponentBase: Int, exponentPower: Int)

  /** a^(b^c mod (10^9 + 7)) modulo 10^9 + 7. */
  def reducedByTheModulus(
      base: Int,
      exponentBase: Int,
      exponentPower: Int
  ): BigInt =
    val modulus = BigInt(CsesFamily.modulus)
    BigInt(base).modPow(
      BigInt(exponentBase).modPow(BigInt(exponentPower), modulus),
      modulus
    )

  /** The ladder: a to the b to the c with a up to 3, b and c up to 2, and with
    * a up to 5, b and c up to 3 (the direct programs read within the reference
    * reading's 50,000 tables, 2 of the 20 respelled singles passing them), and
    * CSES's constraint, 0 ≤ a, b, c ≤ 10^9, each number written, at most four
    * sites. MEASURED 2026-11-22 on 65bb56e89 by a scratch probe in
    * contest-corpora's tests (CPUs 2 and 3 of contest.slice, nice 10, the
    * 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 1,926 (direct, 4,157 steps) and
    * 3,303 (respelled, 7,435 steps), of the repeated program of the seed
    * 20261031 at R = 4, 1,282 (direct) and 1,768 (respelled); at the middle
    * rung, 42,520 (direct, 96,425 steps; 2 of the 20 above 20,000), 2 of the 20
    * respelled singles and the respelled R = 4 program stopped at the probe's
    * 60,000 tables, and the direct R = 4 program took 28,316.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "numbers_small",
      NominalRanges(
        Repetition.repetitionsWithin(24),
        Vector(
          NominalParameter("base", 0 to 3),
          NominalParameter("exponentBase", 0 to 2),
          NominalParameter("exponentPower", 0 to 2)
        )
      )
    ),
    CsesRung(
      "numbers_medium",
      NominalRanges(
        Repetition.repetitionsWithin(60),
        Vector(
          NominalParameter("base", 0 to 5),
          NominalParameter("exponentBase", 0 to 3),
          NominalParameter("exponentPower", 0 to 3)
        )
      )
    ),
    CsesRung(
      "numbers_1000000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("base", 0 to 1000000000),
          NominalParameter("exponentBase", 0 to 1000000000),
          NominalParameter("exponentPower", 0 to 1000000000)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[ExponentiationTwo]] =
    CsesFamily.families(rungs, ExponentiationTwo(_, _))

/** CSES 1090, Ferris Wheel, `ferris_wheel x weights`: the fewest gondolas that
  * carry the children, each gondola one child or two of at most x in weight
  * together. A site is x, from the parameter `capacity`, and n weights, n from
  * the parameter `weights`, each drawn from 1 to x, so that every child fits a
  * gondola alone, as the problem's premise asks.
  */
final class FerrisWheel(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[FerrisWheel.Site](spelling, rung):

  val problem: String = "ferris_wheel"

  val claim: String = "gezi.contest.corpora.reductions.FerrisWheelReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[FerrisWheel.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.ferrisWheel(site.capacity, IArray.from(site.weights))
      )
    )

  protected def site(draws: Draws): (FerrisWheel.Site, Draws) =
    val (capacity, afterCapacity) =
      CsesFamily.drawnParameter(draws, nominal, "capacity")
    val (count, afterCount) =
      CsesFamily.drawnParameter(afterCapacity, nominal, "weights")
    rung.input match
      case RungInput.Written =>
        val (weights, after) = CsesFamily.drawnValues(count, afterCount)(
          CsesFamily.between(_, 1 to capacity)
        )
        (FerrisWheel.Site(capacity, SeededInput.Input.Written(weights)), after)
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterCount, CsesFamily.seeds)
        (
          FerrisWheel.Site(
            capacity,
            SeededInput.Input.Seeded(
              SeededInput.Numbers(seed, count, 1, capacity)
            )
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.ferrisWheel

  def arguments(
      problems: CsesProblems,
      site: FerrisWheel.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(site.capacity +: written)
        Vector(
          naturals(site.capacity),
          CsesEncodings.list(written.map(naturals))
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(
          CsesEncodings.natural(site.capacity),
          generator.argument(problems)
        )

  /** A solution that puts the children two to a gondola, half of them rounded
    * up, whatever they weigh.
    */
  def wrongAnswers(
      site: FerrisWheel.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural((site.weights.size + 1) / 2))

/** The sites and the ladder of `FerrisWheel`. */
object FerrisWheel:

  /** The capacity x and the weights of a site. */
  final case class Site(capacity: Int, input: SeededInput.Input[Vector[Int]]):

    /** The weights. */
    def weights: Vector[Int] = input.data

    override def toString: String =
      s"Site($capacity,${input.described(_.toString)})"

  /** The ladder: up to 4 children, and up to 8, the most whose single program
    * the reference reading reads within its 50,000 tables (at 10, 2 of 30
    * direct and 3 of 30 respelled programs passed them), with x up to 8, and
    * CSES's constraints, 1 ≤ x ≤ 10^9 and 1 ≤ n ≤ 2 · 10^5, n drawn from the
    * upper half, at most four sites. MEASURED 2026-11-22 on 65bb56e89 by a
    * scratch probe in contest-corpora's tests (CPUs 2 and 3 of contest.slice,
    * nice 10, the 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 1,529 (direct, 3,258 steps) and
    * 2,805 (respelled, 6,485 steps), of the repeated program of the seed
    * 20261031 at R = 4, 2,255 and 3,486 and at R = 256, 44,599 (direct, 113,884
    * steps) and 58,876 (respelled); of the single programs of the seeds 0 to 29
    * at the middle rung, 12,286 (direct, 29,720 steps) and 25,436 (respelled,
    * 59,945 steps), of the repeated program at R = 4, 10,238 and 14,891.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "weights_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("capacity", 1 to 8),
          NominalParameter("weights", 1 to 4)
        )
      )
    ),
    CsesRung(
      "weights_8",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("capacity", 1 to 8),
          NominalParameter("weights", 1 to 8)
        )
      )
    ),
    CsesRung(
      "weights_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("capacity", 1 to 1000000000),
          NominalParameter("weights", 100000 to 200000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[FerrisWheel]] =
    CsesFamily.families(rungs, FerrisWheel(_, _))

/** CSES 1083, Missing Number, `missing_number n numbers`: the number from 1 to
  * n that the n - 1 other numbers leave out. A site is n, from the parameter
  * `upper`, and the numbers 1 to n but one drawn, in an order drawn, so that n
  * ≥ 1 and the numbers are different, as the problem's premise asks.
  */
final class MissingNumber(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[MissingNumber.Site](spelling, rung):

  val problem: String = "missing_number"

  val claim: String =
    "gezi.contest.corpora.reductions.MissingNumberReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[MissingNumber.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.missingNumber(site.upper, IArray.from(site.numbers))
      )
    )

  protected def site(draws: Draws): (MissingNumber.Site, Draws) =
    val (upper, afterUpper) = CsesFamily.drawnParameter(draws, nominal, "upper")
    rung.input match
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterUpper, CsesFamily.seeds)
        (
          MissingNumber.Site(
            upper,
            SeededInput.Input.Seeded(SeededInput.Rotation(seed, upper))
          ),
          after
        )
      case RungInput.Written =>
        val (missing, afterMissing) = CsesFamily.between(afterUpper, 1 to upper)
        val (numbers, after) = CsesFamily.shuffled(
          (1 to upper).toVector.filter(_ != missing),
          afterMissing
        )
        (MissingNumber.Site(upper, SeededInput.Input.Written(numbers)), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.missingNumber

  def arguments(
      problems: CsesProblems,
      site: MissingNumber.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(site.upper +: written)
        Vector(naturals(site.upper), CsesEncodings.list(written.map(naturals)))
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.upper), generator.argument(problems))

  /** A solution off by one. */
  def wrongAnswers(
      site: MissingNumber.Site,
      answer: NativeValue
  ): Vector[NativeValue] = Vector(CsesFamily.offByOne(answer))

/** The sites and the ladder of `MissingNumber`. */
object MissingNumber:

  /** The count n and the other n - 1 numbers of a site. */
  final case class Site(upper: Int, input: SeededInput.Input[Vector[Int]]):

    /** The numbers. */
    def numbers: Vector[Int] = input.data

    override def toString: String =
      s"Site($upper,${input.described(_.toString)})"

  /** The ladder: n from 5 to 8, and from 24 to 48 (at 96, 2 of 30 direct and 7
    * of 30 respelled single programs passed the reference reading's 50,000
    * tables), and CSES's constraint, 1 ≤ n ≤ 2 · 10^5, drawn from the upper
    * half, at most four sites. MEASURED 2026-11-22 on 65bb56e89 by a scratch
    * probe in contest-corpora's tests (CPUs 2 and 3 of contest.slice, nice 10,
    * the 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 1,508 (direct, 3,302 steps) and
    * 1,986 (respelled, 4,471 steps), of the repeated program of the seed
    * 20261031 at R = 4, 1,812 and 2,749 and at R = 256, 28,350 (direct, 77,578
    * steps) and 50,114 (respelled); of the single programs of the seeds 0 to 29
    * at the middle rung, 17,506 (direct, 44,573 steps) and 30,806 (respelled,
    * 79,889 steps), of the repeated program at R = 4, 10,389 and 21,226.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "upper_8",
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("upper", 5 to 8))
      )
    ),
    CsesRung(
      "upper_48",
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("upper", 24 to 48))
      )
    ),
    CsesRung(
      "upper_200000",
      NominalRanges(
        1 to 4,
        Vector(NominalParameter("upper", 100000 to 200000))
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[MissingNumber]] =
    CsesFamily.families(rungs, MissingNumber(_, _))

/** CSES 1069, Repetitions, `repetitions letters`: the length of the longest run
  * of one letter. A site is n letters, n from the parameter `letters`, each
  * from the parameter `letter`, the four letters being 0 to 3.
  */
final class Repetitions(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[Repetitions.Site](spelling, rung):

  val problem: String = "repetitions"

  val claim: String = "gezi.contest.corpora.reductions.RepetitionsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[Repetitions.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.repetitions(IArray.from(site.numbers)))
    )

  protected def site(draws: Draws): (Repetitions.Site, Draws) =
    CsesFamily.drawnNumbers(draws, nominal, rung.input, "letters", "letter")

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.repetitions

  def arguments(
      problems: CsesProblems,
      site: Repetitions.Site
  ): Vector[ProblemTerm] = Vector(site.argument(problems))

  /** A solution that answers one less than the longest run, as if it counted
    * the places where a letter equals the one before it.
    */
  def wrongAnswers(
      site: Repetitions.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Binary(digits) =>
      Vector(NativeValue.natural(CsesFamily.naturalOf(digits) - 1))
    case other => throw IllegalArgumentException(s"no natural: $other")

/** The sites and the ladder of `Repetitions`. */
object Repetitions:

  /** The letters of a site, written or seeded. */
  type Site = CsesFamily.NumbersSite

  /** The ladder: up to 6 letters, and up to 24, and CSES's constraint, 1 ≤ n ≤
    * 10^6, drawn from the upper half, at most four sites. MEASURED 2026-11-22
    * on 65bb56e89 by a scratch probe in contest-corpora's tests (CPUs 2 and 3
    * of contest.slice, nice 10, the 1-minute load about 7), tabling(weak_head)
    * knowing top (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000
    * tables, each reading one normal form: of the single programs of the seeds
    * 0 to 19 at the bottom rung, the most tables were 1,654 (direct, 3,586
    * steps) and 3,793 (respelled, 8,709 steps), of the repeated program of the
    * seed 20261031 at R = 4, 1,758 and 3,043, and at R = 256 both twins stopped
    * at the probe's 60,000 tables; of the single programs of the seeds 0 to 29
    * at the middle rung, 11,329 (direct, 26,304 steps) and 45,239 (respelled,
    * 113,181 steps; 9 of the 30 above 20,000), of the repeated program at R =
    * 4, 21,959 and 32,283.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "letters_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("letters", 1 to 6),
          NominalParameter("letter", 0 to 3)
        )
      )
    ),
    CsesRung(
      "letters_24",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("letters", 1 to 24),
          NominalParameter("letter", 0 to 3)
        )
      )
    ),
    CsesRung(
      "letters_1000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("letters", 500000 to 1000000),
          NominalParameter("letter", 0 to 3)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[Repetitions]] =
    CsesFamily.families(rungs, Repetitions(_, _))

/** CSES 1647, Static Range Minimum Queries, `static_range_minimums values
  * queries`: for each query (a, b), the least value from place a to place b,
  * both included and counted from 1, the sum of these. A site is n values, n
  * from the parameter `length`, each from the parameter `value`, and q queries,
  * q from the parameter `queries`, each a drawn from 1 to n and b from a to n,
  * so that 1 ≤ a ≤ b ≤ n, as the problem's premise asks.
  */
final class StaticRangeMinimums(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[StaticRangeMinimums.Site](spelling, rung):

  val problem: String = "static_range_minimums"

  val claim: String =
    "gezi.contest.corpora.reductions.StaticRangeMinimumsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[StaticRangeMinimums.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.staticRangeMinimums(
          IArray.from(site.values),
          site.queries
        )
      )
    )

  protected def site(draws: Draws): (StaticRangeMinimums.Site, Draws) =
    val (length, afterLength) =
      CsesFamily.drawnParameter(draws, nominal, "length")
    rung.input match
      case RungInput.Written =>
        val (values, afterValues) = CsesFamily.drawnValues(length, afterLength)(
          CsesFamily.drawnParameter(_, nominal, "value")
        )
        val (count, afterCount) =
          CsesFamily.drawnParameter(afterValues, nominal, "queries")
        val (queries, after) =
          CsesFamily.drawnValues(count, afterCount)(current =>
            val (first, afterFirst) = CsesFamily.between(current, 1 to length)
            val (last, afterLast) =
              CsesFamily.between(afterFirst, first to length)
            ((first, last), afterLast)
          )
        (
          StaticRangeMinimums.Site(
            SeededInput.Input.Written(values),
            SeededInput.Input.Written(queries)
          ),
          after
        )
      case RungInput.Seeded =>
        val (count, afterCount) =
          CsesFamily.drawnParameter(afterLength, nominal, "queries")
        val (valueSeed, afterValueSeed) =
          CsesFamily.between(afterCount, CsesFamily.seeds)
        val (querySeed, after) =
          CsesFamily.between(afterValueSeed, CsesFamily.seeds)
        val range = Repetition.range(nominal, "value")
        val values =
          SeededInput.Numbers(valueSeed, length, range.start, range.end)
        val queries = SeededInput.Ranges(querySeed, count, 1, length)
        (
          StaticRangeMinimums.Site(
            SeededInput.Input.Seeded(values),
            SeededInput.Input.Seeded(queries)
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.staticRangeMinimums

  def arguments(
      problems: CsesProblems,
      site: StaticRangeMinimums.Site
  ): Vector[ProblemTerm] =
    (site.valuesInput, site.queriesInput) match
      case (
            SeededInput.Input.Written(values),
            SeededInput.Input.Written(queries)
          ) =>
        val naturals = CsesEncodings.naturals(
          values ++ queries.flatMap((first, last) => Vector(first, last))
        )
        Vector(
          CsesEncodings.list(values.map(naturals)),
          CsesEncodings.list(
            queries.map((first, last) =>
              CsesEncodings.pair(naturals(first), naturals(last))
            )
          )
        )
      case (
            SeededInput.Input.Seeded(values),
            SeededInput.Input.Seeded(queries)
          ) =>
        Vector(values.argument(problems), queries.argument(problems))
      case _ =>
        throw IllegalStateException(
          s"a site's values and queries are both written or both seeded: $site"
        )

  /** A solution that answers the least value of the prefix up to place b, from
    * place 1, at every query, summed; it differs from the answer where a query
    * starts after the place of the prefix's least value.
    */
  def wrongAnswers(
      site: StaticRangeMinimums.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    val prefixMinimums = site.values.scanLeft(Int.MaxValue)(math.min)
    Vector(
      NativeValue.natural(
        site.queries.map((_, last) => prefixMinimums(last).toLong).sum
      )
    )

/** The sites and the ladder of `StaticRangeMinimums`. */
object StaticRangeMinimums:

  /** The values of a site and its queries, each `(a, b)` with 1 ≤ a ≤ b ≤ n.
    */
  final case class Site(
      valuesInput: SeededInput.Input[Vector[Int]],
      queriesInput: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The values. */
    def values: Vector[Int] = valuesInput.data

    /** The queries. */
    def queries: Vector[(Int, Int)] = queriesInput.data

    override def toString: String =
      s"Site(${valuesInput.described(_.toString)},${queriesInput.described(_.toString)})"

  /** The ladder: lists of up to 8 values, and up to 100, with up to 3 queries,
    * and CSES's constraints, 1 ≤ n, q ≤ 2 · 10^5 and 1 ≤ x ≤ 10^9, the counts
    * drawn from their upper halves, at most four sites. MEASURED 2026-11-22 on
    * 65bb56e89 by a scratch probe in contest-corpora's tests (CPUs 2 and 3 of
    * contest.slice, nice 10, the 1-minute load about 7), tabling(weak_head)
    * knowing top (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000
    * tables, each reading one normal form: of the single programs of the seeds
    * 0 to 19 at the bottom rung, the most tables were 1,813 (direct, 3,893
    * steps) and 3,075 (respelled, 7,071 steps), of the repeated program of the
    * seed 20261031 at R = 4, 2,812 and 4,963 and at R = 256, 53,396 (direct,
    * 126,338 steps) and the respelled twin stopped at the probe's 60,000; of
    * the single programs of the seeds 0 to 29 at the middle rung, 18,912
    * (direct, 44,799 steps) and 33,487 (respelled, 80,496 steps; 3 of the 30
    * above 20,000), of the repeated program at R = 4, 21,689 and 30,149.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "length_8",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("length", 1 to 8),
          NominalParameter("value", 1 to 16),
          NominalParameter("queries", 1 to 3)
        )
      )
    ),
    CsesRung(
      "length_100",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("length", 1 to 100),
          NominalParameter("value", 1 to 1000),
          NominalParameter("queries", 1 to 3)
        )
      )
    ),
    CsesRung(
      "length_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("length", 100000 to 200000),
          NominalParameter("value", 1 to 1000000000),
          NominalParameter("queries", 100000 to 200000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[StaticRangeMinimums]] =
    CsesFamily.families(rungs, StaticRangeMinimums(_, _))

/** CSES 1753, String Matching, `string_matching text pattern`: the places of
  * the text where the pattern occurs. A site is a text of n letters and a
  * pattern of m letters, n from the parameter `text` and m from the parameter
  * `pattern` and at least 1, each letter from the parameter `letter`, so few
  * that the pattern occurs often.
  */
final class StringMatching(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[StringMatching.Site](spelling, rung):

  val problem: String = "string_matching"

  val claim: String =
    "gezi.contest.corpora.reductions.StringMatchingReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[StringMatching.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.stringMatching(
          IArray.from(site.text),
          IArray.from(site.pattern)
        )
      )
    )

  protected def site(draws: Draws): (StringMatching.Site, Draws) =
    val (textLength, afterTextLength) =
      CsesFamily.drawnParameter(draws, nominal, "text")
    val (patternLength, afterPatternLength) =
      CsesFamily.drawnParameter(afterTextLength, nominal, "pattern")
    val letters = Repetition.range(nominal, "letter")
    rung.input match
      case RungInput.Written =>
        val (text, afterText) =
          CsesFamily.drawnValues(textLength, afterPatternLength)(
            CsesFamily.between(_, letters)
          )
        val (pattern, after) = CsesFamily.drawnValues(patternLength, afterText)(
          CsesFamily.between(_, letters)
        )
        (
          StringMatching.Site(
            SeededInput.Input.Written(text),
            SeededInput.Input.Written(pattern)
          ),
          after
        )
      case RungInput.Seeded =>
        val (textSeed, afterTextSeed) =
          CsesFamily.between(afterPatternLength, CsesFamily.seeds)
        val (patternSeed, after) =
          CsesFamily.between(afterTextSeed, CsesFamily.seeds)
        val text =
          SeededInput.Numbers(textSeed, textLength, letters.start, letters.end)
        val pattern = SeededInput.Numbers(
          patternSeed,
          patternLength,
          letters.start,
          letters.end
        )
        (
          StringMatching.Site(
            SeededInput.Input.Seeded(text),
            SeededInput.Input.Seeded(pattern)
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.stringMatching

  def arguments(
      problems: CsesProblems,
      site: StringMatching.Site
  ): Vector[ProblemTerm] =
    (site.textInput, site.patternInput) match
      case (
            SeededInput.Input.Written(text),
            SeededInput.Input.Written(pattern)
          ) =>
        val naturals = CsesEncodings.naturals(text ++ pattern)
        Vector(
          CsesEncodings.list(text.map(naturals)),
          CsesEncodings.list(pattern.map(naturals))
        )
      case (
            SeededInput.Input.Seeded(text),
            SeededInput.Input.Seeded(pattern)
          ) =>
        Vector(text.argument(problems), pattern.argument(problems))
      case _ =>
        throw IllegalStateException(
          s"a site's text and pattern are both written or both seeded: $site"
        )

  /** A solution that counts the occurrences that do not overlap, found left to
    * right, resuming after the end of each (`StringMatching.nonOverlapping`).
    */
  def wrongAnswers(
      site: StringMatching.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        StringMatching.nonOverlapping(site.text, site.pattern)
      )
    )

/** The sites, the non-overlapping count and the ladder of `StringMatching`. */
object StringMatching:

  /** The text and the pattern of a site, each written or seeded. */
  final case class Site(
      textInput: SeededInput.Input[Vector[Int]],
      patternInput: SeededInput.Input[Vector[Int]]
  ):

    /** The text. */
    def text: Vector[Int] = textInput.data

    /** The pattern. */
    def pattern: Vector[Int] = patternInput.data

    override def toString: String =
      s"Site(${textInput.described(_.toString)},${patternInput.described(_.toString)})"

  /** The occurrences found left to right where, after one, the search resumes
    * after its end, in O(n m) time.
    */
  def nonOverlapping(text: Vector[Int], pattern: Vector[Int]): BigInt =
    @scala.annotation.tailrec
    def found(place: Int, count: Int): Int =
      if place + pattern.size > text.size then count
      else if text.startsWith(pattern, place) then
        found(place + pattern.size, count + 1)
      else found(place + 1, count)
    BigInt(found(0, 0))

  /** The ladder: a text of up to 8 letters and a pattern of up to 3, and a text
    * of up to 120 and a pattern of up to 4, of two letters, and CSES's
    * constraints, 1 ≤ n ≤ 10^6, drawn from the upper half, and, for the
    * pattern, 5 ≤ m ≤ 15, at most four sites. MEASURED 2026-11-22 on 65bb56e89
    * by a scratch probe in contest-corpora's tests (CPUs 2 and 3 of
    * contest.slice, nice 10, the 1-minute load about 7), tabling(weak_head)
    * knowing top (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000
    * tables, each reading one normal form: of the single programs of the seeds
    * 0 to 19 at the bottom rung, the most tables were 943 (direct, 1,938 steps)
    * and 1,150 (respelled, 2,424 steps), of the repeated program of the seed
    * 20261031 at R = 4, 1,249 and 1,450 and at R = 256, 27,360 (direct, 66,104
    * steps) and 38,903 (respelled); of the single programs of the seeds 0 to 29
    * at the middle rung, 4,213 (direct, 9,375 steps) and 8,117 (respelled,
    * 19,014 steps), of the repeated program at R = 4, 8,121 and 16,322.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "text_8",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("text", 1 to 8),
          NominalParameter("pattern", 1 to 3),
          NominalParameter("letter", 0 to 1)
        )
      )
    ),
    CsesRung(
      "text_120",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("text", 1 to 120),
          NominalParameter("pattern", 1 to 4),
          NominalParameter("letter", 0 to 1)
        )
      )
    ),
    CsesRung(
      "text_1000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("text", 500000 to 1000000),
          NominalParameter("pattern", 5 to 15),
          NominalParameter("letter", 0 to 1)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[StringMatching]] =
    CsesFamily.families(rungs, StringMatching(_, _))

/** CSES 1660, Subarray Sums I, `subarray_sums x values`: the contiguous
  * subarrays that sum to x. A site is x, from the parameter `target`, and n
  * positive values, n from the parameter `count`, each from the parameter
  * `value`.
  */
final class SubarraySums(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[SubarraySums.Site](spelling, rung):

  val problem: String = "subarray_sums"

  val claim: String =
    "gezi.contest.corpora.reductions.SubarraySumsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[SubarraySums.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.subarraySums(
          site.target.toLong,
          IArray.from(site.values.map(_.toLong))
        )
      )
    )

  protected def site(draws: Draws): (SubarraySums.Site, Draws) =
    val (target, afterTarget) =
      CsesFamily.drawnParameter(draws, nominal, "target")
    val (values, after) = CsesFamily.drawnNumbers(
      afterTarget,
      nominal,
      rung.input,
      "count",
      "value"
    )
    (SubarraySums.Site(target, values.input), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.subarraySums

  def arguments(
      problems: CsesProblems,
      site: SubarraySums.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(site.target +: written)
        Vector(naturals(site.target), CsesEncodings.list(written.map(naturals)))
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.target), generator.argument(problems))

  /** A solution that counts only the subarrays that start at place 1, the
    * prefixes whose sum is x.
    */
  def wrongAnswers(
      site: SubarraySums.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        site.values.scanLeft(0L)(_ + _).tail.count(_ == site.target.toLong)
      )
    )

/** The sites and the ladder of `SubarraySums`. */
object SubarraySums:

  /** The target x and the values of a site. */
  final case class Site(target: Int, input: SeededInput.Input[Vector[Int]]):

    /** The values. */
    def values: Vector[Int] = input.data

    override def toString: String =
      s"Site($target,${input.described(_.toString)})"

  /** The ladder: up to 6 values, and up to 16, of at most 4, with x up to 8,
    * and CSES's constraints, 1 ≤ n ≤ 2 · 10^5, drawn from the upper half, 1 ≤ x
    * ≤ 100 and values from 1 to 10 (so that many subarrays reach x), at most
    * four sites. MEASURED 2026-11-22 on 65bb56e89 by a scratch probe in
    * contest-corpora's tests (CPUs 2 and 3 of contest.slice, nice 10, the
    * 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 2,284 (direct, 5,041 steps) and
    * 4,516 (respelled, 10,958 steps), of the repeated program of the seed
    * 20261031 at R = 4, 2,452 and 3,226, and at R = 256 both twins stopped at
    * the probe's 60,000 tables; of the single programs of the seeds 0 to 29 at
    * the middle rung, 12,684 (direct, 29,971 steps) and 27,234 (respelled,
    * 65,906 steps; 3 of the 30 above 20,000), of the repeated program at R = 4,
    * 19,208 and 51,230 (respelled).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "count_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("target", 1 to 8),
          NominalParameter("count", 1 to 6),
          NominalParameter("value", 1 to 4)
        )
      )
    ),
    CsesRung(
      "count_16",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("target", 1 to 8),
          NominalParameter("count", 1 to 16),
          NominalParameter("value", 1 to 4)
        )
      )
    ),
    CsesRung(
      "count_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("target", 1 to 100),
          NominalParameter("count", 100000 to 200000),
          NominalParameter("value", 1 to 10)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[SubarraySums]] =
    CsesFamily.families(rungs, SubarraySums(_, _))

/** CSES 1640, Sum of Two Values, `sum_of_two_values x values`: the pairs of two
  * different places whose values sum to x. A site is x, from the parameter
  * `target`, and n values, n from the parameter `count`, each from the
  * parameter `value`, a value repeated allowed.
  */
final class SumOfTwoValues(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[SumOfTwoValues.Site](spelling, rung):

  val problem: String = "sum_of_two_values"

  val claim: String =
    "gezi.contest.corpora.reductions.SumOfTwoValuesReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[SumOfTwoValues.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.sumOfTwoValues(
          site.target.toLong,
          IArray.from(site.values.map(_.toLong))
        )
      )
    )

  protected def site(draws: Draws): (SumOfTwoValues.Site, Draws) =
    val (target, afterTarget) =
      CsesFamily.drawnParameter(draws, nominal, "target")
    val (values, after) = CsesFamily.drawnNumbers(
      afterTarget,
      nominal,
      rung.input,
      "count",
      "value"
    )
    (SumOfTwoValues.Site(target, values.input), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.sumOfTwoValues

  def arguments(
      problems: CsesProblems,
      site: SumOfTwoValues.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(site.target +: written)
        Vector(naturals(site.target), CsesEncodings.list(written.map(naturals)))
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.target), generator.argument(problems))

  /** A solution that counts ordered pairs, i before j and j before i, twice the
    * answer; and one that lets a place pair with itself, the pairs of places i
    * ≤ j whose values sum to x, the answer and the places of value x / 2.
    */
  def wrongAnswers(
      site: SumOfTwoValues.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Binary(digits) =>
      val pairs = CsesFamily.naturalOf(digits)
      val halves = if site.target % 2 == 0 then
        site.values.count(_ == site.target / 2)
      else 0
      Vector(
        NativeValue.natural(pairs * 2),
        NativeValue.natural(pairs + halves)
      )
    case other => throw IllegalArgumentException(s"no natural: $other")

/** The sites and the ladder of `SumOfTwoValues`. */
object SumOfTwoValues:

  /** The target x and the values of a site. */
  final case class Site(target: Int, input: SeededInput.Input[Vector[Int]]):

    /** The values. */
    def values: Vector[Int] = input.data

    override def toString: String =
      s"Site($target,${input.described(_.toString)})"

  /** The ladder: up to 6 values, and up to 32, of at most 4, with x from 2 to 8
    * so that pairs of values reach it, and CSES's constraints, 1 ≤ n ≤ 2 ·
    * 10^5, drawn from the upper half, 1 ≤ x ≤ 2 · 10^6 and values from 1 to
    * 10^6, at most four sites. MEASURED 2026-11-22 on 65bb56e89 by a scratch
    * probe in contest-corpora's tests (CPUs 2 and 3 of contest.slice, nice 10,
    * the 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 1,276 (direct, 2,669 steps) and
    * 1,923 (respelled, 4,248 steps), of the repeated program of the seed
    * 20261031 at R = 4, 1,656 and 2,417 and at R = 256, 31,313 (direct, 73,880
    * steps) and 42,958 (respelled); of the single programs of the seeds 0 to 29
    * at the middle rung, 5,241 (direct, 11,559 steps) and 7,175 (respelled,
    * 16,670 steps), of the repeated program at R = 4, 4,152 and 6,540. At the
    * top rung the trap needs an even x and a value x / 2 among the values,
    * which the seed 20261031 does not offer.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "count_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("target", 2 to 8),
          NominalParameter("count", 1 to 6),
          NominalParameter("value", 1 to 4)
        )
      )
    ),
    CsesRung(
      "count_32",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("target", 2 to 8),
          NominalParameter("count", 1 to 32),
          NominalParameter("value", 1 to 4)
        )
      )
    ),
    CsesRung(
      "count_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("target", 1 to 2000000),
          NominalParameter("count", 100000 to 200000),
          NominalParameter("value", 1 to 1000000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[SumOfTwoValues]] =
    CsesFamily.families(rungs, SumOfTwoValues(_, _))

/** The tree of a site of `TreeDiameter` and of `TreeMatching`: n nodes and n
  *   - 1 edges, written (`TreeSite.drawn`) with each node k from 2 to n joined
  *     to a parent drawn from 1 to k - 1, each edge written from either end
  *     with even odds, the edges shuffled; seeded, `SeededInput.TreeEdges`.
  */
object TreeSite:

  /** The node count n and the edges of a site. */
  final case class Site(
      nodes: Int,
      input: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The edges. */
    def edges: Vector[(Int, Int)] = input.data

    override def toString: String =
      s"Site($nodes,${input.described(_.toString)})"

  /** The site of n nodes drawn from the parameter `nodes`. */
  def drawn(
      draws: Draws,
      nominal: NominalRanges,
      input: RungInput
  ): (Site, Draws) =
    val (nodes, afterNodes) = CsesFamily.drawnParameter(draws, nominal, "nodes")
    input match
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterNodes, CsesFamily.seeds)
        (
          Site(
            nodes,
            SeededInput.Input.Seeded(SeededInput.TreeEdges(seed, nodes))
          ),
          after
        )
      case RungInput.Written =>
        val (written, afterEdges) =
          (2 to nodes).foldLeft((Vector.empty[(Int, Int)], afterNodes)) {
            case ((found, current), node) =>
              val (parent, afterParent) =
                CsesFamily.between(current, 1 to node - 1)
              val (flipped, afterFlipped) =
                afterParent.chosen(Vector(false, true))
              (
                found :+ (if flipped then (node, parent) else (parent, node)),
                afterFlipped
              )
          }
        val (edges, after) = CsesFamily.shuffled(written, afterEdges)
        (Site(nodes, SeededInput.Input.Written(edges)), after)

  /** The terms of a site: n, then the edges. */
  def arguments(problems: CsesProblems, site: Site): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(
          site.nodes +: written.flatMap((first, second) =>
            Vector(first, second)
          )
        )
        Vector(
          naturals(site.nodes),
          CsesEncodings.list(
            written.map((first, second) =>
              CsesEncodings.pair(naturals(first), naturals(second))
            )
          )
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.nodes), generator.argument(problems))

  /** The greatest depth of a node, its distance from node 1, found level by
    * level in O(n) time.
    */
  def greatestDepth(site: Site): Int =
    val neighbours = site.edges
      .flatMap((first, second) => Vector((first, second), (second, first)))
      .groupMap(_._1)(_._2)
    @scala.annotation.tailrec
    def deeper(frontier: Vector[(Int, Int)], depth: Int): Int =
      val next = frontier.flatMap((node, parent) =>
        neighbours
          .getOrElse(node, Vector.empty)
          .filter(_ != parent)
          .map((_, node))
      )
      if next.isEmpty then depth else deeper(next, depth + 1)
    deeper(Vector((1, 0)), 0)

/** CSES 1131, Tree Diameter, `tree_diameter n edges`: the greatest number of
  * edges on a path between two nodes of a tree. A site is a tree (`TreeSite`),
  * n from the parameter `nodes`.
  */
final class TreeDiameter(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[TreeSite.Site](spelling, rung):

  val problem: String = "tree_diameter"

  val claim: String =
    "gezi.contest.corpora.reductions.TreeDiameterReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[TreeSite.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.treeDiameter(site.nodes, site.edges))
    )

  protected def site(draws: Draws): (TreeSite.Site, Draws) =
    TreeSite.drawn(draws, nominal, rung.input)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.treeDiameter

  def arguments(
      problems: CsesProblems,
      site: TreeSite.Site
  ): Vector[ProblemTerm] = TreeSite.arguments(problems, site)

  /** A solution that answers the greatest depth from node 1, the edges on the
    * longest path that starts at node 1, as if the longest path always did.
    */
  def wrongAnswers(
      site: TreeSite.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(TreeSite.greatestDepth(site)))

/** The ladder of `TreeDiameter`. */
object TreeDiameter:

  /** The ladder: trees of up to 4 nodes, and up to 6 (at 7, the respelled
    * repeated program of R = 4 stopped at the probe's 60,000 tables), and
    * CSES's constraint, 1 ≤ n ≤ 2 · 10^5, drawn from the upper half, at most
    * four sites. MEASURED 2026-11-22 on 65bb56e89 by a scratch probe in
    * contest-corpora's tests (CPUs 2 and 3 of contest.slice, nice 10, the
    * 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 4,120 (direct, 9,475 steps) and
    * 6,602 (respelled, 15,613 steps), of the repeated program of the seed
    * 20261031 at R = 4, 3,256 and 4,445, and at R = 256 both twins stopped at
    * the probe's 60,000; of the single programs at the middle rung, 15,260
    * (direct, 36,371 steps) and 30,204 (respelled, 73,751 steps), of the
    * repeated program at R = 4, 23,238 and 30,074.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "nodes_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("nodes", 1 to 4))
      )
    ),
    CsesRung(
      "nodes_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("nodes", 1 to 6))
      )
    ),
    CsesRung(
      "nodes_200000",
      NominalRanges(
        1 to 4,
        Vector(NominalParameter("nodes", 100000 to 200000))
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[TreeDiameter]] =
    CsesFamily.families(rungs, TreeDiameter(_, _))

/** CSES 1130, Tree Matching, `tree_matching n edges`: the most edges of a tree
  * that share no node. A site is a tree (`TreeSite`), n from the parameter
  * `nodes`.
  */
final class TreeMatching(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[TreeSite.Site](spelling, rung):

  val problem: String = "tree_matching"

  val claim: String =
    "gezi.contest.corpora.reductions.TreeMatchingReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[TreeSite.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.treeMatching(site.nodes, site.edges))
    )

  protected def site(draws: Draws): (TreeSite.Site, Draws) =
    TreeSite.drawn(draws, nominal, rung.input)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.treeMatching

  def arguments(
      problems: CsesProblems,
      site: TreeSite.Site
  ): Vector[ProblemTerm] = TreeSite.arguments(problems, site)

  /** A solution that answers half the nodes, rounded down, as if every node
    * could be matched.
    */
  def wrongAnswers(
      site: TreeSite.Site,
      answer: NativeValue
  ): Vector[NativeValue] = Vector(NativeValue.natural(site.nodes / 2))

/** The ladder of `TreeMatching`. */
object TreeMatching:

  /** The ladder: trees of up to 4 nodes, and up to 8 (at 10, 1 of 30 respelled
    * single programs stopped at the probe's 60,000 tables), and CSES's
    * constraint, 1 ≤ n ≤ 2 · 10^5, drawn from the upper half, at most four
    * sites. MEASURED 2026-11-22 on 65bb56e89 by a scratch probe in
    * contest-corpora's tests (CPUs 2 and 3 of contest.slice, nice 10, the
    * 1-minute load about 7), tabling(weak_head) knowing top
    * (`ReadingState.knowingTop`) within 20,000,000 steps and 60,000 tables,
    * each reading one normal form: of the single programs of the seeds 0 to 19
    * at the bottom rung, the most tables were 1,326 (direct, 2,820 steps) and
    * 2,243 (respelled, 5,119 steps), of the repeated program of the seed
    * 20261031 at R = 4, 1,811 and 2,472, and at R = 256, 54,917 (direct,
    * 134,575 steps) and the respelled twin stopped at the probe's 60,000; of
    * the single programs of the seeds 0 to 29 at the middle rung, 6,514
    * (direct, 15,570 steps) and 14,596 (respelled, 35,852 steps), of the
    * repeated program at R = 4, 4,898 and 10,233.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "nodes_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("nodes", 1 to 4))
      )
    ),
    CsesRung(
      "nodes_8",
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("nodes", 1 to 8))
      )
    ),
    CsesRung(
      "nodes_200000",
      NominalRanges(
        1 to 4,
        Vector(NominalParameter("nodes", 100000 to 200000))
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[TreeMatching]] =
    CsesFamily.families(rungs, TreeMatching(_, _))
