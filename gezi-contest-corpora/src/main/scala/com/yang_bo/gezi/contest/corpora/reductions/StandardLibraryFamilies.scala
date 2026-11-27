package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** A repeated family built from the standard library's terms
  * (`StandardLibraryTerms`, the group's `standardLibrary`): its program and its
  * single programs are closed terms that hold the library's terms, so that a
  * point carries the bodies and no name.
  */
abstract class StandardLibraryFamily[Drawn](val spelling: Spelling)
    extends RepeatedFamily[Drawn]:

  /** The family's name, the first part of its stem. */
  def family: String

  final def stem: String = s"$family/${Repetition.spellingName(spelling)}"

  /** The family's name alone: the twins of one family draw the same data. */
  final override def drawStem: String = family

  /** The repeated program of the draws, built from the library's terms. */
  protected def program(terms: StandardLibraryTerms, drawn: Drawn): ProblemTerm

  /** The single-input programs of the draws, built from the library's terms. */
  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: Drawn
  ): Vector[ProblemTerm]

  protected final def repeated(
      group: ReductionGroup,
      drawn: Drawn
  ): ProblemTerm = program(group.standardLibrary, drawn)

  protected final def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    singlePrograms(group.standardLibrary, drawn)

/** Whether n * 2^m + k is even, at R distinct triples (n, m, k):
  * `even (nat_fold (nat_fold n double m) successor k)`, the function let bound
  * once and applied at every site (`StandardLibraryTerms.sites`). The respelled
  * function is the same computation through compose and an η-expanded double,
  * `compose even (\x. nat_fold x successor k) (nat_fold n (\y. double y) m)`.
  *
  * Its work is the doubling: read directly, n * 2^m is a Scott numeral of that
  * many successors, while the natives double and even of the baseline's backend
  * take one step for each double; the parity depends on k when m is positive,
  * so the answers differ across sites.
  *
  * The native solver: the parity of n * 2^m + k, a Boolean.
  */
final class LibraryDoublingParities(
    spelling: Spelling,
    val nominal: NominalRanges
) extends StandardLibraryFamily[LibraryDoublingParities.Drawn](spelling)
    with NativelySolved[LibraryDoublingParities.Drawn]:

  import LibraryDoublingParities.Triple

  val family: String = "repeated_library_doubling_parities"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryDoublingParitiesReferenceTest"

  def solved(drawn: LibraryDoublingParities.Drawn): Vector[NativeValue] =
    LibraryDoublingParities.parities(drawn)

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryDoublingParities.Drawn =
    LibraryDoublingParities.Drawn(draws.distinct(repetitions)(triple)._1)

  private def triple(draws: Draws): (Triple, Draws) =
    val (number, afterNumber) = Repetition.drawnNumber(draws, nominal, "number")
    val (doublings, afterDoublings) =
      Repetition.drawnNumber(afterNumber, nominal, "doublings")
    val (addend, afterAddend) =
      Repetition.drawnNumber(afterDoublings, nominal, "addend")
    (Triple(number, doublings, addend), afterAddend)

  private def arguments(
      terms: StandardLibraryTerms,
      triple: Triple
  ): Vector[ProblemTerm] =
    Vector(
      terms.numeral(triple.number),
      terms.numeral(triple.doublings),
      terms.numeral(triple.addend)
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryDoublingParities.Drawn
  ): ProblemTerm =
    terms.sites(
      LibraryDoublingParities.function(terms, spelling),
      drawn.triples.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryDoublingParities.Drawn
  ): Vector[ProblemTerm] =
    val function = LibraryDoublingParities.function(terms, spelling)
    drawn.triples.map(triple => applied(function, arguments(terms, triple)))

/** The draws of `LibraryDoublingParities`. */
object LibraryDoublingParities:

  /** The data of a site: n, m and k. */
  final case class Triple(number: Int, doublings: Int, addend: Int)

  /** The triples of the sites. */
  final case class Drawn(triples: Vector[Triple])

  /** Whether n * 2^m + k is even at each site. */
  def parities(drawn: Drawn): Vector[NativeValue] =
    drawn.triples.map(triple =>
      NativeValue.Truth(
        ((BigInt(triple.number) << triple.doublings) + triple.addend) % 2 == 0
      )
    )

  /** The function of n, m and k in the spelling. */
  def function(terms: StandardLibraryTerms, spelling: Spelling): ProblemTerm =
    import terms.*
    spelling match
      case Spelling.Direct =>
        λ(number =>
          λ(doublings =>
            λ(addend =>
              even(
                natFold(natFold(number)(double)(doublings))(successor)(addend)
              )
            )
          )
        )
      case Spelling.Respelled =>
        λ(number =>
          λ(doublings =>
            λ(addend =>
              compose(even)(λ(doubled => natFold(doubled)(successor)(addend)))(
                natFold(number)(λ(value => double(value)))(doublings)
              )
            )
          )
        )

  /** The nominal ranges of the round's points: n from 1 to 3, m from 4 to 10, k
    * from 0 to 7; 168 distinct triples. weak_head read the single sites (1, 8,
    * 0), (1, 10, 0) and (1, 12, 0) in 85,269, 381,973 and 1,691,669 steps, and
    * (3, 12, 7) in 4,125,372 (2026-10-31), so m up to 10 keeps the reference's
    * reading of tens of sites within the 20,000,000 steps of `judgePointsFile`.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(3 * 7 * 8),
    Vector(
      NominalParameter("number", 1 to 3),
      NominalParameter("doublings", 4 to 10),
      NominalParameter("addend", 0 to 7)
    )
  )

  /** The family in both spellings at the round's nominal ranges. */
  val variants: Vector[LibraryDoublingParities] =
    Repetition.spellings.map(LibraryDoublingParities(_, nominal))

/** Whether the natural whose binary digits a list holds is even, at R distinct
  * lists of digits (each zero or one, the head the least significant): the list
  * read by Horner's rule,
  * `even (list_fold zero (\d. \a. nat_fold (double a) successor d) digits)`,
  * written out at every site with no let around it. The respelled site writes
  * the step through compose,
  * `compose even (list_fold zero (\d. compose (\a. nat_fold a successor d) double)) digits`.
  *
  * Its work is the doubling at each digit: read directly, the value is a Scott
  * numeral below 2^L for L digits, while the natives double and even take one
  * step for each digit. The parity is the head digit's.
  *
  * The native solver: whether each list's value is even, which is whether its
  * head digit, the least significant, is zero, the empty list's value zero
  * being even; a Boolean.
  */
final class LibraryBinaryParities(
    spelling: Spelling,
    val nominal: NominalRanges
) extends StandardLibraryFamily[LibraryBinaryParities.Drawn](spelling)
    with NativelySolved[LibraryBinaryParities.Drawn]:

  val family: String = "repeated_library_binary_parities"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryBinaryParitiesReferenceTest"

  def solved(drawn: LibraryBinaryParities.Drawn): Vector[NativeValue] =
    LibraryBinaryParities.parities(drawn)

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryBinaryParities.Drawn =
    LibraryBinaryParities.Drawn(draws.distinct(repetitions)(digits)._1)

  private def digits(draws: Draws): (Vector[Int], Draws) =
    val (length, afterLength) = Repetition.drawnNumber(draws, nominal, "length")
    (1 to length).foldLeft((Vector.empty[Int], afterLength))((drawn, _) =>
      val (before, beforeDraws) = drawn
      val (digit, afterDigit) = beforeDraws.number(0 to 1)
      (before :+ digit, afterDigit)
    )

  private def site(
      terms: StandardLibraryTerms,
      digits: Vector[Int]
  ): ProblemTerm =
    LibraryBinaryParities.site(terms, spelling, digits)

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryBinaryParities.Drawn
  ): ProblemTerm =
    terms.list(drawn.lists.map(site(terms, _)))

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryBinaryParities.Drawn
  ): Vector[ProblemTerm] =
    drawn.lists.map(site(terms, _))

/** The draws of `LibraryBinaryParities`. */
object LibraryBinaryParities:

  /** The digits of each site. */
  final case class Drawn(lists: Vector[Vector[Int]])

  /** Whether each list's value is even: whether its head digit is zero. */
  def parities(drawn: Drawn): Vector[NativeValue] =
    drawn.lists.map(digits =>
      NativeValue.Truth(digits.headOption.forall(_ == 0))
    )

  /** The site over the digits in the spelling. */
  def site(
      terms: StandardLibraryTerms,
      spelling: Spelling,
      digits: Vector[Int]
  ): ProblemTerm =
    import terms.*
    val list = terms.list(digits.map(numeral))
    spelling match
      case Spelling.Direct =>
        even(
          listFold(zero)(
            λ(digit =>
              λ(accumulated => natFold(double(accumulated))(successor)(digit))
            )
          )(list)
        )
      case Spelling.Respelled =>
        compose(even)(
          listFold(zero)(
            λ(digit =>
              compose(λ(accumulated => natFold(accumulated)(successor)(digit)))(
                double
              )
            )
          )
        )(list)

  /** The nominal ranges of the round's points: lists of 4 to 11 digits; more
    * than 256 distinct lists. weak_head read the single sites of the digits
    * 1011, 11111111 and 111111111111 in 4,519, 98,433 and 1,904,513 steps
    * (2026-10-31), so 11 digits keep the reference's reading of tens of sites
    * within the 20,000,000 steps of `judgePointsFile`.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitions,
    Vector(NominalParameter("length", 4 to 11))
  )

  /** The family in both spellings at the round's nominal ranges. */
  val variants: Vector[LibraryBinaryParities] =
    Repetition.spellings.map(LibraryBinaryParities(_, nominal))

/** `LibraryDoublingParities` with no work shared between sites: whether n * 2^m
  * + k is even, at R sites whose numbers n are distinct, the function and both
  * spellings those of `LibraryDoublingParities`, let bound once and applied at
  * every site.
  *
  * The number n is odd and drawn, distinct, from a wide range; m and k are
  * drawn for each site after its n. The doublings of a site are n * 2^i for i
  * up to m, and an odd n makes n * 2^i determine n and i, so no value a site
  * doubles is one another site doubles. Its work is the doubling, as in
  * `LibraryDoublingParities`, now distinct at every site.
  *
  * The family's name and its claim are parameters, so that one construction
  * serves the base family and its scaled variant
  * (`LibraryUnsharedDoublings.variants`,
  * `LibraryUnsharedDoublings.largeVariants`).
  */
final class LibraryUnsharedDoublings(
    spelling: Spelling,
    val nominal: NominalRanges,
    val family: String,
    val claim: String
) extends StandardLibraryFamily[LibraryDoublingParities.Drawn](spelling)
    with NativelySolved[LibraryDoublingParities.Drawn]:

  import LibraryDoublingParities.Triple

  /** The native solver: whether n * 2^m + k is even at each site. */
  def solved(drawn: LibraryDoublingParities.Drawn): Vector[NativeValue] =
    LibraryDoublingParities.parities(drawn)

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryDoublingParities.Drawn =
    val (numbers, afterNumbers) =
      draws.distinct(repetitions)(Repetition.drawnNumber(_, nominal, "number"))
    val (triples, _) =
      numbers.foldLeft((Vector.empty[Triple], afterNumbers))((drawn, number) =>
        val (before, beforeDraws) = drawn
        val (doublings, afterDoublings) =
          Repetition.drawnNumber(beforeDraws, nominal, "doublings")
        val (addend, afterAddend) =
          Repetition.drawnNumber(afterDoublings, nominal, "addend")
        (before :+ Triple(number, doublings, addend), afterAddend)
      )
    LibraryDoublingParities.Drawn(triples)

  private def arguments(
      terms: StandardLibraryTerms,
      triple: Triple
  ): Vector[ProblemTerm] =
    Vector(
      terms.numeral(triple.number),
      terms.numeral(triple.doublings),
      terms.numeral(triple.addend)
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryDoublingParities.Drawn
  ): ProblemTerm =
    terms.sites(
      LibraryDoublingParities.function(terms, spelling),
      drawn.triples.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryDoublingParities.Drawn
  ): Vector[ProblemTerm] =
    val function = LibraryDoublingParities.function(terms, spelling)
    drawn.triples.map(triple => applied(function, arguments(terms, triple)))

/** The nominal ranges and variants of `LibraryUnsharedDoublings`. */
object LibraryUnsharedDoublings:

  /** The nominal ranges of the round's points: n odd from 257 to 767, m from 5
    * to 6, k from 0 to 7, at R up to 16; 256 distinct numbers, whose products n
    * * 2^m run from 8,224 to 49,088. weak_head read the single site of the
    * smallest product, (257, 5, 0), in 1,294,911 steps (direct) and 1,295,055
    * (respelled), and that of the largest, (767, 6, 7), in 8,696,710 and
    * 8,696,982 (2026-11-01).
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(16),
    Vector(
      NominalParameter("number", Range.inclusive(257, 767, 2)),
      NominalParameter("doublings", 5 to 6),
      NominalParameter("addend", 0 to 7)
    )
  )

  /** The family's name. */
  val name: String = "repeated_library_unshared_doublings"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryUnsharedDoublingsReferenceTest"

  /** The family in both spellings at the round's nominal ranges. */
  val variants: Vector[LibraryUnsharedDoublings] =
    Repetition.spellings.map(LibraryUnsharedDoublings(_, nominal, name, claim))

  /** The scaled variant's name. */
  val largeName: String = "repeated_library_unshared_doublings_large"

  /** The test that checks the scaled variant's computed reference against
    * tabling(weak_head)'s reading on small draws.
    */
  val largeClaim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryUnsharedDoublingsLargeReferenceTest"

  /** The nominal ranges of the scaled variant, sized for a computed reference
    * and beyond any direct reading: n odd from 257 to 767, m from 12 to 16, k
    * from 0 to 7, at R up to 16; the products n * 2^m run from 1,052,672 to
    * 50,266,112. Extrapolated linearly in the product from the measurements of
    * `nominal` (1,294,911 steps at 8,224 and 8,696,710 at 49,088; not measured
    * at these sizes), weak_head's reading of the smallest site would take about
    * 1.6 * 10^8 steps and that of the largest about 9 * 10^9, against the
    * 20,000,000 of `judgePointsFile`. The native formula: the parity of n * 2^m
    * + k, which is k's for m > 0.
    */
  val largeNominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(16),
    Vector(
      NominalParameter("number", Range.inclusive(257, 767, 2)),
      NominalParameter("doublings", 12 to 16),
      NominalParameter("addend", 0 to 7)
    )
  )

  /** The scaled variant in the spelling at its nominal ranges. */
  def large(spelling: Spelling): LibraryUnsharedDoublings =
    LibraryUnsharedDoublings(spelling, largeNominal, largeName, largeClaim)

  /** The scaled variant in both spellings at its nominal ranges. */
  val largeVariants: Vector[LibraryUnsharedDoublings] =
    Repetition.spellings.map(large)

/** `LibraryBinaryParities` with no work shared between sites: whether the
  * natural whose binary digits a list holds is even, at R lists of one length,
  * the site and both spellings those of `LibraryBinaryParities`, written out at
  * every site with no let around it.
  *
  * Every list has the same length and ends in the digit one (its most
  * significant), so every site's value lies between 2^(L-1) and 2^L; a list is
  * drawn anew when its last `distinctSuffix` digits are those of an earlier
  * list. Horner's rule reads the list from its end, so two sites share at most
  * the values of their common suffix, of fewer than `distinctSuffix` digits,
  * below 2^(distinctSuffix - 1), while the doublings near the head, the bulk of
  * the work, are distinct.
  *
  * The family's name and its claim are parameters, so that one construction
  * serves the base family and its scaled variant
  * (`LibraryUnsharedBinary.variants`, `LibraryUnsharedBinary.largeVariants`).
  */
final class LibraryUnsharedBinary(
    spelling: Spelling,
    val nominal: NominalRanges,
    val distinctSuffix: Int,
    val family: String,
    val claim: String
) extends StandardLibraryFamily[LibraryBinaryParities.Drawn](spelling)
    with NativelySolved[LibraryBinaryParities.Drawn]:

  /** The native solver: whether each site's value is even, which is whether its
    * least significant digit, the head of its list, is zero
    * (`LibraryBinaryParities`: list_fold's step at a head d and a folded tail a
    * is d + 2a), the empty list's value zero being even.
    */
  def solved(drawn: LibraryBinaryParities.Drawn): Vector[NativeValue] =
    LibraryBinaryParities.parities(drawn)

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryBinaryParities.Drawn =
    val (suffixes, afterSuffixes) =
      draws.distinct(repetitions)(drawnDigits(distinctSuffix - 1))
    val prefixLength =
      Repetition.range(nominal, "length").start - distinctSuffix
    val (lists, _) = suffixes.foldLeft(
      (Vector.empty[Vector[Int]], afterSuffixes)
    )((drawn, suffix) =>
      val (before, beforeDraws) = drawn
      val (prefix, afterPrefix) = drawnDigits(prefixLength)(beforeDraws)
      (before :+ (prefix ++ suffix :+ 1), afterPrefix)
    )
    LibraryBinaryParities.Drawn(lists)

  /** `count` digits, each zero or one. */
  private def drawnDigits(count: Int)(draws: Draws): (Vector[Int], Draws) =
    (1 to count).foldLeft((Vector.empty[Int], draws))((drawn, _) =>
      val (before, beforeDraws) = drawn
      val (digit, afterDigit) = beforeDraws.number(0 to 1)
      (before :+ digit, afterDigit)
    )

  private def site(
      terms: StandardLibraryTerms,
      digits: Vector[Int]
  ): ProblemTerm =
    LibraryBinaryParities.site(terms, spelling, digits)

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryBinaryParities.Drawn
  ): ProblemTerm =
    terms.list(drawn.lists.map(site(terms, _)))

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryBinaryParities.Drawn
  ): Vector[ProblemTerm] =
    drawn.lists.map(site(terms, _))

/** The nominal ranges and variants of `LibraryUnsharedBinary`. */
object LibraryUnsharedBinary:

  /** The suffix length beyond which the round's lists differ: nine digits, the
    * last fixed to one, so 2^8 = 256 distinct suffixes, more than R.
    */
  val distinctSuffix: Int = 9

  /** The nominal ranges of the round's points: lists of 14 digits, the last
    * one, so values from 8,192 to 16,383, at R up to 16. weak_head read the
    * first two single sites of the seed 20261031 in 8,206,745 and 7,095,468
    * steps (direct) and 7,387,883 and 7,554,421 (respelled) (2026-11-01).
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(16),
    Vector(NominalParameter("length", 14 to 14))
  )

  /** The family's name. */
  val name: String = "repeated_library_unshared_binary"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryUnsharedBinaryReferenceTest"

  /** The family in both spellings at the round's nominal ranges. */
  val variants: Vector[LibraryUnsharedBinary] =
    Repetition.spellings.map(
      LibraryUnsharedBinary(_, nominal, distinctSuffix, name, claim)
    )

  /** The scaled variant's name. */
  val largeName: String = "repeated_library_unshared_binary_large"

  /** The test that checks the scaled variant's computed reference against
    * tabling(weak_head)'s reading on small draws.
    */
  val largeClaim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryUnsharedBinaryLargeReferenceTest"

  /** The nominal ranges of the scaled variant, sized for a computed reference
    * and beyond any direct reading: lists of 24 digits, the last one, so values
    * from 2^23 = 8,388,608 to 2^24 - 1 = 16,777,215, at R up to 16, with the
    * distinct suffix of `distinctSuffix` digits. Extrapolated linearly in the
    * value from the measurements of `nominal` (from 7,095,468 to 8,206,745
    * steps at 14 digits, values between 8,192 and 16,383; not measured at these
    * sizes), weak_head's reading of a site of 24 digits would take 2^10 times
    * as many, of the order of 10^9 to 10^10 steps, against the 20,000,000 of
    * `judgePointsFile`. The native formula: the parity of the value, which is
    * the head digit's.
    */
  val largeNominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(16),
    Vector(NominalParameter("length", 24 to 24))
  )

  /** The scaled variant in the spelling at its nominal ranges. */
  def large(spelling: Spelling): LibraryUnsharedBinary =
    LibraryUnsharedBinary(
      spelling,
      largeNominal,
      distinctSuffix,
      largeName,
      largeClaim
    )

  /** The scaled variant in both spellings at its nominal ranges. */
  val largeVariants: Vector[LibraryUnsharedBinary] =
    Repetition.spellings.map(large)

/** The powers of words of one width w (fixed_width, the library's words of w
  * bits): at R sites whose odd bases x are distinct, x^(k + 1) wrapped to w
  * bits, by k multiplications, `nat_fold x (\p. word_multiply w x p) k`, the
  * function let bound once and applied at every site to the word x and the
  * numeral k. The respelled function writes the step through compose and
  * identity, `nat_fold x (compose (word_multiply w x) identity) k`. The answer
  * is the word, w cells.
  *
  * Its work is the multiplications: read directly, each is word_multiply's
  * shift-and-add over w cells of booleans, while the backend's family `word`
  * (`com.yang_bo.gezi.jit.WordFamily`) holds a word as one integer of w bits. Every
  * multiplication of a site has that site's base x as its left operand, and the
  * bases are distinct across sites, so the operand pairs (x, p) of the
  * multiplications of two sites are distinct.
  */
final class LibraryUnsharedWordPowers(
    spelling: Spelling,
    val nominal: NominalRanges
) extends StandardLibraryFamily[LibraryUnsharedWordPowers.Drawn](spelling)
    with NativelySolved[LibraryUnsharedWordPowers.Drawn]:

  import LibraryUnsharedWordPowers.Power

  val family: String = LibraryUnsharedWordPowers.name

  /** The width of every word, the one value of the range `width`. */
  val width: Int =
    val widths = Repetition.range(nominal, "width")
    require(
      widths.size == 1 && widths.start >= 1,
      s"one positive width: $widths"
    )
    widths.start

  val claim: String = LibraryUnsharedWordPowers.claim

  /** The native solver: the words x^(k + 1) mod 2^w. */
  def solved(drawn: LibraryUnsharedWordPowers.Drawn): Vector[NativeValue] =
    drawn.powers.map(power =>
      NativeValue.Word(
        width,
        power.base.modPow(power.exponent + 1, BigInt(1) << width)
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryUnsharedWordPowers.Drawn =
    val (bases, afterBases) = draws.distinct(repetitions)(base)
    val (powers, _) =
      bases.foldLeft((Vector.empty[Power], afterBases))((drawn, base) =>
        val (before, beforeDraws) = drawn
        val (exponent, afterExponent) =
          Repetition.drawnNumber(beforeDraws, nominal, "exponent")
        (before :+ Power(base, exponent), afterExponent)
      )
    LibraryUnsharedWordPowers.Drawn(powers)

  /** An odd base below 2^w: its w - 1 upper bits drawn, each zero or one, the
    * least significant bit one.
    */
  private def base(draws: Draws): (BigInt, Draws) =
    (1 until width).foldLeft((BigInt(1), draws))((drawn, position) =>
      val (before, beforeDraws) = drawn
      val (bit, afterBit) = beforeDraws.number(0 to 1)
      (if bit == 1 then before.setBit(position) else before, afterBit)
    )

  private def arguments(
      terms: StandardLibraryTerms,
      power: Power
  ): Vector[ProblemTerm] =
    Vector(terms.word(width, power.base), terms.numeral(power.exponent))

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryUnsharedWordPowers.Drawn
  ): ProblemTerm =
    terms.sites(
      LibraryUnsharedWordPowers.function(terms, spelling, width),
      drawn.powers.map(arguments(terms, _))
    )

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryUnsharedWordPowers.Drawn
  ): Vector[ProblemTerm] =
    val function = LibraryUnsharedWordPowers.function(terms, spelling, width)
    drawn.powers.map(power => applied(function, arguments(terms, power)))

/** The draws, the function, the nominal ranges and the variants of
  * `LibraryUnsharedWordPowers`.
  */
object LibraryUnsharedWordPowers:

  /** The data of a site: the base x and the count k of multiplications. */
  final case class Power(base: BigInt, exponent: Int)

  /** The powers of the sites. */
  final case class Drawn(powers: Vector[Power])

  /** The function of x and k at the width in the spelling. */
  def function(
      terms: StandardLibraryTerms,
      spelling: Spelling,
      width: Int
  ): ProblemTerm =
    import terms.*
    val multiply = wordMultiply(numeral(width))
    spelling match
      case Spelling.Direct =>
        λ(base =>
          λ(exponent =>
            natFold(base)(λ(power => multiply(base)(power)))(exponent)
          )
        )
      case Spelling.Respelled =>
        λ(base =>
          λ(exponent =>
            natFold(base)(compose(multiply(base))(identity))(exponent)
          )
        )

  /** The family's name. */
  val name: String = "repeated_library_unshared_word_powers"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.LibraryUnsharedWordPowersReferenceTest"

  /** The nominal ranges of the round's points: words of width 32, bases odd and
    * distinct, 2^31 of them, k from 256 to 511, at R up to 16. weak_head read
    * the single sites (x, k) = (11, 2) at width 4 in 9,043 steps (direct) and
    * 9,087 (respelled), (201, 2) and (201, 4) at width 8 in 33,061 and 66,425
    * (direct), (40001, 2) at width 16 in 129,745, and (2147483647, 1) and
    * (2147483647, 2) at width 32 in 224,023 and 489,205 (direct) and 224,045
    * and 489,249 (respelled) (2026-11-01): about 265,000 steps for each
    * multiplication at width 32, so a site of the nominal ranges takes from
    * about 6.8 * 10^7 to 1.4 * 10^8 steps (extrapolated, not measured), against
    * the 20,000,000 of `judgePointsFile`. The native formula: x^(k + 1) mod
    * 2^32.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(16),
    Vector(
      NominalParameter("width", 32 to 32),
      NominalParameter("exponent", 256 to 511)
    )
  )

  /** The family in both spellings at the round's nominal ranges. */
  val variants: Vector[LibraryUnsharedWordPowers] =
    Repetition.spellings.map(LibraryUnsharedWordPowers(_, nominal))
