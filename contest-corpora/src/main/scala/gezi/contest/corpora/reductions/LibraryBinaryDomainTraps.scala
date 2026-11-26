package gezi.contest.corpora.reductions

import gezi.frontend.Term
import gezi.frontend.Term.*

/** The standard library's binary API applied to arguments outside the
  * binary type: at R sites, each written out with no let around it, whether
  * the sum of two binary numerals equals a third,
  * `merge_binary_equality (merge_binary_plus a b) c`, the sites collected in
  * the library's list. The respelled site writes the same calls through
  * compose and η-expansions,
  * `compose (\s. merge_binary_equality s c) (\x. merge_binary_plus a x) b`.
  *
  * The operands are binary numerals of 20 to 30 digits at the nominal
  * ranges. At a drawn nonempty subset of the sites, of 1 to max(1, R / 4)
  * sites (so one site when R is below 8), the larger operand is a numeral with leading
  * zeros: the canonical numeral of its value with the binary_zero at its
  * end replaced by one to four binary_even over binary_zero, a term outside
  * the binary type, since the type filter (`binary`, in
  * `corpora/library/binary`) gives top on
  * `binary_even binary_zero`. At such a site c is the canonical numeral of
  * a + b: merge_binary_plus keeps the leading zeros of its longer operand
  * (when its other operand runs out it returns the rest unchanged), and
  * merge_binary_equality compares the variants digit by digit, so the site
  * is false, while an entry that reads the operands as integers, adds them
  * and compares the integers answers true. At every other site the operands
  * are canonical and c is the canonical numeral of a + b or of a + b + 1,
  * drawn, so the answers differ across sites.
  *
  * The family's claim: each site's term is equal, by the β rule, the η rule
  * and the library terms' unfolding, to the Boolean the library terms' own semantics on
  * binary trees gives (`LibraryBinaryDomainTraps.sum`,
  * `LibraryBinaryDomainTraps.equal`), and the point's normal form is the
  * list of these Booleans in site order; `LibraryBinaryDomainTrapsReferenceTest`
  * checks it against tabling(weak_head)'s reading on small draws. Its purpose is to
  * catch an entry that converts values outside the binary type to integers
  * without checking their membership, which gives a false answer at every
  * site with leading zeros.
  *
  * The native solver: the library terms' semantics on trees, the sum by
  * merge_binary_plus's clauses and the comparison by
  * merge_binary_equality's, never through an integer. The draw throws when
  * a site with leading zeros has the same answer under the trees' semantics
  * as under the integers', so every such site is a trap.
  */
final class LibraryBinaryDomainTraps(spelling: Spelling, val nominal: NominalRanges)
    extends StandardLibraryFamily[LibraryBinaryDomainTraps.Drawn](spelling)
    with NativelySolved[LibraryBinaryDomainTraps.Drawn]:

  import LibraryBinaryDomainTraps.Drawn
  import LibraryBinaryDomainTraps.Numeral
  import LibraryBinaryDomainTraps.Pair
  import LibraryBinaryDomainTraps.Site
  import LibraryBinaryDomainTraps.definitionalAnswer
  import LibraryBinaryDomainTraps.drawnBetween
  import LibraryBinaryDomainTraps.integerAnswer
  import LibraryBinaryDomainTraps.term

  val family: String = LibraryBinaryDomainTraps.name

  val claim: String = LibraryBinaryDomainTraps.claim

  /** The native solver: each site's answer by the trees' semantics. */
  def solved(drawn: Drawn): Vector[NativeValue] = drawn.sites.map(site => NativeValue.Truth(definitionalAnswer(site)))

  protected def drawn(group: ReductionGroup, draws: Draws, repetitions: Int): Drawn =
    val (pairs, afterPairs) = draws.distinct(repetitions)(drawnPair)
    val (trapCount, afterCount) = afterPairs.number(1 to math.max(1, repetitions / 4))
    val (trapSites, afterTraps) = afterCount.distinct(trapCount)(_.number(0 to repetitions - 1))
    val (sites, _) = pairs.zipWithIndex.foldLeft((Vector.empty[Site], afterTraps))((drawnSites, pairAndIndex) =>
      val (before, beforeDraws) = drawnSites
      val (pair, index) = pairAndIndex
      val (site, afterSite) = drawnSite(pair, trapSites.contains(index), beforeDraws)
      (before :+ site, afterSite)
    )
    Drawn(sites)

  /** The operands' values: the larger of b digits, b drawn from `bits`, and
    * the smaller of b - s digits, s drawn from `shorter_by`, the larger at
    * most 2^b - 2^(b - s), so that their sum has b digits.
    */
  private def drawnPair(draws: Draws): (Pair, Draws) =
    val (digits, afterDigits) = Repetition.drawnNumber(draws, nominal, "bits")
    val (shorterBy, afterShorterBy) = Repetition.drawnNumber(afterDigits, nominal, "shorter_by")
    val smallerDigits = digits - shorterBy
    require(shorterBy >= 2 && smallerDigits >= 1, s"no pair of $digits and $smallerDigits digits whose sum has $digits")
    val (larger, afterLarger) = drawnBetween(afterShorterBy, BigInt(1) << (digits - 1), (BigInt(1) << digits) - (BigInt(1) << smallerDigits))
    val (smaller, afterSmaller) = drawnBetween(afterLarger, BigInt(1) << (smallerDigits - 1), (BigInt(1) << smallerDigits) - 1)
    (Pair(larger, smaller), afterSmaller)

  /** The site of the pair: which operand comes first drawn; at a trap site
    * the larger padded with leading zeros and c the canonical sum, at
    * another site both canonical and c the sum or the sum plus one, drawn.
    * Throws when a trap site's answer under the trees' semantics is its
    * answer under the integers', or when another site's are not the same.
    */
  private def drawnSite(pair: Pair, trap: Boolean, draws: Draws): (Site, Draws) =
    val (largerFirst, afterOrder) = draws.number(0 to 1)
    val total = pair.larger + pair.smaller
    val (larger, compared, afterSite) =
      if trap then
        val (padding, afterPadding) = Repetition.drawnNumber(afterOrder, nominal, "padding")
        (Numeral(pair.larger, padding), Numeral(total, 0), afterPadding)
      else
        val (offset, afterOffset) = afterOrder.number(0 to 1)
        (Numeral(pair.larger, 0), Numeral(total + offset, 0), afterOffset)
    val smaller = Numeral(pair.smaller, 0)
    val site =
      if largerFirst == 1 then Site(larger, smaller, compared)
      else Site(smaller, larger, compared)
    val definitional = definitionalAnswer(site)
    val roundTrip = integerAnswer(site)
    if trap && definitional == roundTrip then
      throw IllegalStateException(s"not a domain trap: $site answers $definitional on trees and on integers")
    if !trap && definitional != roundTrip then
      throw IllegalStateException(s"a canonical site answers $definitional on trees and $roundTrip on integers: $site")
    (site, afterSite)

  private def site(terms: StandardLibraryTerms, drawnSite: Site): ProblemTerm =
    import terms.*
    val left = term(terms, drawnSite.left.tree)
    val right = term(terms, drawnSite.right.tree)
    val compared = term(terms, drawnSite.compared.tree)
    spelling match
      case Spelling.Direct => binaryEquality(binaryPlus(left)(right))(compared)
      case Spelling.Respelled =>
        compose(λ(total => binaryEquality(total)(compared)))(λ(addend => binaryPlus(left)(addend)))(right)

  protected def program(terms: StandardLibraryTerms, drawn: Drawn): ProblemTerm = terms.list(drawn.sites.map(site(terms, _)))

  protected def singlePrograms(terms: StandardLibraryTerms, drawn: Drawn): Vector[ProblemTerm] = drawn.sites.map(site(terms, _))

/** The draws, the trees' semantics, the nominal ranges and the variants of
  * `LibraryBinaryDomainTraps`.
  */
object LibraryBinaryDomainTraps:

  /** A binary tree as the library's constructors build it: binary_zero,
    * binary_even h (the value 2h) and binary_odd h (the value 2h + 1).
    */
  enum Tree:
    case Zero
    case Even(half: Tree)
    case Odd(half: Tree)

  /** A numeral: the canonical tree of the value with its binary_zero
    * replaced by `padding` binary_even over binary_zero; canonical when the
    * padding is zero.
    */
  final case class Numeral(value: BigInt, padding: Int):
    require(value >= 0 && padding >= 0, s"no numeral of $value with $padding leading zeros")

    /** The numeral's tree. */
    def tree: Tree = padded(value, padding)

  /** The operands' values of a site, the larger first. */
  final case class Pair(larger: BigInt, smaller: BigInt)

  /** A site: `merge_binary_equality (merge_binary_plus left right) compared`. */
  final case class Site(left: Numeral, right: Numeral, compared: Numeral)

  /** The sites, in order. */
  final case class Drawn(sites: Vector[Site])

  /** The canonical tree of the value with its zero replaced by `padding`
    * evens over zero.
    */
  def padded(value: BigInt, padding: Int): Tree =
    if value == 0 then (1 to padding).foldLeft(Tree.Zero: Tree)((inner, _) => Tree.Even(inner))
    else if value.testBit(0) then Tree.Odd(padded(value >> 1, padding))
    else Tree.Even(padded(value >> 1, padding))

  /** The tree's value. */
  def value(tree: Tree): BigInt = tree match
    case Tree.Zero       => BigInt(0)
    case Tree.Even(half) => value(half) * 2
    case Tree.Odd(half)  => value(half) * 2 + 1

  /** merge_binary_increment's clauses: 0 + 1 = 1, 2h + 1, (2g + 1) + 1 =
    * 2(g + 1).
    */
  def increment(tree: Tree): Tree = tree match
    case Tree.Zero       => Tree.Odd(Tree.Zero)
    case Tree.Even(half) => Tree.Odd(half)
    case Tree.Odd(half)  => Tree.Even(increment(half))

  /** merge_binary_plus's clauses: a zero operand gives the other operand
    * unchanged; two halves are added, with a carry for two odd operands.
    */
  def sum(left: Tree, right: Tree): Tree = (left, right) match
    case (Tree.Zero, _)                     => right
    case (_, Tree.Zero)                     => left
    case (Tree.Even(half), Tree.Even(other)) => Tree.Even(sum(half, other))
    case (Tree.Even(half), Tree.Odd(other))  => Tree.Odd(sum(half, other))
    case (Tree.Odd(half), Tree.Even(other))  => Tree.Odd(sum(half, other))
    case (Tree.Odd(half), Tree.Odd(other))   => Tree.Even(increment(sum(half, other)))

  /** merge_binary_equality's clauses: the same variant and equal halves. */
  def equal(left: Tree, right: Tree): Boolean = (left, right) match
    case (Tree.Zero, Tree.Zero)               => true
    case (Tree.Even(half), Tree.Even(other)) => equal(half, other)
    case (Tree.Odd(half), Tree.Odd(other))   => equal(half, other)
    case _                                   => false

  /** The site's answer under the library terms' semantics on trees. Asserts that
    * the sum's tree has the sum of the operands' values.
    */
  def definitionalAnswer(site: Site): Boolean =
    val total = sum(site.left.tree, site.right.tree)
    assert(value(total) == site.left.value + site.right.value, s"merge_binary_plus's tree of $site has another value")
    equal(total, site.compared.tree)

  /** The site's answer when every numeral is read as its integer. */
  def integerAnswer(site: Site): Boolean = site.left.value + site.right.value == site.compared.value

  /** The tree's term, built with binary_zero, binary_even and binary_odd. */
  def term(terms: StandardLibraryTerms, tree: Tree): ProblemTerm =
    import terms.*
    tree match
      case Tree.Zero       => binaryZero
      case Tree.Even(half) => binaryEven(term(terms, half))
      case Tree.Odd(half)  => binaryOdd(term(terms, half))

  /** A value from low to high, inclusive, read from two draws of 15 bits
    * each, so up to 2^30 values.
    */
  def drawnBetween(draws: Draws, low: BigInt, high: BigInt): (BigInt, Draws) =
    require(low <= high && high - low < (BigInt(1) << 30), s"no value is drawn between $low and $high")
    val (lowBits, afterLow) = draws.number(0 to Draws.highBitsCount - 1)
    val (highBits, afterHigh) = afterLow.number(0 to Draws.highBitsCount - 1)
    (low + ((BigInt(highBits) << 15) | BigInt(lowBits)) % (high - low + 1), afterHigh)

  /** The family's name. */
  val name: String = "repeated_library_binary_domain_traps"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String = "gezi.contest.corpora.reductions.LibraryBinaryDomainTrapsReferenceTest"

  /** The nominal ranges of the round's points: the larger operand of 20 to
    * 30 digits, the smaller 2 to 8 digits shorter, one to four leading
    * zeros at a trap site, at R up to 16. weak_head's reading of a nominal
    * site was not measured.
    */
  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(16),
    Vector(NominalParameter("bits", 20 to 30), NominalParameter("shorter_by", 2 to 8), NominalParameter("padding", 1 to 4))
  )

  /** The family in both spellings at the round's nominal ranges. */
  val variants: Vector[LibraryBinaryDomainTraps] = Repetition.spellings.map(LibraryBinaryDomainTraps(_, nominal))
