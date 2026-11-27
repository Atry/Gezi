package gezi.contest.corpora.reductions

/** The answers of the CSES problems of the fourth batch by their
  * definitions, computed in the tests at the small sizes of the families'
  * bottom rungs and of the point tables, as `CsesThirdBatchDefinitions`
  * computes the third batch's: each follows the problem's statement as its
  * file's header words it, not the best known algorithm. The power is the
  * exponent multiplied out, the gondolas are the least over every way to
  * leave a child alone or pair it with a later one that fits, the missing
  * number is the first of 1 to n that the list lacks, the runs, the
  * matches, the subarrays, the pairs and the range minima are enumerated by
  * their places, the diameter is the greatest least number of steps between
  * two nodes, and the matching the largest set of edges that share no node.
  */
object CsesFourthBatchDefinitions:

  private val modulus: BigInt = BigInt(CsesFamily.modulus)

  /** a^(b^c) modulo 10^9 + 7, the exponent multiplied out. */
  def exponentiationTwo(site: ExponentiationTwo.Site): NativeValue =
    NativeValue.natural(BigInt(site.base).modPow(BigInt(site.exponentBase).pow(site.exponentPower), modulus))

  /** The fewest gondolas: the first child goes alone or with a later one
    * that fits beside it, and the others go on.
    */
  def ferrisWheel(site: FerrisWheel.Site): NativeValue =
    def gondolas(weights: Vector[Int]): Int = weights match
      case first +: rest =>
        val alone = 1 + gondolas(rest)
        val paired = rest.indices.filter(index => first + rest(index) <= site.capacity).map(index => 1 + gondolas(rest.patch(index, Vector.empty, 1)))
        (alone +: paired).min
      case _ => 0
    NativeValue.natural(gondolas(site.weights))

  /** The first number from 1 to n that the list does not hold. */
  def missingNumber(site: MissingNumber.Site): NativeValue =
    NativeValue.natural((1 to site.upper).filter(number => !site.numbers.contains(number)).head)

  /** The greatest length of a segment whose letters are all equal. */
  def repetitions(site: Repetitions.Site): NativeValue =
    val segments = for
      first <- site.numbers.indices
      last <- first until site.numbers.size
      if site.numbers.slice(first, last + 1).forall(_ == site.numbers(first))
    yield last - first + 1
    NativeValue.natural(segments.max)

  /** The least value from place a to place b, summed over the queries. */
  def staticRangeMinimums(site: StaticRangeMinimums.Site): NativeValue =
    NativeValue.natural(site.queries.map((first, last) => BigInt(site.values.slice(first - 1, last).min)).sum)

  /** The places of the text where the pattern's letters are the text's from
    * there on.
    */
  def stringMatching(site: StringMatching.Site): NativeValue =
    NativeValue.natural(site.text.indices.count(place => site.text.slice(place, place + site.pattern.size) == site.pattern))

  /** The contiguous subarrays whose values sum to x. */
  def subarraySums(site: SubarraySums.Site): NativeValue =
    NativeValue.natural((for
      first <- site.values.indices
      last <- first until site.values.size
      if site.values.slice(first, last + 1).sum == site.target
    yield 1).size)

  /** The pairs of places i < j whose values sum to x. */
  def sumOfTwoValues(site: SumOfTwoValues.Site): NativeValue =
    NativeValue.natural((for
      first <- site.values.indices
      second <- first + 1 until site.values.size
      if site.values(first) + site.values(second) == site.target
    yield 1).size)

  /** The greatest, over every node, of the least number of steps from it to
    * the farthest node, each step along an edge.
    */
  def treeDiameter(site: TreeSite.Site): NativeValue =
    def widened(nodes: Set[Int]): Set[Int] =
      nodes ++ site.edges.flatMap((first, second) =>
        (if nodes.contains(first) then Vector(second) else Vector.empty) ++ (if nodes.contains(second) then Vector(first) else Vector.empty)
      )
    val farthest = (1 to site.nodes).map(start => Vector.iterate(Set(start), site.nodes)(widened).indexWhere(_.size == site.nodes))
    NativeValue.natural(farthest.max)

  /** The most edges, over every subset of the edges that no two of which
    * share a node.
    */
  def treeMatching(site: TreeSite.Site): NativeValue =
    val subsets = site.edges.foldLeft(Vector(Vector.empty[(Int, Int)]))((found, edge) => found ++ found.map(_ :+ edge))
    val matchings = subsets.filter(subset => subset.flatMap((first, second) => Vector(first, second)).distinct.size == 2 * subset.size)
    NativeValue.natural(matchings.map(_.size).max)

class ExponentiationTwoReferenceTest
    extends CsesFamilySuite(
      ExponentiationTwo(Spelling.Direct, ExponentiationTwo.rungs.head),
      ExponentiationTwo(Spelling.Respelled, ExponentiationTwo.rungs.head),
      CsesFourthBatchDefinitions.exponentiationTwo,
      "cses_exponentiation_two"
    )

class FerrisWheelReferenceTest
    extends CsesFamilySuite(
      FerrisWheel(Spelling.Direct, FerrisWheel.rungs.head),
      FerrisWheel(Spelling.Respelled, FerrisWheel.rungs.head),
      CsesFourthBatchDefinitions.ferrisWheel,
      "cses_ferris_wheel"
    )

class MissingNumberReferenceTest
    extends CsesFamilySuite(
      MissingNumber(Spelling.Direct, MissingNumber.rungs.head),
      MissingNumber(Spelling.Respelled, MissingNumber.rungs.head),
      CsesFourthBatchDefinitions.missingNumber,
      "cses_missing_number"
    )

class RepetitionsReferenceTest
    extends CsesFamilySuite(
      Repetitions(Spelling.Direct, Repetitions.rungs.head),
      Repetitions(Spelling.Respelled, Repetitions.rungs.head),
      CsesFourthBatchDefinitions.repetitions,
      "cses_repetitions"
    )

class StaticRangeMinimumsReferenceTest
    extends CsesFamilySuite(
      StaticRangeMinimums(Spelling.Direct, StaticRangeMinimums.rungs.head),
      StaticRangeMinimums(Spelling.Respelled, StaticRangeMinimums.rungs.head),
      CsesFourthBatchDefinitions.staticRangeMinimums,
      "cses_static_range_minimums"
    )

class StringMatchingReferenceTest
    extends CsesFamilySuite(
      StringMatching(Spelling.Direct, StringMatching.rungs.head),
      StringMatching(Spelling.Respelled, StringMatching.rungs.head),
      CsesFourthBatchDefinitions.stringMatching,
      "cses_string_matching"
    )

class SubarraySumsReferenceTest
    extends CsesFamilySuite(
      SubarraySums(Spelling.Direct, SubarraySums.rungs.head),
      SubarraySums(Spelling.Respelled, SubarraySums.rungs.head),
      CsesFourthBatchDefinitions.subarraySums,
      "cses_subarray_sums"
    )

class SumOfTwoValuesReferenceTest
    extends CsesFamilySuite(
      SumOfTwoValues(Spelling.Direct, SumOfTwoValues.rungs.head),
      SumOfTwoValues(Spelling.Respelled, SumOfTwoValues.rungs.head),
      CsesFourthBatchDefinitions.sumOfTwoValues,
      "cses_sum_of_two_values"
    )

class TreeDiameterReferenceTest
    extends CsesFamilySuite(
      TreeDiameter(Spelling.Direct, TreeDiameter.rungs.head),
      TreeDiameter(Spelling.Respelled, TreeDiameter.rungs.head),
      CsesFourthBatchDefinitions.treeDiameter,
      "cses_tree_diameter"
    )

class TreeMatchingReferenceTest
    extends CsesFamilySuite(
      TreeMatching(Spelling.Direct, TreeMatching.rungs.head),
      TreeMatching(Spelling.Respelled, TreeMatching.rungs.head),
      CsesFourthBatchDefinitions.treeMatching,
      "cses_tree_matching"
    )
