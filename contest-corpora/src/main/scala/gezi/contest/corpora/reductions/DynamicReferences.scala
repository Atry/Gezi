package gezi.contest.corpora.reductions

import scala.annotation.tailrec

/** The native references of the dynamic programmes, the port of the deleted
  * Prolog file (`git show
  * 6ab16a338^:lambda_jit/corpora/contest_dynamic_references.pl`): the lattice
  * paths, the subset sums and the longest common subsequence, each by its
  * table, and the deterministic inputs of their points.
  */
object DynamicReferences:

  /** The number of monotone lattice paths across a rows by columns grid: each
    * row of the table the prefix sums of the previous one
    * (`reference_grid_paths/3`).
    */
  def referenceGridPaths(rows: Int, columns: Int): BigInt =
    (1 to rows)
      .foldLeft(Vector.fill(columns + 1)(BigInt(1)))((row, _) =>
        row.scanLeft(BigInt(0))(_ + _).tail
      )
      .last

  /** The ordered set of the sums of the subsets of the items, one pass per item
    * (`reference_subset_sums/2`).
    */
  def referenceSubsetSums(items: Vector[Int]): Vector[Int] =
    items.foldLeft(Vector(0))((sums, item) =>
      (sums ++ sums.map(_ + item)).distinct.sorted
    )

  /** The first `count` odd primes from 3 on (`subset_items/2`). */
  def subsetItems(count: Int): Vector[Int] =
    LazyList.iterate(3)(_ + 2).filter(prime).take(count).toVector

  private def prime(number: Int): Boolean =
    number > 1 && (2 to math.sqrt(number.toDouble).floor.toInt)
      .forall(number % _ != 0)

  /** The length of a longest common subsequence, by the usual table, one row
    * per symbol of the left (`reference_lcs/3`).
    */
  def referenceLongestCommonSubsequence[Symbol](
      left: Vector[Symbol],
      right: Vector[Symbol]
  ): Int =
    left
      .foldLeft(Vector.fill(right.size + 1)(0))((above, symbol) =>
        right.indices.foldLeft(Vector(0))((row, column) =>
          row :+ (if right(column) == symbol then above(column) + 1
                  else math.max(above(column + 1), row.last))
        )
      )
      .last

  /** The next state of the linear congruential sequence of the corpora. */
  def nextRandom(state: Long): Long =
    (state * 1103515245L + 12345L) % 2147483648L

  /** A fixed string over {a, b}, the bit 16 of the linear congruential sequence
    * from the seed (`pseudo_string/3`).
    */
  def pseudoString(seed: Long, length: Int): Vector[Char] =
    states(seed, length).map(state =>
      if (state >> 16) % 2 == 0 then 'a' else 'b'
    )

  /** The `count` states of the sequence after the seed. */
  def states(seed: Long, count: Int): Vector[Long] =
    statesFrom(seed, count, Vector.empty)

  @tailrec
  private def statesFrom(
      state: Long,
      count: Int,
      found: Vector[Long]
  ): Vector[Long] =
    if found.size == count then found
    else
      val next = nextRandom(state)
      statesFrom(next, count, found :+ next)

  /** The strings `pseudo_string(1, length)` and `pseudo_string(7, length)` and
    * the length of their longest common subsequence (`lcs_point_strings/4`).
    */
  def lcsPointStrings(length: Int): (Vector[Char], Vector[Char], Int) =
    val left = pseudoString(1, length)
    val right = pseudoString(7, length)
    (left, right, referenceLongestCommonSubsequence(left, right))
