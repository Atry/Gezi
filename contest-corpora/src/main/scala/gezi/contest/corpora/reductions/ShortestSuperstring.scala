package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The lengths of the superstrings of some words within a budget, the port
  * of `problems/shortest_superstring`.
  */
object ShortestSuperstring:

  private val family = "shortest_superstring"

  /** The program under the lets of the words (`superstring_term/3`). */
  def superstringTerm(attractors: Attractors, words: Vector[Vector[Int]], budget: Int): Term =
    lets(
      words.map(SetFree.booleanList(attractors, _)),
      wordVariables =>
        val overlapsFunction = overlapsTerm(attractors)
        val none = CollectKeys.noneCollected(attractors, words.size)
        val nil = attractors.attractorSurface("nil", Spelling.Direct)
        val difference = attractors.functionSurface("natural_difference", Spelling.Direct)
        λ(overlaps =>
          tourFunction(attractors, wordVariables, overlaps)(none)(nil)(unary(budget))(λ(remaining =>
            difference(unary(budget))(remaining)
          ))
        )(overlapsFunction)
    )

  /** The set of the overlaps of left's suffixes with right's prefixes,
    * answered as lengths (`overlaps_term/1`).
    */
  private def overlapsTerm(attractors: Attractors): Term =
    val prefix = attractors.functionSurface("bits_prefix", Spelling.Direct)
    val length = attractors.functionSurface("length", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            members(
              Vector(
                prefix(left)(right)(λ(continuation => continuation(length(left))))(top),
                left(top)(λ(_ => λ(rest => self(rest)(right))))
              )
            )
          )
        )
      )
    )

  /** `Y (\self. \used. \previous. \r. \k. full used (k r) {branches})`
    * (`tour_function/3`).
    */
  private def tourFunction(attractors: Attractors, words: Vector[Term], overlaps: Term): Term =
    def function(name: String) = attractors.functionSurface(name, Spelling.Direct)
    val full = function("bit_set_full")
    attractors.fixpoint(
      λ(self =>
        λ(used =>
          λ(previous =>
            λ(remaining =>
              λ(continuation =>
                full(used)(continuation(remaining))(members(words.zipWithIndex.map((word, position) =>
                  val member = function("bit_set_member")
                  val insert = function("bit_set_insert")
                  val atLeast = function("natural_at_least")
                  val differenceOne = function("natural_difference")
                  val differenceTwo = function("natural_difference")
                  val length = function("length")
                  member(used)(unary(position))(top)(overlaps(previous)(word)(λ(overlap =>
                    λ(cost =>
                      atLeast(remaining)(cost)(self(insert(used)(unary(position)))(word)(differenceTwo(remaining)(cost))(
                        continuation
                      ))(top)
                    )(differenceOne(length(word))(overlap))
                  )))
                )))
              )
            )
          )
        )
      )
    )

  /** The lengths of the overlaps of left's suffixes with right's prefixes,
    * every one (`overlap/3`).
    */
  def overlaps(left: Vector[Int], right: Vector[Int]): Vector[Int] =
    (0 to left.size).toVector.map(start => left.drop(start)).filter(right.startsWith(_)).map(_.size)

  /** The sorted lengths within the budget of the superstrings that place
    * the words in some order, each overlap any one (`superstring_totals/3`).
    */
  def superstringTotals(words: Vector[Vector[Int]], budget: Int): Vector[Int] =
    words.permutations.toVector.flatMap(order => orderLengths(order, Vector.empty, budget, 0)).distinct.sorted

  private def orderLengths(order: Vector[Vector[Int]], previous: Vector[Int], budget: Int, accumulated: Int): Vector[Int] =
    if order.isEmpty then Vector(accumulated)
    else
      overlaps(previous, order.head)
        .map(overlap => accumulated + order.head.size - overlap)
        .filter(_ <= budget)
        .flatMap(next => orderLengths(order.tail, order.head, budget, next))

  /** The least length over every order, each overlap the longest
    * (`shortest_superstring/2`).
    */
  def shortestSuperstring(words: Vector[Vector[Int]]): Int =
    words.permutations.toVector
      .map(order =>
        order
          .foldLeft((Vector.empty[Int], 0)) { case ((previous, total), word) =>
            (word, total + word.size - overlaps(previous, word).max)
          }
          ._2
      )
      .min

  /** `count` words of `length` bits, the bits of one linear congruential
    * sequence from 7 (`point_words/3`).
    */
  def pointWords(count: Int, length: Int): Vector[Vector[Int]] =
    SetFree.randomBits(7, count * length, 16).grouped(length).toVector

  /** The problems (`superstring_point/4`), the budget the shortest length
    * plus the slack.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("superstring_point").map {
      case Vector(point, count, length, slack) =>
        val words = pointWords(ProblemData.small(count), ProblemData.small(length))
        val budget = shortestSuperstring(words) + ProblemData.small(slack)
        ReductionProblem(
          ProblemData.text(point),
          superstringTerm(group.attractors, words, budget),
          "unary",
          Reduction.expectedOf(superstringTotals(words, budget).map(Scott.unaryTree)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a superstring point: $other")
    }
