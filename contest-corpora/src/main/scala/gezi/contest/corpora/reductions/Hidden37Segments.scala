package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** The numbers of words a string is cut into within a budget, the port of `problems/hidden_37_segments`.
  */
object Hidden37Segments:

  private val family = "hidden_37_segments"

  /** `(\starts. \choose. \drop. \words. Cut (concat Chunks) Budget (\r. difference Budget r))
    * Starts Choose Drop Words` (`segments_term/5`).
    */
  def segmentsTerm(attractors: Attractors, chunks: Vector[Vector[Int]], words: Vector[Vector[Int]], budget: Int): Term =
    val concat = attractors.functionSurface("concat", Spelling.Direct)
    val difference = attractors.functionSurface("natural_difference", Spelling.Direct)
    λ(starts =>
      λ(choose =>
        λ(drop =>
          λ(wordsVariable =>
            cutFunction(attractors, starts, choose, drop, wordsVariable)(concat(SetFree.bitLists(attractors, chunks)))(
              unary(budget)
            )(λ(remaining => difference(unary(budget))(remaining)))
          )
        )
      )
    )(startsFunction(attractors))(chooseFunction(attractors))(Hidden37Concatenation.dropFunction(attractors))(
      SetFree.bitLists(attractors, words)
    )

  /** `\s. \w. prefix w s` (`starts_function/1`). */
  private def startsFunction(attractors: Attractors): Term =
    val prefix = attractors.functionSurface("bits_prefix", Spelling.Direct)
    λ(string => λ(word => prefix(word)(string)))

  /** Each word chosen (`choose_function/1`). */
  private def chooseFunction(attractors: Attractors): Term =
    attractors.fixpoint(
      λ(self =>
        λ(words =>
          λ(function => words(top)(λ(word => λ(rest => members(Vector(function(word), self(rest)(function)))))))
        )
      )
    )

  /** The string cut at a word that starts it, each cut costing one unit of
    * the budget (`cut_function/5`).
    */
  private def cutFunction(attractors: Attractors, starts: Term, choose: Term, drop: Term, words: Term): Term =
    val filter = attractors.functionSurface("filter", Spelling.Direct)
    val length = attractors.functionSurface("length", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(string =>
          λ(remaining =>
            λ(continuation =>
              string(continuation(remaining))(λ(_ =>
                λ(_ =>
                  remaining(top)(λ(predecessor =>
                    choose(filter(starts(string))(words))(λ(word => self(drop(length(word))(string))(predecessor)(continuation)))
                  ))
                )
              ))
            )
          )
        )
      )
    )

  /** The sorted numbers of words within the budget the string is cut into,
    * by the table of the suffixes (`segment_counts/4`).
    */
  def segmentCounts(string: Vector[Int], words: Vector[Vector[Int]], budget: Int): Vector[Int] =
    val table = (string.size - 1 to 0 by -1).foldLeft(Map(string.size -> Vector(0)))((table, position) =>
      val rest = string.drop(position)
      val counts = words
        .filter(rest.startsWith(_))
        .flatMap(word => table(position + word.size).map(_ + 1))
        .filter(_ <= budget)
        .distinct
        .sorted
      table.updated(position, counts)
    )
    table(0)

  /** The fewest words, or nothing when the string cannot be cut
    * (`fewest_segments/3`).
    */
  def fewestSegments(string: Vector[Int], words: Vector[Vector[Int]]): Option[Int] =
    segmentCounts(string, words, string.size).headOption

  private def next(state: Long): Long = DynamicReferences.nextRandom(state)

  private def lexicographicallyBefore(left: Vector[Int], right: Vector[Int]): Boolean =
    left.zip(right).find(_ != _).map(_ < _).getOrElse(left.size < right.size)

  /** `[1]` and nine random words of 2 to 5 bits holding a one, sorted
    * without repetition (`point_words/2`).
    */
  def pointWords(seed: Long): Vector[Vector[Int]] =
    val longer = (1 to 9)
      .foldLeft((Vector.empty[Vector[Int]], seed)) { case ((found, state), _) =>
        val sized = next(state)
        val size = ((sized >> 20) % 4 + 2).toInt
        val bitStates = DynamicReferences.states(sized, size)
        val bits = bitStates.map(bitState => ((bitState >> 20) & 1).toInt)
        (found :+ (if bits.contains(1) then bits else 1 +: bits.tail), bitStates.last)
      }
      ._1
    (Vector(1) +: longer).distinct.sortWith(lexicographicallyBefore)

  /** Words drawn until the string is at least `length` long
    * (`point_string/4`).
    */
  @tailrec
  def pointString(length: Int, words: Vector[Vector[Int]], state: Long, built: Vector[Int]): Vector[Int] =
    if built.size >= length then built
    else
      val following = next(state)
      pointString(length, words, following, built ++ words(((following >> 16) % words.size).toInt))

  /** The string cut into chunks of 1 to 7 bits (`point_chunks/3`). */
  @tailrec
  def pointChunks(string: Vector[Int], state: Long, chunks: Vector[Vector[Int]]): Vector[Vector[Int]] =
    if string.isEmpty then chunks
    else
      val following = next(state)
      val size = math.min(((following >> 18) % 7 + 1).toInt, string.size)
      pointChunks(string.drop(size), following, chunks :+ string.take(size))

  /** The string with the first bit from its middle flipped after which it
    * cannot be cut (`flipped/3`).
    */
  private def flipped(string: Vector[Int], words: Vector[Vector[Int]]): Vector[Int] =
    (string.size / 2 until string.size)
      .map(position => string.updated(position, 1 - string(position)))
      .find(fewestSegments(_, words).isEmpty)
      .getOrElse(throw IllegalArgumentException("no flip makes the string uncuttable"))

  /** The chunks, words, budget and counts of a point (`point_problem/5`). */
  def pointProblem(group: ReductionGroup, point: String): (Vector[Vector[Int]], Vector[Vector[Int]], Int, Vector[Int]) =
    group.problems(family).keyed("segments_point").get(point) match
      case Some(Vector(length, seed, slack, _, flip)) =>
        val seedValue: Long = ProblemData.small(seed)
        val words = pointWords(seedValue)
        val original = pointString(ProblemData.small(length), words, seedValue, Vector.empty)
        val fewest = fewestSegments(original, words).getOrElse(throw IllegalArgumentException(s"$point cannot be cut"))
        // The flip is a Church Boolean of corpora/library/prelude/boolean, true for the flipped string.
        val string = if ProblemData.boolean(flip) then flipped(original, words) else original
        val budget = fewest + ProblemData.small(slack)
        (pointChunks(string, seedValue, Vector.empty), words, budget, segmentCounts(string, words, budget))
      case other => throw IllegalArgumentException(s"no segments point $point: $other")

  /** The problems (`segments_point/6`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("segments_point").map(arguments =>
      val point = ProblemData.text(arguments.head)
      val (chunks, words, budget, counts) = pointProblem(group, point)
      ReductionProblem(
        point,
        segmentsTerm(group.attractors, chunks, words, budget),
        "unary",
        Reduction.expectedOf(counts.map(Scott.unaryTree)),
        Reduction.hiddenLimits
      )
    )
