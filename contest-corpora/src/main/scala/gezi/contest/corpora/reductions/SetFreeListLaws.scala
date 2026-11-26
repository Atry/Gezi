package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The length of a mapped list by the attractors, the port of
  * `problems/set_free_list_laws`: `length (map id xs) = length xs`
  * on a list doubled k times, and a near miss that filters everything out.
  */
object SetFreeListLaws:

  private val family = "set_free_list_laws"

  /** A point: its transformer, spelling and doublings (`list_law_point/4`). */
  final case class ListLawPoint(point: String, transformer: String, spelling: Spelling, doublings: Int)

  /** The points: the facts read, then each size with each twin. */
  def points(group: ReductionGroup): Vector[ListLawPoint] =
    val stated = group.problems(family).rows("list_law_point").map {
      case Vector(point, transformer, spelling, doublings) =>
        ListLawPoint(ProblemData.text(point), ProblemData.text(transformer), SetFree.spelling(spelling), ProblemData.small(doublings))
      case other => throw IllegalArgumentException(s"not a list law point: $other")
    }
    val sized = for
      size <- group.problems(family).rows("list_law_size")
      twin <- group.problems(family).rows("list_law_twin")
    yield ListLawPoint(
      s"set_free_list_law_${ProblemData.text(size(0))}_${ProblemData.text(twin(0))}",
      ProblemData.text(twin(1)),
      SetFree.spelling(twin(2)),
      ProblemData.small(size(1))
    )
    stated ++ sized

  /** `equal (length (transformer argument list)) (length list)`
    * (`list_law_point_surface/2`).
    */
  def pointSurface(attractors: Attractors, point: ListLawPoint): ProblemTerm =
    lawApplied(attractors, point.transformer, point.spelling, unary(point.doublings))

  /** The law's two lengths compared on the list doubled the given number of
    * times, a unary numeral.
    */
  private[reductions] def lawApplied(attractors: Attractors, transformerName: String, spelling: Spelling, doublings: ProblemTerm): ProblemTerm =
    def function(name: String) = attractors.functionSurface(name, spelling)
    val equal = function("natural_equal")
    val lengthOne = function("length")
    val lengthTwo = function("length")
    val transformer = function(transformerName)
    val argument = transformerName match
      case "map"    => λ(element => element)
      case "filter" =>
        val falseValue = attractors.attractorSurface("false", Spelling.Direct)
        λ(_ => falseValue)
      case other => throw IllegalArgumentException(s"no transformer $other")
    equal(lengthOne(transformer(argument)(doubledList(attractors, spelling, doublings))))(
      lengthTwo(doubledList(attractors, spelling, doublings))
    )

  /** `repeat k dbl [i]` (`doubled_list/3`), k a unary numeral. */
  private def doubledList(attractors: Attractors, spelling: Spelling, doublings: ProblemTerm): ProblemTerm =
    val repeat = attractors.fixpoint(
      Attractors.spelledSurface(
        spelling,
        λ(self => λ(count => λ(function => λ(start => count(start)(λ(predecessor => function(self(predecessor)(function)(start))))))))
      )
    )
    val append = attractors.functionSurface("append", spelling)
    val doubling = λ(list => append(list)(list))
    repeat(doublings)(doubling)(
      attractors.functionSurface("cons", spelling)(λ(element => element))(attractors.functionSurface("nil", spelling))
    )

  /** The problems: map keeps the length, filter does not (`reference/2`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      val verdict = point.transformer match
        case "map"    => true
        case "filter" => false
        case other    => throw IllegalArgumentException(s"no transformer $other")
      ReductionProblem(
        point.point,
        pointSurface(group.attractors, point),
        "boolean",
        Expected.One(Scott.booleanTree(verdict)),
        Reduction.defaultLimits
      )
    )
