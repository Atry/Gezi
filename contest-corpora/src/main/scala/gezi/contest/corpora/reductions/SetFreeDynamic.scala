package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The longest common subsequence by a recursion over the attractors, the port
  * of `problems/set_free_dynamic`: direct and respelled twins and a near miss
  * whose match does not count.
  */
object SetFreeDynamic:

  private val family = "set_free_dynamic"

  /** The recursion of a point, the constructors of
    * problems/set_free_dynamic/recursion in order: the longest common
    * subsequence, whose match adds one to the recursion over both tails, and
    * the near miss, whose match does not count.
    */
  enum Recursion:
    case LongestCommonSubsequence, Near

  /** The recursion a field writes, a constructor of
    * problems/set_free_dynamic/recursion read by its position
    * (`ProblemData.alternative`).
    */
  def recursion(field: ProblemField): Recursion =
    ProblemData.alternative(field, Recursion.values.size) match
      case (position, Vector()) => Recursion.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(
          s"the recursion of $family has ${fields.size} fields"
        )

  /** A point: its recursion, spelling and bit strings. */
  final case class CommonSubsequencePoint(
      point: String,
      recursion: Recursion,
      spelling: Spelling,
      left: Vector[Int],
      right: Vector[Int]
  )

  /** The points: the facts read, then each size with each twin, the strings
    * `bits(Length, 3)` and `bits(Length, 5)`.
    */
  def points(group: ReductionGroup): Vector[CommonSubsequencePoint] =
    val stated = group.problems(family).rows("common_subsequence_point").map {
      case Vector(point, recursion, spelling, left, right) =>
        CommonSubsequencePoint(
          ProblemData.text(point),
          this.recursion(recursion),
          SetFree.spelling(spelling),
          ProblemData.smalls(left),
          ProblemData.smalls(right)
        )
      case other => throw IllegalArgumentException(s"not a point: $other")
    }
    val sized = for
      size <- group.problems(family).rows("common_subsequence_size")
      twin <- group.problems(family).rows("common_subsequence_twin")
    yield
      val length = ProblemData.small(size(1))
      CommonSubsequencePoint(
        s"set_free_common_subsequence_${ProblemData.text(size(0))}_${ProblemData.text(twin(0))}",
        recursion(twin(1)),
        SetFree.spelling(twin(2)),
        SetFree.randomBits(3, length, 16),
        SetFree.randomBits(5, length, 16)
      )
    stated ++ sized

  /** `(Y (Template equal at_least successor)) LeftList RightList`
    * (`common_subsequence_point_surface/2`).
    */
  def pointSurface(
      attractors: Attractors,
      point: CommonSubsequencePoint
  ): ProblemTerm =
    attractors.fixpoint(
      recursionTemplate(attractors, point.recursion, point.spelling)(
        attractors.functionSurface("merge_symbols_equal", point.spelling)
      )(attractors.functionSurface("natural_at_least", point.spelling))(
        attractors.functionSurface("successor", point.spelling)
      )
    )(SetFree.booleanList(attractors, point.left))(
      SetFree.booleanList(attractors, point.right)
    )

  /** The recursion's body over the attractors it calls,
    * `\equal. \at_least. \successor. \self. \xs. \ys. ...`
    * (`recursion_template/3`).
    */
  private def recursionTemplate(
      attractors: Attractors,
      recursion: Recursion,
      spelling: Spelling
  ): ProblemTerm =
    val zeroOne = attractors.attractorSurface("zero", Spelling.Direct)
    val zeroTwo = attractors.attractorSurface("zero", Spelling.Direct)
    Attractors.spelledSurface(
      spelling,
      λ(equal =>
        λ(atLeast =>
          λ(successor =>
            λ(self =>
              λ(xs =>
                λ(ys =>
                  xs(zeroOne)(
                    λ(x =>
                      λ(xTail =>
                        ys(zeroTwo)(
                          λ(y =>
                            λ(yTail =>
                              val matched = recursion match
                                case Recursion.LongestCommonSubsequence =>
                                  successor(self(xTail)(yTail))
                                case Recursion.Near => self(xTail)(yTail)
                              val maximum =
                                atLeast(self(xTail)(ys))(self(xs)(yTail))(
                                  self(xTail)(ys)
                                )(self(xs)(yTail))
                              equal(x)(y)(matched)(maximum)
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The dynamic programme over the prefixes, row by row
    * (`longest_common_subsequence/3`).
    */
  def longestCommonSubsequence(left: Vector[Int], right: Vector[Int]): Int =
    DynamicReferences.referenceLongestCommonSubsequence(left, right)

  /** The problems: the length of the longest common subsequence, or 0 for the
    * near miss (`reference/4`).
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      val length = point.recursion match
        case Recursion.LongestCommonSubsequence =>
          longestCommonSubsequence(point.left, point.right)
        case Recursion.Near => 0
      ReductionProblem(
        point.point,
        pointSurface(group.attractors, point),
        "unary",
        Expected.One(Scott.unaryTree(length)),
        Reduction.defaultLimits
      )
    )
