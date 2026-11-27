package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** A Fibonacci loop whose accumulators stay in scope, the port of
  * `problems/set_free_scope`: direct and respelled twins, and a near miss that
  * doubles zero.
  */
object SetFreeScope:

  private val family = "set_free_scope"

  /** A point: its loop, spelling and steps (`scope_point/4`). */
  final case class ScopePoint(
      point: String,
      loop: String,
      spelling: Spelling,
      steps: Int
  )

  /** The points: the facts read, then each size with each twin. */
  def points(group: ReductionGroup): Vector[ScopePoint] =
    val stated = group.problems(family).rows("scope_point").map {
      case Vector(point, loop, spelling, steps) =>
        ScopePoint(
          ProblemData.text(point),
          ProblemData.text(loop),
          SetFree.spelling(spelling),
          ProblemData.small(steps)
        )
      case other => throw IllegalArgumentException(s"not a scope point: $other")
    }
    val sized = for
      size <- group.problems(family).rows("scope_size")
      twin <- group.problems(family).rows("scope_twin")
    yield ScopePoint(
      s"set_free_scope_${ProblemData.text(size(0))}_${ProblemData.text(twin(0))}",
      ProblemData.text(twin(1)),
      SetFree.spelling(twin(2)),
      ProblemData.small(size(1))
    )
    stated ++ sized

  /** The loop over the unary steps (`scope_point_surface/2`, `loop_surface/4`).
    */
  def pointSurface(group: ReductionGroup, point: ScopePoint): ProblemTerm =
    loopApplied(group, point.loop, point.spelling, unary(point.steps))

  /** The loop of the spelling over the steps, a unary numeral. */
  private[reductions] def loopApplied(
      group: ReductionGroup,
      loop: String,
      spelling: Spelling,
      steps: ProblemTerm
  ): ProblemTerm = loop match
    case "fibonacci" =>
      val template = Attractors.spelledSurface(
        spelling,
        λ(plus =>
          λ(self =>
            λ(count =>
              λ(first =>
                λ(second =>
                  count(first)(
                    λ(predecessor =>
                      self(predecessor)(second)(plus(first)(second))
                    )
                  )
                )
              )
            )
          )
        )
      )
      group.attractors.fixpoint(
        template(SetFree.libraryFunction(group, "merge_binary_plus", spelling))
      )(steps)(
        binary(0)
      )(binary(1))
    case "doubling" =>
      val even =
        group.attractors.attractorSurface("binary_even", Spelling.Direct)
      group.attractors.fixpoint(
        λ(self =>
          λ(count =>
            λ(start =>
              count(start)(λ(predecessor => self(predecessor)(even(start))))
            )
          )
        )
      )(steps)(binary(0))
    case other => throw IllegalArgumentException(s"no loop $other")

  /** The tree the point expects: fib of the steps, or that many evens over zero
    * (`reference_tree/3`).
    */
  def referenceTree(group: ReductionGroup, point: ScopePoint): ScottTree =
    point.loop match
      case "fibonacci" =>
        Scott.binaryTree(group.fibonacci.referenceFibonacci(point.steps))
      case "doubling" =>
        (1 to point.steps).foldLeft(Scott.leaf("zero"))((tree, _) =>
          ScottTree("even", Vector(tree))
        )
      case other => throw IllegalArgumentException(s"no loop $other")

  /** The problems. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      ReductionProblem(
        point.point,
        pointSurface(group, point),
        "binary",
        Expected.One(referenceTree(group, point)),
        Reduction.defaultLimits
      )
    )
