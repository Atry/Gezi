package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** Depth-first search that answers a term on exhaustion, the port of
  * `problems/set_free_empty_search`: the empty stack answers E,
  * `E = Y (\e. \x. x e)`, so an unreachable target has no consistent normal
  * form.
  */
object SetFreeEmptySearch:

  private val family = "set_free_empty_search"

  /** A point: its spelling, height and target (`empty_search_point/4`). */
  final case class EmptySearchPoint(point: String, spelling: Spelling, height: Int, target: Int)

  /** The points: the facts read, then each size with each twin, unreachable,
    * the target one above the height.
    */
  def points(group: ReductionGroup): Vector[EmptySearchPoint] =
    val stated = group.problems(family).rows("empty_search_point").map {
      case Vector(point, spelling, height, target) =>
        EmptySearchPoint(ProblemData.text(point), SetFree.spelling(spelling), ProblemData.small(height), ProblemData.small(target))
      case other => throw IllegalArgumentException(s"not an empty search point: $other")
    }
    val sized = for
      size <- group.problems(family).rows("empty_search_size")
      twin <- group.problems(family).rows("empty_search_twin")
    yield
      val height = ProblemData.small(size(1))
      EmptySearchPoint(
        s"set_free_empty_search_${ProblemData.text(size(0))}_unreachable_${ProblemData.text(twin(0))}",
        SetFree.spelling(twin(1)),
        height,
        height + 1
      )
    stated ++ sized

  /** The depth-first recursion with its leading parameters E and append
    * (`empty_on_exhaustion_template/1`).
    */
  def emptyOnExhaustionTemplate(attractors: Attractors): ProblemTerm =
    val trueValue = attractors.attractorSurface("true", Spelling.Direct)
    λ(empty =>
      λ(append =>
        λ(self =>
          λ(successors =>
            λ(goal =>
              λ(stack =>
                stack(empty)(λ(node =>
                  λ(rest => goal(node)(trueValue)(self(successors)(goal)(append(successors(node))(rest))))
                ))
              )
            )
          )
        )
      )
    )

  /** `E = Y (\e. \x. x e)` (`empty_term/1`). */
  def emptyTerm(attractors: Attractors): ProblemTerm =
    attractors.fixpoint(λ(self => λ(argument => argument(self))))

  /** `(Y (Template E append)) Successors Goal Stack`
    * (`empty_search_point_surface/2`).
    */
  def pointSurface(attractors: Attractors, point: EmptySearchPoint): ProblemTerm =
    attractors.fixpoint(
      Attractors.spelledSurface(point.spelling, emptyOnExhaustionTemplate(attractors))(emptyTerm(attractors))(
        attractors.functionSurface("append", point.spelling)
      )
    )(SetFreeSearch.successors(attractors, point.spelling, point.height))(
      SetFreeSearch.goal(attractors, point.spelling, point.target)
    )(SetFreeSearch.stack(attractors, point.spelling))

  /** The problems: true when the target is reachable, no tree otherwise. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      ReductionProblem(
        point.point,
        pointSurface(group.attractors, point),
        "boolean",
        if point.target <= point.height then Expected.One(Scott.leaf("true")) else Expected.Trees(Vector.empty),
        Reduction.defaultLimits
      )
    )
