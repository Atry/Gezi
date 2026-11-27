package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** Depth-first search on a ladder by the attractor, the port of
  * `problems/set_free_search`: reachable and unreachable targets
  * in both spellings, and a near miss that tests the goal at leaves only.
  */
object SetFreeSearch:

  private val family = "set_free_search"

  /** The search of a point, the constructors of
    * problems/set_free_search/search in order: the attractor's depth-first
    * search, and the near miss that tests the goal at leaves only.
    */
  enum Search:
    case DepthFirst, LeavesOnly

  /** The search a field writes, a constructor of
    * problems/set_free_search/search read by its position
    * (`ProblemData.alternative`).
    */
  def search(field: ProblemField): Search =
    ProblemData.alternative(field, Search.values.size) match
      case (position, Vector()) => Search.fromOrdinal(position)
      case (_, fields)          => throw IllegalArgumentException(s"the search of $family has ${fields.size} fields")

  /** A point: its search, spelling, height and target (`ladder_point/5`). */
  final case class LadderPoint(point: String, search: Search, spelling: Spelling, height: Int, target: Int)

  /** The points: the facts read, then each size with each twin
    * (`ladder_size/2`; the twins of `ladder_twin/5`, whose target is computed:
    * one above the height for the unreachable twins, 3 for the near miss).
    */
  def points(group: ReductionGroup): Vector[LadderPoint] =
    val stated = group.problems(family).rows("ladder_point").map {
      case Vector(point, search, spelling, height, target) =>
        LadderPoint(
          ProblemData.text(point),
          this.search(search),
          SetFree.spelling(spelling),
          ProblemData.small(height),
          ProblemData.small(target)
        )
      case other => throw IllegalArgumentException(s"not a ladder point: $other")
    }
    val sized = for
      size <- group.problems(family).rows("ladder_size")
      (twin, search, spelling, target) <- Vector[(String, Search, Spelling, Int => Int)](
        ("unreachable_direct", Search.DepthFirst, Spelling.Direct, _ + 1),
        ("unreachable_respelled", Search.DepthFirst, Spelling.Respelled, _ + 1),
        ("near_miss", Search.LeavesOnly, Spelling.Direct, _ => 3)
      )
    yield
      val height = ProblemData.small(size(1))
      LadderPoint(s"set_free_ladder_${ProblemData.text(size(0))}_$twin", search, spelling, height, target(height))
    stated ++ sized

  /** `Search Successors Goal Stack` (`ladder_point_surface/2`). */
  def pointSurface(attractors: Attractors, point: LadderPoint): ProblemTerm =
    val search = point.search match
      case Search.DepthFirst => attractors.functionSurface("depth_first", point.spelling)
      case Search.LeavesOnly =>
        attractors.fixpoint(leavesOnlyTemplate(attractors)(attractors.functionSurface("append", Spelling.Direct)))
    search(successors(attractors, point.spelling, point.height))(goal(attractors, point.spelling, point.target))(
      stack(attractors, point.spelling)
    )

  /** `cons 0 nil` in the spelling. */
  def stack(attractors: Attractors, spelling: Spelling): ProblemTerm =
    attractors.functionSurface("cons", spelling)(unary(0))(attractors.functionSurface("nil", spelling))

  /** The body of the leaves-only search, with append as its leading
    * parameter (`leaves_only_template/1`).
    */
  def leavesOnlyTemplate(attractors: Attractors): ProblemTerm =
    val falseValue = attractors.attractorSurface("false", Spelling.Direct)
    val trueValue = attractors.attractorSurface("true", Spelling.Direct)
    λ(append =>
      λ(self =>
        λ(successors =>
          λ(goal =>
            λ(stack =>
              stack(falseValue)(λ(node =>
                λ(rest =>
                  val pushed = self(successors)(goal)(append(successors(node))(rest))
                  successors(node)(goal(node)(trueValue)(self(successors)(goal)(rest)))(λ(_ => λ(_ => pushed)))
                )
              ))
            )
          )
        )
      )
    )

  /** `\k. k = n then nil else cons (k + 1) (cons (k + 1) nil)`
    * (`successors/3`).
    */
  def successors(attractors: Attractors, spelling: Spelling, height: Int): ProblemTerm =
    def function(name: String) = attractors.functionSurface(name, spelling)
    val equal = function("natural_equal")
    val limit = unary(height)
    val nilOne = function("nil")
    val nilTwo = function("nil")
    val consOne = function("cons")
    val consTwo = function("cons")
    val successorOne = function("successor")
    val successorTwo = function("successor")
    λ(node => equal(node)(limit)(nilOne)(consOne(successorOne(node))(consTwo(successorTwo(node))(nilTwo))))

  /** `\k. k = target` (`goal/3`). */
  def goal(attractors: Attractors, spelling: Spelling, target: Int): ProblemTerm =
    val equal = attractors.functionSurface("natural_equal", spelling)
    λ(node => equal(node)(unary(target)))

  /** The problems: depth first reaches every target up to the height; the
    * leaves-only search only the height (`reference/4`).
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      val verdict = point.search match
        case Search.DepthFirst => point.target <= point.height
        case Search.LeavesOnly => point.target == point.height
      ReductionProblem(
        point.point,
        pointSurface(group.attractors, point),
        "boolean",
        Expected.One(Scott.booleanTree(verdict)),
        Reduction.defaultLimits
      )
    )
