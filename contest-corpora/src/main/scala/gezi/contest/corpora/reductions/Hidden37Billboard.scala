package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The tallest billboard, the port of
  * `problems/hidden_37_billboard`: each rod left out or welded to
  * the left or the right support, the answers the heights of the equal
  * supports.
  */
object Hidden37Billboard:

  private val family = "hidden_37_billboard"

  /** `Go Rods 0 0` (`billboard_term/2`). */
  def billboardTerm(attractors: Attractors, rods: Vector[Int]): ProblemTerm =
    goFunction(attractors)(SetFree.scottList(attractors, rods.map(rod => binary(rod))))(binary(0))(binary(0))

  /** The search over the rods (`go_function/1`). */
  private def goFunction(attractors: Attractors): ProblemTerm =
    val equal = attractors.functionSurface("merge_binary_equality", Spelling.Direct)
    val plusOne = attractors.functionSurface("merge_binary_plus", Spelling.Direct)
    val plusTwo = attractors.functionSurface("merge_binary_plus", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(rods =>
          λ(left =>
            λ(right =>
              rods(equal(left)(right)(left)(top))(λ(rod =>
                λ(rest =>
                  members(
                    Vector(
                      self(rest)(left)(right),
                      self(rest)(plusOne(rod)(left))(right),
                      self(rest)(left)(plusTwo(rod)(right))
                    )
                  )
                )
              ))
            )
          )
        )
      )
    )

  /** The sorted heights of the equal supports, by the set of the pairs of
    * support heights after each rod (`billboard_heights/2`).
    */
  def billboardHeights(rods: Vector[Int]): Vector[Int] =
    rods
      .foldLeft(Vector((0, 0)))((pairs, rod) =>
        pairs.flatMap((left, right) => Vector((left, right), (left + rod, right), (left, right + rod))).distinct
      )
      .collect { case (left, right) if left == right => left }
      .distinct
      .sorted

  /** The rods of a point (`point_rods/2`): random for a subtask, the powers
    * of two, or the nine rods with one lengthened so that their tallest
    * height is lost.
    */
  def pointRods(group: ReductionGroup, point: String): Vector[Int] =
    point match
      case "hidden_37_billboard_trap_powers" => (0 to 6).toVector.map(1 << _)
      case "hidden_37_billboard_trap_near_miss" =>
        val original = pointRods(group, "hidden_37_billboard_nine")
        val tallest = billboardHeights(original).max
        original.indices
          .map(position => original.updated(position, original(position) + 1))
          .find(near => !billboardHeights(near).contains(tallest))
          .getOrElse(throw IllegalArgumentException("no lengthened rod loses the tallest height"))
      case _ =>
        group.problems(family).keyed("billboard_point").get(point) match
          case Some(Vector(count, seed, kind)) if ProblemData.text(kind) == "subtask" =>
            DynamicReferences.states(ProblemData.small(seed), ProblemData.small(count)).map(state => ((state >> 16) % 20 + 1).toInt)
          case other => throw IllegalArgumentException(s"no rods of $point: $other")

  /** The problems (`billboard_point/4`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("billboard_point").map(arguments =>
      val point = ProblemData.text(arguments.head)
      val rods = pointRods(group, point)
      ReductionProblem(
        point,
        billboardTerm(group.attractors, rods),
        "binary",
        Reduction.expectedOf(billboardHeights(rods).map(height => Scott.binaryTree(height))),
        Reduction.hiddenLimits
      )
    )
