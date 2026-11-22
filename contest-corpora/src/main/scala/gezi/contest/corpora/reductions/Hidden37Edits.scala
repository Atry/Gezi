package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The edit distance within a budget, the port
  * of `problems/hidden_37_edits`.
  */
object Hidden37Edits:

  private val family = "hidden_37_edits"

  /** `(\same. \size. Ed Source Target Budget (\r. difference Budget r)) Same Size`
    * (`edits_term/4`).
    */
  def editsTerm(attractors: Attractors, source: Vector[Int], target: Vector[Int], budget: Int): Term =
    val equal = attractors.functionSurface("merge_symbols_equal", Spelling.Direct)
    val length = attractors.functionSurface("length", Spelling.Direct)
    val difference = attractors.functionSurface("natural_difference", Spelling.Direct)
    λ(same =>
      λ(size =>
        edFunction(attractors, same, size)(SetFree.booleanList(attractors, source))(SetFree.booleanList(attractors, target))(
          unary(budget)
        )(λ(remaining => difference(unary(budget))(remaining)))
      )
    )(λ(left => λ(right => equal(left)(right))))(λ(list => length(list)))

  /** The search over the scripts of edits (`ed_function/3`). */
  private def edFunction(attractors: Attractors, same: Term, size: Term): Term =
    attractors.fixpoint(
      λ(self =>
        λ(source =>
          λ(target =>
            λ(remaining =>
              λ(continuation =>
                source(fits(attractors, remaining, size(target), continuation))(λ(sourceHead =>
                  λ(sourceTail =>
                    target(fits(attractors, remaining, size(source), continuation))(λ(targetHead =>
                      λ(targetTail =>
                        members(
                          Vector(
                            same(sourceHead)(targetHead)(self(sourceTail)(targetTail)(remaining)(continuation))(top),
                            remaining(top)(λ(predecessor =>
                              members(
                                Vector(
                                  self(sourceTail)(targetTail)(predecessor)(continuation),
                                  self(sourceTail)(target)(predecessor)(continuation),
                                  self(source)(targetTail)(predecessor)(continuation)
                                )
                              )
                            ))
                          )
                        )
                      )
                    ))
                  )
                ))
              )
            )
          )
        )
      )
    )

  /** `at_least budget cost (k (difference budget cost)) []` (`fits/4`). */
  private def fits(attractors: Attractors, budget: Term, cost: Term, continuation: Term): Term =
    val atLeast = attractors.functionSurface("natural_at_least", Spelling.Direct)
    val difference = attractors.functionSurface("natural_difference", Spelling.Direct)
    atLeast(budget)(cost)(continuation(difference(budget)(cost)))(top)

  /** The edit distance by its table (`edit_distance/3`). */
  def editDistance(source: Vector[Int], target: Vector[Int]): Int =
    source
      .foldLeft((0 to target.size).toVector)((above, bit) =>
        target.indices.foldLeft(Vector(above(0) + 1))((row, column) =>
          val substitute = if target(column) == bit then above(column) else above(column) + 1
          row :+ math.min(substitute, math.min(above(column + 1) + 1, row.last + 1))
        )
      )
      .last

  private def next(state: Long): Long = DynamicReferences.nextRandom(state)

  /** The source of random bits and the target after random edits
    * (`point_strings/3`).
    */
  def pointStrings(length: Int, edits: Int, seed: Long): (Vector[Int], Vector[Int]) =
    val states = DynamicReferences.states(seed, length)
    val source = states.map(state => ((state >> 20) & 1).toInt)
    val target = (1 to edits)
      .foldLeft((source, states.lastOption.getOrElse(seed))) { case ((string, state), _) =>
        val stateOne = next(state)
        val stateTwo = next(stateOne)
        val kind = ((stateOne >> 20) % 3).toInt
        val position = ((stateTwo >> 12) % math.max(string.size, 1)).toInt
        val edited = kind match
          case 0 => string.updated(position, 1 - string(position))
          case 1 => string.patch(position, Vector.empty, 1)
          case _ => string.patch(position, Vector(((stateTwo >> 24) & 1).toInt), 0)
        (edited, stateTwo)
      }
      ._1
    (source, target)

  /** The problems (`edits_point/5`): the distance at slack 0, no tree when
    * the budget is short.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("edits_point").map {
      case Vector(point, length, edits, seed, slack) =>
        val (source, target) = pointStrings(ProblemData.small(length), ProblemData.small(edits), ProblemData.small(seed))
        val distance = editDistance(source, target)
        val slackValue = ProblemData.small(slack)
        val expected =
          if slackValue == 0 then Expected.One(Scott.unaryTree(distance))
          else if slackValue < 0 then Expected.Trees(Vector.empty)
          else throw IllegalArgumentException(s"the Prolog expects nothing for a positive slack: $point")
        ReductionProblem(
          ProblemData.text(point),
          editsTerm(group.attractors, source, target, distance + slackValue),
          "unary",
          expected,
          Reduction.hiddenLimits
        )
      case other => throw IllegalArgumentException(s"not an edits point: $other")
    }
