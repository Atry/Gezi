package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The sizes of the teams that cover every skill within a budget, the port of
  * `problems/smallest_team`.
  */
object SmallestTeam:

  private val family = "smallest_team"

  /** `Team People None Budget (\r. difference Budget r)` (`team_term/4`). */
  def teamTerm(
      attractors: Attractors,
      skillCount: Int,
      people: Vector[Vector[Int]],
      budget: Int
  ): ProblemTerm =
    val difference =
      attractors.functionSurface("natural_difference", Spelling.Direct)
    teamFunction(attractors)(peopleSurface(attractors, people, skillCount))(
      CollectKeys.noneCollected(attractors, skillCount)
    )(unary(budget))(λ(remaining => difference(unary(budget))(remaining)))

  /** Each person left out or taken at the cost of one unit of the budget, the
    * skills covered by union (`team_function/1`).
    */
  private def teamFunction(attractors: Attractors): ProblemTerm =
    val full = attractors.functionSurface("bit_set_full", Spelling.Direct)
    val union = attractors.functionSurface("bit_set_union", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(people =>
          λ(covered =>
            λ(remaining =>
              λ(continuation =>
                people(full(covered)(continuation(remaining))(top))(
                  λ(skills =>
                    λ(rest =>
                      members(
                        Vector(
                          self(rest)(covered)(remaining)(continuation),
                          remaining(top)(
                            λ(predecessor =>
                              self(rest)(union(covered)(skills))(predecessor)(
                                continuation
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
    )

  /** The Scott list of the people's skill sets (`people_surface/3`). */
  private def peopleSurface(
      attractors: Attractors,
      people: Vector[Vector[Int]],
      skillCount: Int
  ): ProblemTerm =
    SetFree.scottList(
      attractors,
      people.map(skills =>
        SetFree.booleanList(
          attractors,
          (0 until skillCount).toVector.map(skill =>
            if skills.contains(skill) then 1 else 0
          )
        )
      )
    )

  /** The sorted sizes within the budget of the teams that cover every skill,
    * every subset enumerated (`team_sizes/4`).
    */
  def teamSizes(
      skillCount: Int,
      people: Vector[Vector[Int]],
      budget: Int
  ): Vector[Int] =
    subsets(people)
      .filter(chosen =>
        chosen.size <= budget && (0 until skillCount).forall(skill =>
          chosen.exists(_.contains(skill))
        )
      )
      .map(_.size)
      .distinct
      .sorted

  private def subsets(
      people: Vector[Vector[Int]]
  ): Vector[Vector[Vector[Int]]] =
    people.foldRight(Vector(Vector.empty[Vector[Int]]))((person, rest) =>
      rest ++ rest.map(person +: _)
    )

  /** The least size of a team covering every skill, by the dynamic programme
    * over the covered masks (`smallest_team/3`); nothing when no team covers
    * them, where the Prolog fails.
    */
  def smallestTeam(skillCount: Int, people: Vector[Vector[Int]]): Option[Int] =
    val table = people.foldLeft(Map(0 -> 0))((table, skills) =>
      val mask =
        skills.foldLeft(0)((accumulated, skill) => accumulated | (1 << skill))
      table.toVector.sortBy(_._1).foldLeft(table) {
        case (current, (covered, count)) =>
          val union = covered | mask
          if current.get(union).exists(_ <= count + 1) then current
          else current.updated(union, count + 1)
      }
    )
    table.get((1 << skillCount) - 1)

  /** The people of a point, each skill held when the 29th bit of its state of
    * the linear congruential sequence from 11 is clear (`point_people/3`).
    */
  def pointPeople(skillCount: Int, peopleCount: Int): Vector[Vector[Int]] =
    DynamicReferences
      .states(11, skillCount * peopleCount)
      .grouped(skillCount)
      .toVector
      .map(states =>
        states.zipWithIndex.collect {
          case (state, skill) if (state >> 29) == 0 => skill
        }
      )

  /** The problems (`team_point/4`), the budget the least size plus the slack.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("team_point").map {
      case Vector(point, skillCount, peopleCount, slack) =>
        val skills = ProblemData.small(skillCount)
        val people = pointPeople(skills, ProblemData.small(peopleCount))
        val smallest = smallestTeam(skills, people).getOrElse(
          throw IllegalArgumentException(s"no team covers $point")
        )
        val slackValue = ProblemData.small(slack)
        val expected =
          if slackValue == 0 then Expected.One(Scott.unaryTree(smallest))
          else if slackValue < 0 then Expected.Trees(Vector.empty)
          else
            throw IllegalArgumentException(
              s"the Prolog expects nothing for a positive slack: $point"
            )
        ReductionProblem(
          ProblemData.text(point),
          teamTerm(group.attractors, skills, people, smallest + slackValue),
          "unary",
          expected,
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a team point: $other")
    }
