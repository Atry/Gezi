package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemField

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The least finishing time of jobs placed on workers, the port of
  * `problems/hidden_37_workers`.
  */
object Hidden37Workers:

  private val family = "hidden_37_workers"

  /** The slack of a point, the constructors of problems/hidden_37_workers/slack
    * in order: the near miss, whose jobs have one lengthened and whose budget
    * is the least, and the amount added to the least to make the budget.
    */
  enum Slack:
    case Near
    case Added(amount: Int)

  /** The slack a field writes, a constructor of
    * problems/hidden_37_workers/slack read by its position
    * (`ProblemData.alternative`), added's field its amount.
    */
  def slack(field: ProblemField): Slack =
    ProblemData.alternative(field, ProblemData.caseCount[Slack]) match
      case (0, Vector())       => Slack.Near
      case (1, Vector(amount)) => Slack.Added(ProblemData.small(amount))
      case (position, fields)  =>
        throw IllegalArgumentException(
          s"the slack of $family at position $position has ${fields.size} fields"
        )

  /** `(\assign. \min. Place Jobs Times (\caps. difference Budget (foldr min Budget caps))) Assign Min`
    * (`workers_term/4`).
    */
  def workersTerm(
      attractors: Attractors,
      jobs: Vector[Int],
      workers: Int,
      budget: Int
  ): ProblemTerm =
    val foldr = attractors.functionSurface("foldr", Spelling.Direct)
    val difference =
      attractors.functionSurface("natural_difference", Spelling.Direct)
    λ(assign =>
      λ(minimum =>
        placeFunction(attractors, assign)(numeralsSurface(attractors, jobs))(
          numeralsSurface(attractors, Vector.fill(workers)(budget))
        )(
          λ(caps =>
            difference(unary(budget))(foldr(minimum)(unary(budget))(caps))
          )
        )
      )
    )(assignFunction(attractors))(minimumFunction(attractors))

  /** The job placed on a worker whose cap it fits, or on a later one
    * (`assign_function/1`).
    */
  private def assignFunction(attractors: Attractors): ProblemTerm =
    val atLeast =
      attractors.functionSurface("natural_at_least", Spelling.Direct)
    val difference =
      attractors.functionSurface("natural_difference", Spelling.Direct)
    val consOne = attractors.attractorSurface("cons", Spelling.Direct)
    val consTwo = attractors.attractorSurface("cons", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(caps =>
          λ(job =>
            λ(continuation =>
              caps(top)(
                λ(cap =>
                  λ(others =>
                    members(
                      Vector(
                        atLeast(cap)(job)(
                          continuation(consOne(difference(cap)(job))(others))
                        )(top),
                        self(others)(job)(
                          λ(rest => continuation(consTwo(cap)(rest)))
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

  /** Every job assigned in turn (`place_function/2`). */
  private def placeFunction(
      attractors: Attractors,
      assign: ProblemTerm
  ): ProblemTerm =
    attractors.fixpoint(
      λ(self =>
        λ(jobs =>
          λ(caps =>
            λ(continuation =>
              jobs(continuation(caps))(
                λ(job =>
                  λ(rest =>
                    assign(caps)(job)(λ(next => self(rest)(next)(continuation)))
                  )
                )
              )
            )
          )
        )
      )
    )

  /** `\a. \b. at_least a b b a` (`min_function/1`). */
  private def minimumFunction(attractors: Attractors): ProblemTerm =
    val atLeast =
      attractors.functionSurface("natural_at_least", Spelling.Direct)
    λ(first => λ(second => atLeast(first)(second)(second)(first)))

  /** The Scott list of the unary numerals (`numerals_surface/2`). */
  private def numeralsSurface(
      attractors: Attractors,
      numbers: Vector[Int]
  ): ProblemTerm =
    SetFree.scottList(attractors, numbers.map(unary))

  /** The least time within which the workers finish the jobs, the first from
    * the largest job to their sum that is finishable
    * (`least_finishing_time/3`).
    */
  def leastFinishingTime(jobs: Vector[Int], workers: Int): Int =
    (jobs.max to jobs.sum)
      .find(finishable(jobs, workers, _))
      .getOrElse(
        throw IllegalArgumentException(s"the jobs $jobs are not finishable")
      )

  /** Whether the jobs fit on the workers within the budget: the least pair of
    * workers opened and time on the last one for each subset of the jobs, the
    * subsets in increasing order of their masks (`finishable/3`). The Prolog
    * keeps the table in a term changed in place by `nb_setarg/3`; here it is an
    * immutable map threaded through the fold.
    */
  def finishable(jobs: Vector[Int], workers: Int, budget: Int): Boolean =
    val size = 1 << jobs.size
    val best = (0 until size).foldLeft(Map(0 -> (1, 0)))((table, mask) =>
      table.get(mask) match
        case None                 => table
        case Some((opened, time)) =>
          jobs.indices
            .filter(index => (mask & (1 << index)) == 0)
            .foldLeft(table)((current, index) =>
              val job = jobs(index)
              val next = if time + job <= budget then (opened, time + job)
              else (opened + 1, job)
              val union = mask | (1 << index)
              if current
                  .get(union)
                  .forall(old => Ordering[(Int, Int)].lt(next, old))
              then current.updated(union, next)
              else current
            )
    )
    best(size - 1)._1 <= workers

  /** The jobs of a point, each 1 to 12 (`point_jobs/2`). */
  def pointJobs(count: Int, seed: Long): Vector[Int] =
    DynamicReferences
      .states(seed, count)
      .map(state => ((state >> 16) % 12 + 1).toInt)

  /** The jobs, workers and budget of a point (`point_problem/4`): the near trap
    * lengthens the first job that raises the least time.
    */
  def pointProblem(
      group: ReductionGroup,
      point: String
  ): (Vector[Int], Int, Int) =
    group.problems(family).keyed("workers_point").get(point) match
      case Some(Vector(count, workers, seed, slack, _)) =>
        val workerCount = ProblemData.small(workers)
        val original =
          pointJobs(ProblemData.small(count), ProblemData.small(seed))
        val least = leastFinishingTime(original, workerCount)
        this.slack(slack) match
          case Slack.Near =>
            val longer = original.indices
              .map(position =>
                original.updated(position, original(position) + 1)
              )
              .find(leastFinishingTime(_, workerCount) > least)
              .getOrElse(
                throw IllegalArgumentException(
                  s"no lengthened job raises the least time of $point"
                )
              )
            (longer, workerCount, least)
          case Slack.Added(amount) => (original, workerCount, least + amount)
      case other =>
        throw IllegalArgumentException(s"no workers point $point: $other")

  /** The problems (`workers_point/6`): the budget when the jobs finish within
    * it, no tree otherwise.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group
      .problems(family)
      .rows("workers_point")
      .map(arguments =>
        val point = ProblemData.text(arguments.head)
        val (jobs, workers, budget) = pointProblem(group, point)
        val least = leastFinishingTime(jobs, workers)
        if budget > least then
          throw IllegalArgumentException(
            s"the budget of $point exceeds the least time"
          )
        ReductionProblem(
          point,
          workersTerm(group.attractors, jobs, workers, budget),
          "unary",
          if least <= budget then Expected.One(Scott.unaryTree(budget))
          else Expected.Trees(Vector.empty),
          Reduction.hiddenLimits
        )
      )
