package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** The obstacles removed on the way across a grid within a budget, round
  * 37's hidden subtask, the port of `problems/hidden_37_obstacles`.
  */
object Hidden37Obstacles:

  private val family = "hidden_37_obstacles"

  /** The program (`obstacles_term/3`):
    * `(\grid. (\nth. (\blocked. \moves. \goal. Body) Blocked Moves Goal) Nth) Grid`.
    */
  def obstaclesTerm(attractors: Attractors, grid: Vector[Vector[Int]], budget: Int): Term =
    def function(name: String) = attractors.functionSurface(name, Spelling.Direct)
    val (lastRow, lastColumn) = (grid.size - 1, grid.head.size - 1)
    λ(gridVariable =>
      λ(nth =>
        λ(blocked =>
          λ(moves =>
            λ(goal =>
              val difference = function("natural_difference")
              λ(predecessor =>
                goFunction(attractors, blocked, moves, goal, predecessor)(λ(left => difference(unary(budget))(left)))(
                  unary(budget)
                )(binary(stepBudget(grid, budget)))(function("pair")(unary(0))(unary(0)))
              )(binaryPredecessor(attractors))
            )
          )
        )(blockedFunction(attractors, nth, gridVariable))(movesFunction(attractors, lastRow, lastColumn))(
          goalFunction(attractors, lastRow, lastColumn)
        )
      )(nthFunction(attractors))
    )(SetFree.bitLists(attractors, grid))

  /** The element at a unary index (`nth_function/1`). */
  private def nthFunction(attractors: Attractors): Term =
    val nil = attractors.attractorSurface("nil", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(list => λ(index => list(nil)(λ(head => λ(tail => index(head)(λ(predecessor => self(tail)(predecessor))))))))
      )
    )

  /** `\r. \c. member (nth grid r) c` (`blocked_function/3`). */
  private def blockedFunction(attractors: Attractors, nth: Term, grid: Term): Term =
    val member = attractors.functionSurface("bit_set_member", Spelling.Direct)
    λ(row => λ(column => member(nth(grid)(row))(column)))

  /** The four moves that stay on the grid (`moves_function/3`). */
  private def movesFunction(attractors: Attractors, lastRow: Int, lastColumn: Int): Term =
    def function(name: String) = attractors.functionSurface(name, Spelling.Direct)
    val atLeastOne = function("natural_at_least")
    val atLeastTwo = function("natural_at_least")
    val successors = Vector.fill(4)(function("successor"))
    λ(row =>
      λ(column =>
        λ(continuation =>
          members(
            Vector(
              row(top)(λ(above => continuation(above)(column))),
              atLeastOne(unary(lastRow))(successors(0)(row))(continuation(successors(1)(row))(column))(top),
              column(top)(λ(left => continuation(row)(left))),
              atLeastTwo(unary(lastColumn))(successors(2)(column))(continuation(row)(successors(3)(column)))(top)
            )
          )
        )
      )
    )

  /** `\p. and (equal (first p) last) (equal (second p) last)`
    * (`goal_function/3`).
    */
  private def goalFunction(attractors: Attractors, lastRow: Int, lastColumn: Int): Term =
    def function(name: String) = attractors.functionSurface(name, Spelling.Direct)
    val and = function("and")
    val equalOne = function("natural_equal")
    val equalTwo = function("natural_equal")
    val first = function("first")
    val second = function("second")
    λ(position => and(equalOne(first(position))(unary(lastRow)))(equalTwo(second(position))(unary(lastColumn))))

  /** The steps a walk may take: the number of states, a cell with the
    * removals left, so that every reachable state is reached by a walk of
    * fewer steps and the budget changes no answer (`removalCounts`). Written
    * as a canonical binary numeral, whose digits grow with the logarithm of
    * the count, since a unary numeral of up to 64 × 64 × (K + 1) would make
    * the program as large as the count.
    */
  private def stepBudget(grid: Vector[Vector[Int]], budget: Int): Int =
    grid.size * grid.headOption.getOrElse(throw IllegalArgumentException("a grid has no row")).size * (budget + 1)

  /** The predecessor of a positive canonical binary numeral, canonical:
    * pred (2h) = 2 pred(h) + 1 for h ≥ 1, pred (2h + 1) = 2h, which is zero
    * when h is; zero to zero, a case `goFunction` never reaches.
    */
  private def binaryPredecessor(attractors: Attractors): Term =
    val zero = attractors.attractorSurface("binary_zero", Spelling.Direct)
    val evenOne = attractors.attractorSurface("binary_even", Spelling.Direct)
    val evenTwo = attractors.attractorSurface("binary_even", Spelling.Direct)
    val odd = attractors.attractorSurface("binary_odd", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(number =>
          number(zero)(λ(half => odd(self(half))))(λ(half => half(zero)(λ(_ => evenOne(half)))(λ(_ => evenTwo(half)))))
        )
      )
    )

  /** The search over the moves, an obstacle costing one unit of the budget
    * (`go_function/4`), each move one unit of a step budget, a binary
    * numeral, top once it is spent (so that each reference answer has its proof). Without the step budget a walk round the
    * free cells reads ⊥ in DdLP96's reading (a choice is a meet and Y the
    * least fixed point), the whole choice with it, and the program would be
    * below every closed βη normal form in ⊑_O.
    */
  private def goFunction(attractors: Attractors, blocked: Term, moves: Term, goal: Term, predecessor: Term): Term =
    val pairOne = attractors.functionSurface("pair", Spelling.Direct)
    val pairTwo = attractors.functionSurface("pair", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(continuation =>
          λ(remaining =>
            λ(steps =>
              λ(position =>
                members(
                  Vector(
                    goal(position)(continuation(remaining))(top),
                    λ(advance => steps(top)(λ(_ => advance))(λ(_ => advance)))(
                      λ(stepsLeft =>
                        position(λ(row =>
                          λ(column =>
                            moves(row)(column)(λ(nextRow =>
                              λ(nextColumn =>
                                blocked(nextRow)(nextColumn)(remaining(top)(λ(removalsLeft =>
                                  self(continuation)(removalsLeft)(stepsLeft)(pairOne(nextRow)(nextColumn))
                                )))(self(continuation)(remaining)(stepsLeft)(pairTwo(nextRow)(nextColumn)))
                              )
                            ))
                          )
                        ))
                      )(predecessor(steps))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  private def neighbours(grid: Vector[Vector[Int]], cell: (Int, Int)): Vector[(Int, Int)] =
    Vector((-1, 0), (1, 0), (0, -1), (0, 1))
      .map((rowStep, columnStep) => (cell._1 + rowStep, cell._2 + columnStep))
      .filter((row, column) => row >= 0 && row < grid.size && column >= 0 && column < grid.head.size)

  /** The sorted numbers of obstacles removed on the walks across within the
    * budget, by the states reachable from the corner (`removal_counts/3`).
    */
  def removalCounts(grid: Vector[Vector[Int]], budget: Int): Vector[Int] =
    val seen = reachableStates(List(((0, 0), budget)), grid, Set.empty)
    val last = (grid.size - 1, grid.head.size - 1)
    (0 to budget).filter(left => seen.contains((last, left))).map(budget - _).distinct.sorted.toVector

  @tailrec
  private def reachableStates(
      pending: List[((Int, Int), Int)],
      grid: Vector[Vector[Int]],
      seen: Set[((Int, Int), Int)]
  ): Set[((Int, Int), Int)] =
    pending match
      case Nil => seen
      case state :: states =>
        if seen.contains(state) then reachableStates(states, grid, seen)
        else
          val (cell, left) = state
          val nexts = neighbours(grid, cell).flatMap(neighbour =>
            if grid(neighbour._1)(neighbour._2) == 0 then Vector((neighbour, left))
            else if left > 0 then Vector((neighbour, left - 1))
            else Vector.empty
          )
          reachableStates(nexts.toList ++ states, grid, seen + state)

  /** The fewest obstacles on a walk across, layer by layer of cost
    * (`fewest_removals/2`); throws when the corner is unreachable, where the
    * Prolog fails.
    */
  def fewestRemovals(grid: Vector[Vector[Int]]): Int =
    costLayers(List((0, 0)), List.empty, grid, Set((0, 0)), 0)

  @tailrec
  private def costLayers(
      layer: List[(Int, Int)],
      next: List[(Int, Int)],
      grid: Vector[Vector[Int]],
      seen: Set[(Int, Int)],
      cost: Int
  ): Int =
    val last = (grid.size - 1, grid.head.size - 1)
    if layer.contains(last) then cost
    else
      layer match
        case Nil =>
          if next.isEmpty then throw IllegalArgumentException("the far corner is unreachable")
          costLayers(next, List.empty, grid, seen, cost + 1)
        case cell :: cells =>
          val (layerAfter, nextAfter, seenAfter) =
            neighbours(grid, cell).foldLeft((cells, next, seen)) { case ((currentLayer, currentNext, currentSeen), neighbour) =>
              if currentSeen.contains(neighbour) then (currentLayer, currentNext, currentSeen)
              else if grid(neighbour._1)(neighbour._2) == 0 then (neighbour :: currentLayer, currentNext, currentSeen + neighbour)
              else (currentLayer, neighbour :: currentNext, currentSeen + neighbour)
            }
          costLayers(layerAfter, nextAfter, grid, seenAfter, cost)

  /** The grid of a point: random cells, three in five an obstacle, the two
    * corners freed (`point_grid/2`).
    */
  def pointGrid(rows: Int, columns: Int, seed: Long): Vector[Vector[Int]] =
    val cells = DynamicReferences.states(seed, rows * columns).map(state => if (state >> 16) % 5 < 3 then 1 else 0)
    val grid = cells.grouped(columns).toVector
    val freed = grid.updated(0, grid(0).updated(0, 0))
    freed.updated(rows - 1, freed(rows - 1).updated(columns - 1, 0))

  /** The problems (`obstacles_point/6`), the budget the fewest removals plus
    * the slack, never negative.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("obstacles_point").flatMap {
      case Vector(point, rows, columns, seed, slack, _) =>
        val grid = pointGrid(ProblemData.small(rows), ProblemData.small(columns), ProblemData.small(seed))
        val budget = fewestRemovals(grid) + ProblemData.small(slack)
        Option.when(budget >= 0)(
          ReductionProblem(
            ProblemData.text(point),
            obstaclesTerm(group.attractors, grid, budget),
            "unary",
            Reduction.expectedOf(removalCounts(grid, budget).map(Scott.unaryTree)),
            Reduction.hiddenLimits
          )
        )
      case other => throw IllegalArgumentException(s"not an obstacles point: $other")
    }
