package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** The courses that can be completed, the port
  * of `problems/hidden_37_courses`: a course is done when every
  * prerequisite is, the least fixed point.
  */
object Hidden37Courses:

  private val family = "hidden_37_courses"

  /** Under the lets of the courses, `(\done. [done Count c c top | c a course]) Done`
    * (`courses_term/3` with a step budget of the course count). The budget is
    * written once, as the successor of the last course's let-bound numeral,
    * so that the program does not grow with a numeral of the count per course.
    */
  def coursesTerm(attractors: Attractors, count: Int, prerequisites: Vector[Vector[Int]]): Term =
    Graphs.numeralLets(
      count,
      courses =>
        val lastCourse = courses.lastOption.getOrElse(throw IllegalArgumentException("a point has no course"))
        λ(budget =>
          λ(done => members(courses.map(course => done(budget)(course)(course)(top))))(
            doneFunction(attractors, courses, prerequisites)
          )
        )(λ(_ => λ(successor => successor(lastCourse))))
    )

  /** `Y (\self. \budget. \course. budget top (\p. foldr and true (map (self p) (case course))))`,
    * the case the list of the course's prerequisites (`done_function/3` with
    * a budget, so that each reference answer has its proof). Without the budget a course on a cycle reads ⊥ in
    * DdLP96's reading, the whole choice with it, and the program is below
    * every closed βη normal form in ⊑_O. With it a chain of
    * prerequisites that reaches a cycle spends the budget and gives top, and a
    * course whose chains are all acyclic, each shorter than the course count,
    * is done: the completable courses (`completable`).
    */
  private def doneFunction(attractors: Attractors, courses: Vector[Term], prerequisites: Vector[Vector[Int]]): Term =
    val foldr = attractors.functionSurface("foldr", Spelling.Direct)
    val and = attractors.functionSurface("and", Spelling.Direct)
    val trueValue = attractors.attractorSurface("true", Spelling.Direct)
    val map = attractors.functionSurface("map", Spelling.Direct)
    val lists = prerequisites.map(indices => SetFree.scottList(attractors, indices.map(courses)))
    attractors.fixpoint(
      λ(self =>
        λ(budget =>
          λ(course =>
            budget(top)(λ(predecessor =>
              foldr(and)(trueValue)(map(self(predecessor))(Graphs.numeralCase(lists, course)))
            ))
          )
        )
      )
    )

  /** The completable courses, the least fixed point of readiness
    * (`completable/3`).
    */
  def completable(count: Int, prerequisites: Vector[Vector[Int]]): Vector[Int] =
    leastFixedPoint(count, prerequisites, Vector.empty)

  @tailrec
  private def leastFixedPoint(count: Int, prerequisites: Vector[Vector[Int]], set: Vector[Int]): Vector[Int] =
    val next = (0 until count).toVector.filter(course => prerequisites(course).forall(set.contains))
    if next == set then set else leastFixedPoint(count, prerequisites, next)

  private def next(state: Long): Long = DynamicReferences.nextRandom(state)

  /** The shape of a point's prerequisites, the constructors of
    * problems/hidden_37_courses/shape in order: the chain, the ladder of
    * diamonds, the random prerequisites of a degree with back edges, and the
    * two traps, the cycles among a chain and the ladder on a cycle.
    */
  enum CourseShape:
    case Chain
    case Diamonds
    case Random(degree: Int, backEdges: Int)
    case TrapCycles
    case TrapLadder

  /** The shape a field writes, a constructor of
    * problems/hidden_37_courses/shape read by its position
    * (`ProblemData.alternative`), random's fields its degree and back edges.
    */
  def shape(field: ProblemField): CourseShape = ProblemData.alternative(field, ProblemData.caseCount[CourseShape]) match
    case (0, Vector())                  => CourseShape.Chain
    case (1, Vector())                  => CourseShape.Diamonds
    case (2, Vector(degree, backEdges)) => CourseShape.Random(ProblemData.small(degree), ProblemData.small(backEdges))
    case (3, Vector())                  => CourseShape.TrapCycles
    case (4, Vector())                  => CourseShape.TrapLadder
    case (position, fields) =>
      throw IllegalArgumentException(s"the shape of $family at position $position has ${fields.size} fields")

  /** The prerequisites of a shape (`shape_prerequisites/4`). */
  def shapePrerequisites(shape: CourseShape, count: Int, seed: Long): Vector[Vector[Int]] = shape match
    case CourseShape.Chain    => (0 until count).toVector.map(course => if course == 0 then Vector.empty else Vector(course - 1))
    case CourseShape.Diamonds => diamondLadder(count)
    case CourseShape.Random(degree, backEdges) => randomPrerequisites(count, degree, backEdges, seed)
    case CourseShape.TrapCycles =>
      (0 until count).toVector.map(course =>
        if course == 0 then Vector.empty
        else if course % 10 == 0 then Vector(course - 1, course)
        else if course % 10 == 5 then Vector(course - 1, course + 1)
        else Vector(course - 1)
      )
    case CourseShape.TrapLadder => Vector(count) +: (diamondLadder(count).tail :+ Vector(0))

  private def diamondLadder(count: Int): Vector[Vector[Int]] =
    (0 until count).toVector.map(course =>
      if course == 0 then Vector.empty
      else
        val position = course % 3
        if position == 0 then Vector(course - 2, course - 1) else Vector(course - position)
    )

  /** Up to `degree` random earlier courses each, then `backEdges` random
    * back edges (`random_prerequisites/5`).
    */
  private def randomPrerequisites(count: Int, degree: Int, backEdges: Int, seed: Long): Vector[Vector[Int]] =
    val (forward, state) = (0 until count).foldLeft((Vector.empty[Vector[Int]], seed)) { case ((found, current), course) =>
      val (required, following) = randomEarlier(degree, course, current, List.empty)
      (found :+ required.toVector, following)
    }
    (1 to backEdges)
      .foldLeft((forward, state)) { case ((prerequisites, current), _) =>
        val stateOne = next(current)
        val stateTwo = next(stateOne)
        val first = ((stateOne >> 8) % count).toInt
        val second = ((stateTwo >> 8) % count).toInt
        val (low, high) = (math.min(first, second), math.max(first, second))
        (if low == high then prerequisites else prerequisites.updated(low, high +: prerequisites(low)), stateTwo)
      }
      ._1

  @tailrec
  private def randomEarlier(left: Int, course: Int, state: Long, accumulated: List[Int]): (List[Int], Long) =
    if left == 0 || course == 0 then (accumulated, state)
    else
      val following = next(state)
      val earlier = ((following >> 8) % course).toInt
      randomEarlier(left - 1, course, following, if accumulated.contains(earlier) then accumulated else earlier :: accumulated)

  /** The prerequisites of a point (`point_prerequisites/3`). */
  def pointPrerequisites(group: ReductionGroup, point: String): Vector[Vector[Int]] =
    group.problems(family).keyed("course_point").get(point) match
      case Some(Vector(shape, count, seed, _)) =>
        shapePrerequisites(this.shape(shape), ProblemData.small(count), ProblemData.small(seed))
      case other => throw IllegalArgumentException(s"no course point $point: $other")

  /** The problems (`course_point/5`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("course_point").map(arguments =>
      val point = ProblemData.text(arguments.head)
      val prerequisites = pointPrerequisites(group, point)
      ReductionProblem(
        point,
        coursesTerm(group.attractors, prerequisites.size, prerequisites),
        "unary",
        Reduction.expectedOf(completable(prerequisites.size, prerequisites).map(Scott.unaryTree)),
        Reduction.hiddenLimits
      )
    )
