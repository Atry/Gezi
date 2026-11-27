package gezi.contest.corpora.reductions

/** The snapshot of the problems of `problems/hidden_37_courses`, whose purpose
  * is to catch a generator change that alters a problem's program, type,
  * expected trees or limits.
  */
class Hidden37CoursesTest
    extends GeneratedProgramsSuite("contest_hidden_37_courses"):
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, Hidden37Courses.problems(group))

/** The snapshot of the problems of `problems/hidden_37_obstacles`, whose
  * purpose is to catch a generator change that alters a problem's program,
  * type, expected trees or limits.
  */
class Hidden37ObstaclesTest
    extends GeneratedProgramsSuite("contest_hidden_37_obstacles"):
  def generated(group: ReductionGroup) =
    ReductionTesting.problemLines(group, Hidden37Obstacles.problems(group))
