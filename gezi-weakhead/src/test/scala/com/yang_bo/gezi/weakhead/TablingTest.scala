package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.weakhead.Trampoline.done

/** The generic tabling (`Tabling`) on small equation systems over integers,
  * apart from the evaluator: a key that only re-enters itself, mutual recursion
  * around cycles, a set that grows over several iterations, a component nested
  * in another, and a stop that leaves only complete tables, each body
  * collecting the answers of the keys it reads before it gives its own (the
  * streaming bodies are `TablingStreamLawTest`'s). Each result is compared with
  * the least fixed point computed by naive iteration from the empty sets
  * (`leastFixedPoint`).
  */
class TablingTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  private final case class State(
      tables: Tables[State, Int, Int],
      budget: Budget
  )

  /** An equation system: the answers of a key from the answers of the keys it
    * reads, which it names first.
    */
  private final case class Equations(
      reads: Int => Vector[Int],
      answers: (Int, Vector[Set[Int]]) => Set[Int]
  )

  private def tabling(equations: Equations): Tabling[State, Int, Int] =
    Tabling(
      _.tables,
      (state, tables) => state.copy(tables = tables),
      _ => CompletedTables.unshared,
      (key, call) =>
        Answers.computed(
          Computation[State, Unit](state =>
            done(state.budget.charged match
              case Some(charged) =>
                Computed.Done((), state.copy(budget = charged))
              case None => Computed.Stopped(state))
          ).flatMap(_ =>
            Computation
              .traversed(equations.reads(key))(read => call(read).collected)
              .map(read =>
                equations.answers(key, read.map(_.toSet)).toVector.sorted
              )
          )
        )
    )

  private def solved(
      equations: Equations,
      key: Int,
      limit: Long
  ): Computed[State, AnswerSet[Int]] =
    tabling(equations)
      .answers(key)
      .collected
      .result(State(Tables.empty, Budget.of(limit))) match
      case Computed.Done(answers, after) =>
        Computed.Done(AnswerSet(answers.distinct, answers.toSet), after)
      case Computed.Stopped(stopped) => Computed.Stopped(stopped)

  /** The least fixed point by naive iteration over the keys, from the empty
    * sets.
    */
  private def leastFixedPoint(
      equations: Equations,
      keys: Vector[Int]
  ): Map[Int, Set[Int]] =
    def iterated(current: Map[Int, Set[Int]]): Map[Int, Set[Int]] =
      val next = keys
        .map(key =>
          (
            key,
            equations.answers(
              key,
              equations.reads(key).map(current.getOrElse(_, Set.empty))
            )
          )
        )
        .toMap
      if next == current then current else iterated(next)
    iterated(keys.map((_, Set.empty[Int])).toMap)

  private def assertLeast(equations: Equations, keys: Vector[Int]): Unit =
    val expected = leastFixedPoint(equations, keys)
    keys.foreach(key =>
      solved(equations, key, 100000) match
        case Computed.Done(answers, after) =>
          assertEquals((key, answers.members), (key, expected(key)))
          assertEquals(
            after.tables.open,
            Map.empty,
            "every table complete after the call"
          )
          after.tables.complete.foreach((completed, completedAnswers) =>
            assertEquals(
              (completed, completedAnswers.members),
              (completed, expected(completed))
            )
          )
        case Computed.Stopped(_) => fail(s"the call of $key stopped")
    )

  test(
    "a key that only re-enters itself has no answer, decided in finite time"
  ) {
    val equations = Equations(
      key => Vector(key),
      (_, read) =>
        val Vector(itself) = read: @unchecked
        itself
    )
    assertLeast(equations, Vector(0))
  }

  test("mutual recursion around cycles: reachability in a graph") {
    val successors = Map(
      0 -> Vector(1),
      1 -> Vector(2, 0),
      2 -> Vector(0, 3),
      3 -> Vector(4),
      4 -> Vector(3),
      5 -> Vector(0)
    )
    val equations =
      Equations(successors, (key, read) => read.foldLeft(Set(key))(_ ++ _))
    assertLeast(equations, Vector(0, 1, 2, 3, 4, 5))
  }

  test("a set that grows over several iterations of its component") {
    val equations = Equations(
      key => Vector(key, (key + 1) % 3),
      (key, read) =>
        val Vector(itself, next) = read: @unchecked
        Set(key) ++ itself.filter(_ < 30).map(_ + 3) ++ next
    )
    assertLeast(equations, Vector(0, 1, 2))
  }

  test("a component nested in another completes on its own") {
    // 0 and 1 form a cycle; 1 reads 2, which with 3 forms an inner cycle
    // that reads nothing outside it.
    val reads =
      Map(0 -> Vector(1), 1 -> Vector(0, 2), 2 -> Vector(3), 3 -> Vector(2))
    val equations =
      Equations(reads, (key, read) => read.foldLeft(Set(key * 10))(_ ++ _))
    assertLeast(equations, Vector(0, 1, 2, 3))
  }

  test(
    "a stop leaves the complete tables, and the incomplete ones with their answers found and their producers"
  ) {
    val successors = Map(0 -> Vector(1, 2), 1 -> Vector(1), 2 -> Vector(2, 0))
    val equations =
      Equations(successors, (key, read) => read.foldLeft(Set(key))(_ ++ _))
    solved(equations, 0, 3) match
      case Computed.Stopped(stopped) =>
        assertEquals(stopped.budget.spent, 3L)
        val left = stopped.tables
        val expected = leastFixedPoint(equations, Vector(0, 1, 2))
        assertEquals(left.complete.keySet, Set(1))
        assertEquals(left.complete(1).members, Set(1))
        assert(!left.inProgress, "no producer runs after the stop")
        assertEquals(left.open.keySet, Set(0, 2))
        assert(
          left.frames.values.forall(_.dirty),
          "every producer kept, marked dirty"
        )
        left.open.foreach((key, table) =>
          assert(
            table.answers.members.subsetOf(expected(key)),
            s"the approximation of $key holds only its answers"
          )
        )
      case Computed.Done(_, _) =>
        fail("three steps do not reach the fixed point")
  }

  test("the answers come in the order first found, the same on every run") {
    val equations = Equations(
      key => if key == 0 then Vector(2, 1) else Vector.empty,
      (key, read) => read.foldLeft(Set(key))(_ ++ _)
    )
    val runs = (1 to 3).map(_ =>
      solved(equations, 0, 100) match
        case Computed.Done(answers, _) => answers.ordered
        case Computed.Stopped(_)       => fail("stopped")
    )
    val Seq(ordered) = runs.distinct: @unchecked
    assertEquals(ordered.toSet, Set(0, 1, 2))
  }
