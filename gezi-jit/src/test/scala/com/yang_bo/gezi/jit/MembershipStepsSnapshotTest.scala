package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.choice
import com.yang_bo.gezi.generatedinputs.SeededSnapshots
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NormalForms
import com.yang_bo.gezi.weakhead.ReadOut
import com.yang_bo.gezi.weakhead.ReadingState
import snapshot4s.generated.snapshotConfig

/** The snapshot of the read-out by membership (`ReadOut.Membership`, the
  * directed test of whether a head reads a normal form another head reads): for
  * generated terms over the naturals, the booleans and the lists of naturals,
  * with their types and `∥` and `+`, the number of normal forms read and the
  * steps spent, or the steps at which the limit stopped the reading. Its
  * purpose is to show, as a diff beside its input, every change of what the
  * read-out answers and of what it costs, among them a parallel filter by an
  * infinite type, such as `zero ∥ nat_type` and `nil ∥ list_type nat_type`,
  * which the enumeration of each head's reads this test replaced did not finish
  * within any limit. A reading still stops at the limit where the first head of
  * a set, or the term itself, has infinitely many normal forms, such as
  * `nat_type ∥ false`: the read-out reads the first head's normal forms one by
  * one.
  */
class MembershipStepsSnapshotTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with SeededSnapshots:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of MembershipStepsSnapshotTest, "the membership read-out of generated terms", takes 7.046 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  /** The limit of a reading, the reference's confirmation limit of the natives'
    * tests (`NativesTesting.confirmationLimit`). MEASURED 2026-11-12: at
    * 200,000 steps the 40 samples took 310 seconds, the readings that do not
    * finish building ever larger terms, so that their steps cost more as they
    * run.
    */
  private val limit: Long = NativesTesting.confirmationLimit

  private final case class Written(description: String, term: Term)

  private def library(key: String): Written =
    Written(key, JitTesting.libraryTerm(key))

  private def applied(function: Written, argument: Written): Written =
    Written(
      s"${function.description} (${argument.description})",
      function.term(argument.term)
    )

  private lazy val zero = library("zero")
  private lazy val successor = library("successor")
  private lazy val nil = library("nil")
  private lazy val cons = library("cons")
  private lazy val natType = library("nat_type")
  private lazy val listOfNaturals = applied(library("list_type"), natType)

  /** The library terms the leaves are read from, forced before the first test
    * and not charged to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => JitTesting.libraryTerms)

  private def leaf: Gen[Written] =
    Gen.element1(
      zero,
      applied(successor, zero),
      library("true"),
      library("false"),
      nil,
      applied(applied(cons, zero), nil),
      natType,
      library("boolean_type"),
      listOfNaturals
    )

  /** A term of at most the depth, a parallel drawn most often, since the
    * read-out by membership reads a parallel set of several heads.
    */
  private def written(depth: Int): Gen[Written] =
    if depth == 0 then leaf
    else
      Gen.frequency1(
        1 -> leaf,
        4 -> written(depth - 1).flatMap(left =>
          written(depth - 1).map(right =>
            Written(
              s"(${left.description}) ∥ (${right.description})",
              left.term ∥ right.term
            )
          )
        ),
        2 -> written(depth - 1).flatMap(left =>
          written(depth - 1).map(right =>
            Written(
              s"(${left.description}) + (${right.description})",
              choice(left.term, right.term)
            )
          )
        ),
        1 -> written(depth - 1).map(operand => applied(successor, operand)),
        1 -> written(depth - 1).map(operand =>
          applied(applied(cons, operand), nil)
        )
      )

  private def reading(term: Written): String =
    NormalForms
      .normalForm(
        Mode.TablingWeakHead,
        ReadOut.Membership,
        JitTesting.termValue(term.term)
      )
      .collected
      .result(ReadingState.fresh(limit)) match
      case Computed.Done(forms, after) =>
        s"${forms.size} normal forms, ${after.budget.spent} steps"
      case Computed.Stopped(after) => s"stopped at ${after.budget.spent} steps"

  test("the membership read-out of the parallel filters by an infinite type") {
    val witnesses = Vector(
      Written("zero ∥ nat_type", zero.term ∥ natType.term),
      Written("nil ∥ list_type nat_type", nil.term ∥ listOfNaturals.term)
    )
    assertFileSnapshot(
      witnesses
        .map(witness => s"${witness.description}\n=>\n${reading(witness)}\n")
        .mkString("\n"),
      "membership_steps/witnesses.txt"
    )
  }

  test("the membership read-out of generated terms") {
    assertSeededSnapshot(
      Gen.int(Range.constant(1, 2)).flatMap(written),
      20261112L,
      40,
      "membership_steps/generated.txt"
    )(
      _.description,
      identity[String]
    )(reading)
  }
