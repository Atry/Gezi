package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.NoFacts

import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** Deep terms evaluated and read in both modes without growing the JVM stack:
  * the evaluator, the tabling, the store, the expansion of heads and the
  * normal-form reader run on `scala.util.control.TailCalls` and on lists on the
  * heap. 100,000 levels under weak_head; 10,000 under tabling(weak_head), whose
  * readings of these terms make a few tables a level and would pass the table
  * limit (`ReadingState.defaultTableLimit`) at 100,000, still far beyond what
  * recursion on the JVM stack reaches. The results are compared without
  * printing them, since a failure message of a value this deep would itself
  * recurse per level.
  */
class DeepTermsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  // Measured 2026-11-14 on 2 CPUs (contest-lean.slice): the slowest test, "a deep normal form is read in both modes", takes 2.42 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite is within measurement noise of the 3 s default (its slowest test took 2 to 3 s) with no reason yet; its slow tests are to be made fast. The body runs on the JVM's default stack. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(5, "s")

  private def depth(mode: Mode): Int = mode match
    case Mode.TablingWeakHead => 10000
    case _                    => 100000

  /** The Church numeral of the depth applied to the identity and to K: its head
    * is K, after a spine of the depth's applications in function position.
    */
  private def numeralApplied(depth: Int): Term =
    λ(f => λ(x => (0 until depth).foldLeft(x)((body, _) => f(body))))(
      λ(i => i)
    )(λ(k => λ(_ => k)))

  /** Applications nested to the depth in argument position under one binder:
    * \x. x (x (... (x (\y. y)))).
    */
  private def deepNormalForm(depth: Int): Term =
    λ(x => (0 until depth).foldLeft(λ(y => y))((body, _) => x(body)))

  test("a deep spine of applications evaluates in both modes") {
    Vector(Mode.WeakHead, Mode.TablingWeakHead).foreach(mode =>
      val value = EvaluatorTesting.valueOf(numeralApplied(depth(mode)))
      assertEquals(
        (mode, EvaluatorTesting.headsWithin(mode, value, 10000000)),
        (
          mode,
          Bounded.Finished(
            Vector(EvaluatorTesting.lambdaTerm(λ(k => λ(_ => k))))
          )
        )
      )
    )
  }

  test("a deep normal form is read in both modes") {
    Vector(Mode.WeakHead, Mode.TablingWeakHead).foreach(mode =>
      val value = EvaluatorTesting.valueOf(deepNormalForm(depth(mode)))
      val expected = EvaluatorTesting.instructionOf(deepNormalForm(depth(mode)))
      val bounded = EvaluatorTesting.normalFormsWithin(mode, value, 10000000)
      assert(bounded.finished, s"the reading under $mode stopped")
      val readOwn = bounded match
        case Bounded.Finished(Vector(found)) => Configured.same(found, expected)
        case _                               => false
      assert(
        readOwn,
        s"under $mode the normal forms read are not the term's own"
      )
    )
  }
