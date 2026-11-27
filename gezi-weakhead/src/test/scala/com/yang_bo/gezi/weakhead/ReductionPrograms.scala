package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The program of the reduction problem `reduction_fibonacci_twenty` that
  * `normal_forms.plt` reads, ported as a test helper in the front end's HOAS:
  * the pieces of `problems/merge_dynamic` (the unary and binary numerals and
  * the binary arithmetic under its lets), `problems/merge_fibonacci` (fib by
  * its two recursive calls) and `problems/reduction_problems` (the program
  * `fibonacci(N)`). The module `corpora` ports the families whole. Each
  * recursive function is its body applied to itself, the body built twice, as
  * the Prolog generator builds it, so that no binder occurs twice.
  */
object ReductionPrograms:

  private def trueTerm: Term = λ(t => λ(_ => t))
  private def falseTerm: Term = λ(_ => λ(f => f))

  /** The Scott unary numeral of the count, zero = \z. \s. z and successor p
    * = \z. \s. s p.
    */
  def unary(count: Int): Term =
    if count == 0 then λ(z => λ(_ => z))
    else λ(_ => λ(s => s(unary(count - 1))))

  private def binaryZero: Term = λ(z => λ(_ => λ(_ => z)))
  private def binaryEven(half: Term): Term = λ(_ => λ(e => λ(_ => e(half))))
  private def binaryOdd(half: Term): Term = λ(_ => λ(_ => λ(o => o(half))))

  /** The label-free binary numeral of the natural. */
  def binary(natural: BigInt): Term =
    if natural == 0 then binaryZero
    else if natural % 2 == 0 then binaryEven(binary(natural / 2))
    else binaryOdd(binary(natural / 2))

  /** \self. \n. n 1 (\h. odd h) (\h. even (self self h)). */
  private def incrementBody: Term =
    λ(self =>
      λ(n =>
        n(binaryOdd(binaryZero))(λ(h => binaryOdd(h)))(
          λ(g => binaryEven(self(self)(g)))
        )
      )
    )

  /** Binary addition with the carry by the increment. */
  private def plusBody(increment: Term): Term =
    λ(self =>
      λ(a =>
        λ(b =>
          a(b)(
            λ(h1 =>
              b(a)(λ(k1 => binaryEven(self(self)(h1)(k1))))(
                λ(k2 => binaryOdd(self(self)(h1)(k2)))
              )
            )
          )(
            λ(h2 =>
              b(a)(λ(k3 => binaryOdd(self(self)(h2)(k3))))(
                λ(k4 => binaryEven(increment(self(self)(h2)(k4))))
              )
            )
          )
        )
      )
    )

  /** The same variant and equal halves. */
  private def equalityBody(trueVariable: Term, falseVariable: Term): Term =
    λ(self =>
      λ(a =>
        λ(b =>
          a(b(trueVariable)(λ(_ => falseVariable))(λ(_ => falseVariable)))(
            λ(h1 =>
              b(falseVariable)(λ(k1 => self(self)(h1)(k1)))(
                λ(_ => falseVariable)
              )
            )
          )(
            λ(h2 =>
              b(falseVariable)(λ(_ => falseVariable))(
                λ(k2 => self(self)(h2)(k2))
              )
            )
          )
        )
      )
    )

  /** The body under the lets of the booleans and the binary operations; the
    * body receives true, false, plus and equality.
    */
  private def withArithmetic(body: (Term, Term, Term, Term) => Term): Term =
    λ(trueVariable =>
      λ(falseVariable =>
        λ(increment =>
          λ(plus =>
            λ(equality => body(trueVariable, falseVariable, plus, equality))(
              equalityBody(trueVariable, falseVariable)(
                equalityBody(trueVariable, falseVariable)
              )
            )
          )(plusBody(increment)(plusBody(increment)))
        )(incrementBody(incrementBody))
      )(falseTerm)
    )(trueTerm)

  /** \self. \n. n 0 (\p. p 1 (\q. plus (self self p) (self self q))). */
  private def fibonacciBody(plus: Term, zero: Term, one: Term): Term =
    λ(self =>
      λ(n =>
        n(zero)(λ(p => p(one)(λ(q => plus(self(self)(p))(self(self)(q))))))
      )
    )

  /** The program of `reduction_fibonacci_N`: fib applied to the unary numeral
    * of N, under the lets of the arithmetic and of zero and one.
    */
  def fibonacciProgram(count: Int): Term =
    withArithmetic((_, _, plus, _) =>
      λ(zero =>
        λ(one =>
          λ(fibonacci => fibonacci(unary(count)))(
            fibonacciBody(plus, zero, one)(fibonacciBody(plus, zero, one))
          )
        )(binary(1))
      )(binary(0))
    )

  /** fib by iteration, the expected algorithm. */
  def referenceFibonacci(count: Int): BigInt =
    (0 until count)
      .foldLeft((BigInt(0), BigInt(1)))((pair, _) =>
        (pair._2, pair._1 + pair._2)
      )
      ._1
