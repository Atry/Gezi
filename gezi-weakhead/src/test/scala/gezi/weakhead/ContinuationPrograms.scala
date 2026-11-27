package gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Term
import gezi.generatedinputs.HoasGenerators

/** Generated programs in continuation passing style, for the laws of
  * `ContinuationReading`.
  *
  * A program is `λk. S`, `S` a spine of steps `f (λx1 … xm. S')` ending in `k`
  * applied to values, applied to a closed continuation. Each step's function is
  * drawn from functions that call their continuation in tail position at the
  * step's arity (once, on both sides of a choice, on both sides of a parallel),
  * and, in `programs` only, from those that do not: that store the continuation
  * in a field, call it on its own result, apply its result again, never call
  * it, or call it at another arity. A function may take an earlier step's value
  * first, so that a step's function is known only when the step is reduced,
  * where `Packed` checks it.
  */
object ContinuationPrograms:

  /** A value a function hands on: a small closed normal form. */
  private val values: Gen[Term] = HoasGenerators.normalForm

  /** The kinds of step functions that call their continuation in tail position
    * at the step's arity.
    */
  private val tailKinds: Range[Int] = Range.constant(0, 3)

  /** Every kind of step function, those that break the condition included. */
  private val everyKind: Range[Int] = Range.constant(0, 8)

  /** A function that takes its continuation last and calls it with `arity`
    * values, in one of the ways of a kind drawn from `kinds`. `earlier` holds
    * the values bound by earlier steps, which the function may take before its
    * continuation.
    */
  private def function(
      arity: Int,
      earlier: Vector[Term],
      kinds: Range[Int]
  ): Gen[Term] =
    for
      handed <- values.list(Range.singleton(arity + 1))
      wrongArity <- Gen
        .int(Range.constant(0, 3))
        .map(drawn => if drawn == arity then arity + 1 else drawn)
      kind <- Gen.int(kinds)
      taken <- Gen.int(Range.constant(0, earlier.size))
    yield
      val called: Term => Term = continuation =>
        handed.take(arity).foldLeft(continuation)(_(_))
      val made: Term = kind match
        // In tail position at the arity: once, on both sides of a choice, on both sides of a parallel.
        case 0 | 1 => Term.λ(continuation => called(continuation))
        case 2     =>
          Term.λ(continuation => called(continuation) + called(continuation))
        case 3 =>
          Term.λ(continuation => called(continuation) ∥ called(continuation))
        // Not: stored in a field, called on its own result, its result applied again, never called, another arity.
        case 4 => Term.λ(continuation => Term.λ(tuple => tuple(continuation)))
        case 5 => Term.λ(continuation => continuation(called(continuation)))
        case 6 => Term.λ(continuation => called(continuation)(handed(arity)))
        case 7 => Term.λ(_ => handed(arity))
        case _ =>
          Term.λ(continuation =>
            handed.take(wrongArity).foldLeft(continuation)(_(_))
          )
      if taken < earlier.size then Term.λ(_ => made)(earlier(taken)) else made

  /** The spine of `steps` steps after the values bound so far, ending in the
    * program's continuation applied to some of them.
    */
  private def spine(
      steps: Int,
      continuation: Term,
      earlier: Vector[Term],
      kinds: Range[Int]
  ): Gen[Term] =
    if steps == 0 then
      for handed <- Gen.int(Range.constant(1, 2))
      yield (0 until handed).foldLeft(continuation)((applied, position) =>
        applied(if earlier.isEmpty then Term.λ(x => x)
        else earlier(position % earlier.size))
      )
    else
      for
        arity <- Gen.int(Range.constant(1, 2))
        stepFunction <- function(arity, earlier, kinds)
        rest <- spineUnder(arity, steps - 1, continuation, earlier, kinds)
      yield stepFunction(rest)

  /** The continuation of a step of the arity: its binders, then the rest of the
    * spine. The rest is drawn with stand-ins for the binders and spliced in
    * under the binders, since a HOAS term draws nothing inside an abstraction.
    */
  private def spineUnder(
      arity: Int,
      steps: Int,
      continuation: Term,
      earlier: Vector[Term],
      kinds: Range[Int]
  ): Gen[Term] =
    val placeholders = (0 until arity)
      .map(position => Term.BoundVariable(-1 - earlier.size - position))
      .toVector
    spine(steps, continuation, earlier ++ placeholders, kinds).map(drawn =>
      def bound(names: Vector[Term]): Term =
        if names.size == arity then
          substituted(drawn, placeholders.zip(names).toMap)
        else Term.λ(name => bound(names :+ name))
      bound(Vector.empty)
    )

  /** The term with each stand-in replaced. */
  private def substituted(term: Term, replacements: Map[Term, Term]): Term =
    term match
      case stand @ Term.BoundVariable(_) => replacements.getOrElse(stand, stand)
      case Term.Abstraction(body)        =>
        Term.Abstraction(argument => substituted(body(argument), replacements))
      case Term.Application(function, argument) =>
        Term.Application(
          substituted(function, replacements),
          substituted(argument, replacements)
        )
      case Term.ChoiceChain(members) =>
        Term.ChoiceChain(members.map(substituted(_, replacements)))
      case Term.Choice(left, right) =>
        Term.Choice(
          substituted(left, replacements),
          substituted(right, replacements)
        )
      case Term.Parallel(left, right) =>
        Term.Parallel(
          substituted(left, replacements),
          substituted(right, replacements)
        )
      case other => other

  /** A program `λk. S` of the steps. */
  private def programOf(steps: Int, kinds: Range[Int]): Gen[Term] =
    val standIn = Term.BoundVariable(-1000)
    spine(steps, standIn, Vector.empty, kinds).map(drawn =>
      Term.λ(continuation => substituted(drawn, Map(standIn -> continuation)))
    )

  /** A program applied to its continuation, sometimes twice in one choice, so
    * that two consumers meet one shared table.
    */
  private def applied(kinds: Range[Int]): Gen[Term] =
    for
      steps <- Gen.int(Range.constant(1, 4))
      drawnContinuation <- values
      twice <- Gen.boolean
      program <- programOf(steps, kinds)
    yield
      val called = program(drawnContinuation)
      if twice then called + program(Term.λ(x => x)) else called

  /** Programs whose step functions are of every kind. */
  val programs: Gen[Term] = applied(everyKind)

  /** Programs whose every step function calls its continuation in tail position
    * at the step's arity.
    */
  val tailPrograms: Gen[Term] = applied(tailKinds)

  /** One program, its step functions of every kind, applied to each of two or
    * three continuations: consumers of the one table of the program applied to
    * the pack, read through keys of their own.
    */
  val consumers: Gen[Vector[Term]] =
    for
      steps <- Gen.int(Range.constant(1, 4))
      program <- programOf(steps, everyKind)
      continuations <- values.list(Range.constant(2, 3))
    yield continuations.toVector.map(program(_))
