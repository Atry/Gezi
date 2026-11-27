package com.yang_bo.gezi.frontend

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** An object term written in Scala, in higher-order abstract syntax (the user,
  * 2026-10-31: "If you want to support Scala code to write the object language,
  * just use HOAS. Use unicode for the choice and parallel operator, use unary
  * `def apply` for application, so curried call becomes f(a)(b)(c)"). With
  * `import com.yang_bo.gezi.frontend.Term.*`:
  *
  * {{{
  * λ(x => x)                                  the identity
  * λ(f => λ(x => f(f(x))))                    the numeral two
  * λ(a => λ(b => λ(c => a ∥ b + c)))          λa b c. c + (a ∥ b) in a file
  * }}}
  *
  * Application binds tightest, then `∥`, then `+`, by Scala's precedence of
  * operators, while a lambdalattice file gives `+` and `∥` one precedence. A
  * chain `a + b + c` here is the IR's right-nested choice `a + (b + c)`, its
  * members in their order, which a lambdalattice file writes `c + b + a`
  * (`Lambdalattice`, the paragraph on chains); since Scala cannot tell
  * `(a + b) + c` from it, a choice nested in its left side is written
  * `choice(a, b) + c`.
  *
  * Covariant in the type of the closed terms it holds as constants (`Closed`),
  * as `DeBruijnTermOf` is: a term with none is a [[Term]], one of every
  * configuration.
  */
enum TermOf[+Constant]:

  /** An abstraction: its body as a function of its bound variable, a variable
    * of no constant.
    */
  case Abstraction(body: TermOf[Nothing] => TermOf[Constant])

  /** An application. */
  case Application(function: TermOf[Constant], argument: TermOf[Constant])

  /** A choice written with `+`, which a further `+` extends; converted to the
    * right-nested chain of its members.
    */
  case ChoiceChain(members: Vector[TermOf[Constant]])

  /** A binary choice written with `choice`, which a further `+` takes as one
    * member.
    */
  case Choice(left: TermOf[Constant], right: TermOf[Constant])

  /** The parallel of two sides. */
  case Parallel(left: TermOf[Constant], right: TermOf[Constant])

  /** A closed term the host already holds (a term of a configuration, a pure
    * key), converted as its constant (`DeBruijnTerm.Constant`), as the
    * conversion converts a closed subterm. It is no free variable: it holds a
    * term and nothing else, no name, no string and no look-up, and its term is
    * a closed term obtained by projection from a tree (a member of a file read
    * with `StandardLibrary.entryTerm` and `KnowledgeReading.memberTerm`), never
    * by name. It replaces the library names of the deleted `Define`, a free
    * variable (blacklisted), deleted when the library became files reached by
    * paths.
    */
  case Closed(constant: Constant)

  /** The variable the conversion applies an abstraction's function to: the
    * number of abstractions outside the one that binds it. Only the walks of a
    * whole HOAS term make it: the conversion, and the classic Hindley-Milner
    * reference of the benchmarks (`com.yang_bo.gezi.programfamilies.ClassicHindleyMilner`),
    * which walks the term the same way.
    */
  case BoundVariable(level: Int) extends TermOf[Nothing]

  /** This term applied to the argument. */
  def apply[Wider >: Constant](argument: TermOf[Wider]): TermOf[Wider] =
    Application(this, argument)

  /** The choice of this term and the other; a chain of `+` is one right-nested
    * chain of choices.
    */
  def +[Wider >: Constant](other: TermOf[Wider]): TermOf[Wider] = this match
    case ChoiceChain(members) => ChoiceChain(members :+ other)
    case _                    => ChoiceChain(Vector(this, other))

  /** The parallel of this term and the other. */
  def ∥[Wider >: Constant](other: TermOf[Wider]): TermOf[Wider] =
    Parallel(this, other)

  // TODO: the `definitions` parameter of `deBruijnTerm`, and `locallyNamelessTerm`, resolved the library names of
  // the deleted case Define (a free variable, blacklisted; the table of library files is deleted when the library became
  // files reached by paths). Since Define is gone they no longer resolve
  // anything: both give the same de Bruijn term. They are removed, and their callers converted to one `deBruijnTerm` of no
  // argument, in the commit after the one that adds the HOAS case `Closed(instruction)`.
  // The deleted code: git show 2908bffd5:lambda_jit/frontend/src/main/scala/lambdajit/frontend/Term.scala.

  /** The de Bruijn term: each abstraction's function applied to a variable that
    * carries the abstraction's level, and levels turned into indices. Throws
    * `LambdaError` with `VariableOutsideItsAbstraction` for a variable used
    * outside the abstraction that made it.
    */
  def deBruijnTerm(
      definitions: Map[String, Nothing]
  ): DeBruijnTermOf[Constant] =
    Term.converted(this, 0).result

  /** The locally nameless term (`DeBruijnTerm`): the same term as
    * `deBruijnTerm`. Throws `LambdaError` with `VariableOutsideItsAbstraction`
    * for a variable used outside the abstraction that made it.
    */
  def locallyNamelessTerm: DeBruijnTermOf[Constant] =
    Term.converted(this, 0).result

/** A HOAS term of no constant, one of every configuration. */
type Term = TermOf[Nothing]

/** The constructions of HOAS terms. */
object Term:

  export TermOf.{
    Abstraction,
    Application,
    BoundVariable,
    Choice,
    ChoiceChain,
    Closed,
    Parallel
  }

  /** The abstraction whose body is the function of its variable. */
  def λ[Constant](body: Term => TermOf[Constant]): TermOf[Constant] =
    TermOf.Abstraction(body)

  /** The right-nested choice of the members, which a further `+` takes as one
    * member; one member is itself, and none is `top`: the choice itself is
    * binary and has no empty case, and an encoding that lists no member means
    * the term that stands for no answer.
    */
  def choice[Constant](members: TermOf[Constant]*): TermOf[Constant] =
    if members.isEmpty then top
    else
      com.yang_bo.gezi.ir.ChoiceSpine
        .nested[TermOf[Constant]](members.toVector, TermOf.Choice(_, _))

  /** top = Y (λz. λx. z ∥ x), Y being Curry's fixed point combinator
    * `λf. (λx. f (x x)) (λx. f (x x))`: the term that stands for no answer in
    * place of the empty choice, Lean's `top`
    * (`lean/LambdaJit/ContextualPreorderEmptyChoice.lean`) and the library's
    * file `corpora/library/top.lambdalattice`. It is `λx. top ∥ x` after three
    * beta steps.
    */
  val top: Term =
    λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))(λ(z => λ(x => z ∥ x)))

  /** The closed term held as a constant (`Closed`): a term of a configuration,
    * or a pure key.
    */
  def closed[Constant](constant: Constant): TermOf[Constant] =
    TermOf.Closed(constant)

  /** The HOAS term of a closed de Bruijn term: each abstraction the function of
    * its variable that reads the de Bruijn body under it, each binary choice a
    * `Choice`, each constant `Closed`. Converted back (`deBruijnTerm`), it is
    * the de Bruijn term it was made from. Throws `LambdaError` with `NotClosed`
    * for a term with a free name or a loose variable.
    */
  def ofDeBruijn[Constant](term: DeBruijnTermOf[Constant]): TermOf[Constant] =
    embedded(term, term, Vector.empty)

  private def embedded[Constant](
      whole: DeBruijnTermOf[Constant],
      term: DeBruijnTermOf[Constant],
      bound: Vector[Term]
  ): TermOf[Constant] =
    term match
      case DeBruijnTerm.Variable(index) =>
        bound
          .lift(bound.size - 1 - index)
          .getOrElse(throw LambdaError(LambdaErrorReason.NotClosed(whole)))
      case DeBruijnTerm.Lambda(body) =>
        TermOf.Abstraction(variable => embedded(whole, body, bound :+ variable))
      case DeBruijnTerm.Apply(function, argument) =>
        TermOf.Application(
          embedded(whole, function, bound),
          embedded(whole, argument, bound)
        )
      case DeBruijnTerm.Choice(left, right) =>
        TermOf.Choice(
          embedded(whole, left, bound),
          embedded(whole, right, bound)
        )
      case DeBruijnTerm.Parallel(left, right) =>
        TermOf.Parallel(
          embedded(whole, left, bound),
          embedded(whole, right, bound)
        )
      case DeBruijnTerm.Constant(constant) => TermOf.Closed(constant)
      case _ => throw LambdaError(LambdaErrorReason.NotClosed(whole))

  /** The body of the closed HOAS abstraction given the closed argument, by one
    * β step on its de Bruijn term (`Defunctionalization.instantiatedFrom`): an
    * abstraction's body takes a variable, a term of no constant, so an argument
    * holding constants is substituted on the de Bruijn term and the result read
    * back as HOAS (`ofDeBruijn`). Throws `IllegalArgumentException` for a term
    * that is no abstraction.
    */
  def instantiated[Constant](
      abstraction: TermOf[Constant],
      argument: TermOf[Constant]
  ): TermOf[Constant] =
    abstraction.deBruijnTerm(Map.empty) match
      case DeBruijnTerm.Lambda(body) =>
        ofDeBruijn(
          Defunctionalization
            .instantiatedFrom(body, 0, argument.deBruijnTerm(Map.empty))
            .result
        )
      case other =>
        throw IllegalArgumentException(s"no abstraction to instantiate: $other")

  /** The de Bruijn term of the HOAS term under `depth` abstractions. */
  private[frontend] def converted[Constant](
      term: TermOf[Constant],
      depth: Int
  ): TailRec[DeBruijnTermOf[Constant]] = term match
    case Abstraction(body) =>
      tailcall(converted(body(BoundVariable(depth)), depth + 1))
        .map(DeBruijnTerm.Lambda(_))
    case Application(function, argument) =>
      for
        functionTerm <- tailcall(converted(function, depth))
        argumentTerm <- tailcall(converted(argument, depth))
      yield DeBruijnTerm.Apply(functionTerm, argumentTerm)
    case ChoiceChain(members) =>
      Trampoline
        .traversed(members)(converted(_, depth))
        .map(DeBruijnTerm.nestedChoice)
    case Choice(left, right) =>
      for
        leftTerm <- tailcall(converted(left, depth))
        rightTerm <- tailcall(converted(right, depth))
      yield DeBruijnTerm.Choice(leftTerm, rightTerm)
    case Parallel(left, right) =>
      for
        leftTerm <- tailcall(converted(left, depth))
        rightTerm <- tailcall(converted(right, depth))
      yield DeBruijnTerm.Parallel(leftTerm, rightTerm)
    case Closed(constant)     => done(DeBruijnTerm.Constant(constant))
    case BoundVariable(level) =>
      if level < 0 || level >= depth then
        throw LambdaError(
          LambdaErrorReason.VariableOutsideItsAbstraction(level, depth)
        )
      else done(DeBruijnTerm.Variable(depth - level - 1))
