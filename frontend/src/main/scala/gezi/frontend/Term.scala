package gezi.frontend

import gezi.ir.Instruction
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** An object term written in Scala, in higher-order abstract syntax (the
  * user, 2026-10-31: "If you want to support Scala code to write the object
  * language, just use HOAS. Use unicode for the choice and parallel
  * operator, use unary `def apply` for application, so curried call becomes
  * f(a)(b)(c)"). With `import gezi.frontend.Term.*`:
  *
  * {{{
  * λ(x => x)                                  the identity
  * λ(f => λ(x => f(f(x))))                    the numeral two
  * λ(a => λ(b => λ(c => a ∥ b + c)))          λa b c. c + (a ∥ b) in a file
  * }}}
  *
  * Application binds tightest, then `∥`, then `+`, by Scala's precedence of
  * operators, while a lambdalattice file gives `+` and `∥` one precedence.
  * A chain `a + b + c` here is the IR's right-nested choice `a + (b + c)`,
  * its members in their order, which a lambdalattice file writes `c + b + a`
  * (`Lambdalattice`, the paragraph on chains); since Scala cannot tell
  * `(a + b) + c` from it, a choice nested in its left side is written
  * `choice(a, b) + c`.
  */
enum Term:

  /** An abstraction: its body as a function of its bound variable. */
  case Abstraction(body: Term => Term)

  /** An application. */
  case Application(function: Term, argument: Term)

  /** A choice written with `+`, which a further `+` extends; converted to the
    * right-nested chain of its members.
    */
  case ChoiceChain(members: Vector[Term])

  /** A binary choice written with `choice`, which a further `+` takes as one
    * member.
    */
  case Choice(left: Term, right: Term)

  /** The parallel of two sides. */
  case Parallel(left: Term, right: Term)

  /** A closed term the host already holds as an instruction, converted as
    * the constant of its instruction (`DeBruijnTerm.Constant`), as the conversion
    * converts a closed subterm. It is no free variable: it holds an
    * instruction and nothing else, no name, no string and no look-up, and its
    * instruction is a closed term obtained by projection from a tree (a
    * member of a file read with `StandardLibrary.entryTerm` and
    * `KnowledgeReading.memberTerm`), never by name. It replaces the library
    * names of the deleted `Define`, a free variable (blacklisted), deleted
    * when the library became files reached by paths.
    */
  case Closed(instruction: Instruction)

  /** The variable the conversion applies an abstraction's function to: the
    * number of abstractions outside the one that binds it. Only the walks
    * of a whole HOAS term make it: the conversion, and the classic
    * Hindley-Milner reference of the benchmarks
    * (`gezi.programfamilies.ClassicHindleyMilner`), which walks the term the
    * same way.
    */
  case BoundVariable(level: Int)

  /** This term applied to the argument. */
  def apply(argument: Term): Term = Application(this, argument)

  /** The choice of this term and the other; a chain of `+` is one
    * right-nested chain of choices.
    */
  def +(other: Term): Term = this match
    case ChoiceChain(members) => ChoiceChain(members :+ other)
    case _                    => ChoiceChain(Vector(this, other))

  /** The parallel of this term and the other. */
  def ∥(other: Term): Term = Parallel(this, other)

  // TODO: the `definitions` parameter of `deBruijnTerm`, and `locallyNamelessTerm`, resolved the library names of
  // the deleted case Define (a free variable, blacklisted; the table of library files is deleted when the library became
  // files reached by paths). Since Define is gone they no longer resolve
  // anything: both give the same de Bruijn term. They are removed, and their callers converted to one `deBruijnTerm` of no
  // argument, in the commit after the one that adds the HOAS case `Closed(instruction)`.
  // The deleted code: git show 2908bffd5:lambda_jit/frontend/src/main/scala/lambdajit/frontend/Term.scala.

  /** The de Bruijn term: each abstraction's function applied to a variable
    * that carries the abstraction's level, and levels turned into indices.
    * Throws `LambdaError` with `VariableOutsideItsAbstraction` for a variable
    * used outside the abstraction that made it.
    */
  def deBruijnTerm(definitions: Map[String, Instruction]): DeBruijnTerm =
    Term.converted(this, 0).result

  /** The locally nameless term (`DeBruijnTerm`): the same term as
    * `deBruijnTerm`. Throws `LambdaError` with `VariableOutsideItsAbstraction`
    * for a variable used outside the abstraction that made it.
    */
  def locallyNamelessTerm: DeBruijnTerm =
    Term.converted(this, 0).result

/** The constructions of HOAS terms. */
object Term:

  /** The abstraction whose body is the function of its variable. */
  def λ(body: Term => Term): Term = Abstraction(body)

  /** The right-nested choice of the members, which a further `+` takes as
    * one member; one member is itself, and none is `top`: the choice itself is
    * binary and has no empty case, and an encoding that lists no member
    * means the term that stands for no answer.
    */
  def choice(members: Term*): Term =
    if members.isEmpty then top
    else gezi.ir.ChoiceSpine.nested[Term](members.toVector, Choice(_, _))

  /** top = Y (λz. λx. z ∥ x), Y being Curry's fixed point combinator
    * `λf. (λx. f (x x)) (λx. f (x x))`: the term that stands for no answer
    * in place of the empty choice, Lean's `top`
    * (`lean/LambdaJit/ContextualPreorderEmptyChoice.lean`) and the library's
    * file `corpora/library/top.lambdalattice`. It is `λx. top ∥ x` after three
    * beta steps.
    */
  val top: Term = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))(λ(z => λ(x => z ∥ x)))

  /** The closed term of the instruction (`Closed`). */
  def closed(instruction: Instruction): Term = Closed(instruction)

  /** The de Bruijn term of the HOAS term under `depth` abstractions. */
  private def converted(
      term: Term,
      depth: Int
  ): TailRec[DeBruijnTerm] = term match
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
    case Closed(instruction) => done(DeBruijnTerm.Constant(instruction))
    case BoundVariable(level) =>
      if level < 0 || level >= depth then
        throw LambdaError(
          LambdaErrorReason.VariableOutsideItsAbstraction(level, depth)
        )
      else done(DeBruijnTerm.Variable(depth - level - 1))
