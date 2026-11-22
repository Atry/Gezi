package gezi.contest.corpora.common

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** Closed de Bruijn terms back in the front end's HOAS, for the generators
  * that read a term written as data (`variable/1`, `lambda/1`, `apply/2`, a
  * choice and a parallel) and build programs around it: the attractors'
  * normal forms and their respellings, and the reduction group's templates.
  * The translation is trampolined, so a deep term takes no JVM stack.
  */
object DeBruijnTerms:

  /** The HOAS term of a closed de Bruijn term holding no constant and no
    * free name. Throws for a variable no binder binds, for a constant, a
    * library name the corpora's generators never hold, and for a free name.
    */
  def hoas(term: DeBruijnTerm): Term =
    hoas(
      term,
      name => throw IllegalArgumentException(s"a free name ($name) has no HOAS term in the problem corpora")
    )

  /** The HOAS term of a locally nameless term, each free name replaced by
    * the term the function gives for it (`hoas` of a term alone gives none
    * and throws). Throws for a variable no binder binds and for a constant.
    */
  def hoas(term: DeBruijnTerm, freeName: String => Term): Term = converted(term, List.empty, freeName).result

  /** The HOAS term of a closed de Bruijn term `λx1. … λxn. Body`, n the
    * number of the arguments: Body with each xi the i-th argument, as a
    * template read from a problem file (`ProblemData.program`) is
    * instantiated. Throws when the term has fewer than n leading
    * abstractions, and as `hoas` does.
    */
  def instantiated(term: DeBruijnTerm, arguments: Vector[Term]): Term =
    @scala.annotation.tailrec
    def opened(rest: DeBruijnTerm, remaining: Vector[Term], environment: List[Term]): (DeBruijnTerm, List[Term]) =
      remaining match
        case argument +: others =>
          rest match
            case DeBruijnTerm.Lambda(body) => opened(body, others, argument :: environment)
            case other =>
              throw IllegalArgumentException(s"a template has fewer abstractions than its ${arguments.size} arguments: $other")
        case _ => (rest, environment)
    val (body, environment) = opened(term, arguments, List.empty)
    converted(
      body,
      environment,
      name => throw IllegalArgumentException(s"a free name ($name) has no HOAS term in the problem corpora")
    ).result

  private def converted(term: DeBruijnTerm, environment: List[Term], freeName: String => Term): TailRec[Term] =
    term match
      case DeBruijnTerm.Variable(index) =>
        environment.lift(index) match
          case Some(bound) => done(bound)
          case None        => throw IllegalArgumentException(s"the de Bruijn term is not closed: variable $index")
      case DeBruijnTerm.Lambda(body) =>
        done(λ(variable => converted(body, variable :: environment, freeName).result))
      case DeBruijnTerm.Apply(function, argument) =>
        for
          functionTerm <- tailcall(converted(function, environment, freeName))
          argumentTerm <- tailcall(converted(argument, environment, freeName))
        yield functionTerm(argumentTerm)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          leftTerm <- tailcall(converted(left, environment, freeName))
          rightTerm <- tailcall(converted(right, environment, freeName))
        yield leftTerm ∥ rightTerm
      case DeBruijnTerm.Choice(left, right) =>
        for
          leftTerm <- tailcall(converted(left, environment, freeName))
          rightTerm <- tailcall(converted(right, environment, freeName))
        yield choice(leftTerm, rightTerm)
      case DeBruijnTerm.Constant(instruction) =>
        throw IllegalArgumentException(s"a constant ($instruction) has no HOAS term in the problem corpora")
      case DeBruijnTerm.Free(name) => done(freeName(name))
