package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.frontend.DeBruijnTerm
import scala.annotation.tailrec
import com.yang_bo.gezi.weakhead.Trampoline.done

/** The port of `gezi/tests/reference.pl`'s reference evaluator and normaliser,
  * written independently of the IR: the cross-checks of the weak-head evaluator
  * and of the normal-form reader.
  *
  * THE REFERENCE EVALUATOR is classical weak head reduction on closed de Bruijn
  * terms, by substitution. THE REFERENCE NORMALISER is classical leftmost
  * outermost beta reduction to the beta normal form, by substitution with
  * shifting, followed by eta contraction bottom up.
  *
  * Both are bounded by a budget of steps (`Budget`), where the Prolog ones were
  * bounded by SWI-Prolog's inferences: a STEP here is one call of a reduction
  * (a weak head, a beta normal form, a spine) or one node visited by a
  * substitution or a shift, the work an inference of the Prolog clauses counts.
  */
object Reference:

  private type Stepped[Result] = Computation[Budget, Result]

  private val stepTaken: Stepped[Unit] =
    Computation(budget =>
      done(budget.charged match
        case Some(charged) => Computed.Done((), charged)
        case None          => Computed.Stopped(budget))
    )

  /** The weak head of the pure closed term within the limit, or `Exceeded` when
    * the limit is reached.
    */
  def weakHeadWithin(term: DeBruijnTerm, limit: Long): Bounded[DeBruijnTerm] =
    weakHead(term).result(Budget.of(limit)) match
      case Computed.Done(head, _) => Bounded.Finished(head)
      case Computed.Stopped(_)    => Bounded.Exceeded

  /** The βη normal form of the pure closed term within the limit, or `Exceeded`
    * when the limit is reached.
    */
  def normalFormWithin(term: DeBruijnTerm, limit: Long): Bounded[DeBruijnTerm] =
    betaNormal(term).map(etaContracted).result(Budget.of(limit)) match
      case Computed.Done(normalForm, _) => Bounded.Finished(normalForm)
      case Computed.Stopped(_)          => Bounded.Exceeded

  private def weakHead(term: DeBruijnTerm): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      term match
        case DeBruijnTerm.Lambda(_)                 => Computation.pure(term)
        case DeBruijnTerm.Apply(function, argument) =>
          weakHead(function).flatMap {
            case DeBruijnTerm.Lambda(body) =>
              substituted(body, 0, argument).flatMap(weakHead)
            case other =>
              throw IllegalArgumentException(
                s"a closed term's weak head is a lambda, not $other"
              )
          }
        case other =>
          throw IllegalArgumentException(
            s"the reference evaluates closed pure terms, not $other"
          )
    )

  /** The body with the variable of the depth replaced by the closed argument,
    * which needs no shift.
    */
  private def substituted(
      term: DeBruijnTerm,
      depth: Int,
      argument: DeBruijnTerm
  ): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      term match
        case DeBruijnTerm.Variable(index) =>
          Computation.pure(if index == depth then argument else term)
        case DeBruijnTerm.Lambda(body) =>
          substituted(body, depth + 1, argument).map(DeBruijnTerm.Lambda(_))
        case DeBruijnTerm.Apply(function, functionArgument) =>
          for
            functionResult <- substituted(function, depth, argument)
            argumentResult <- substituted(functionArgument, depth, argument)
          yield DeBruijnTerm.Apply(functionResult, argumentResult)
        case other =>
          throw IllegalArgumentException(
            s"the reference substitutes in pure terms, not $other"
          )
    )

  /** The beta normal form of an open term, by its head first. */
  private def betaNormal(term: DeBruijnTerm): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      openWeakHead(term).flatMap {
        case DeBruijnTerm.Lambda(body) =>
          betaNormal(body).map(DeBruijnTerm.Lambda(_))
        case spine => spineNormal(spine)
      }
    )

  /** The weak head of an open term, an abstraction or a variable applied to
    * arguments.
    */
  private def openWeakHead(term: DeBruijnTerm): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      term match
        case DeBruijnTerm.Variable(_) | DeBruijnTerm.Lambda(_) =>
          Computation.pure(term)
        case DeBruijnTerm.Apply(function, argument) =>
          openWeakHead(function).flatMap {
            case DeBruijnTerm.Lambda(body) =>
              openSubstituted(body, 0, argument).flatMap(openWeakHead)
            case functionHead =>
              Computation.pure(DeBruijnTerm.Apply(functionHead, argument))
          }
        case other =>
          throw IllegalArgumentException(
            s"the reference normalises pure terms, not $other"
          )
    )

  /** A variable applied to arguments, each argument normalised. */
  private def spineNormal(spine: DeBruijnTerm): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      spine match
        case DeBruijnTerm.Variable(_)               => Computation.pure(spine)
        case DeBruijnTerm.Apply(function, argument) =>
          for
            functionNormal <- spineNormal(function)
            argumentNormal <- betaNormal(argument)
          yield DeBruijnTerm.Apply(functionNormal, argumentNormal)
        case other => throw IllegalArgumentException(s"a spine is no $other")
    )

  /** The body with variable `depth` replaced by the argument lifted under the
    * binders, and every other free variable above it one lower.
    */
  private def openSubstituted(
      term: DeBruijnTerm,
      depth: Int,
      argument: DeBruijnTerm
  ): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      term match
        case DeBruijnTerm.Variable(index) =>
          if index == depth then lifted(argument, 0, depth)
          else if index > depth then
            Computation.pure(DeBruijnTerm.Variable(index - 1))
          else Computation.pure(term)
        case DeBruijnTerm.Lambda(body) =>
          openSubstituted(body, depth + 1, argument).map(DeBruijnTerm.Lambda(_))
        case DeBruijnTerm.Apply(function, functionArgument) =>
          for
            functionResult <- openSubstituted(function, depth, argument)
            argumentResult <- openSubstituted(functionArgument, depth, argument)
          yield DeBruijnTerm.Apply(functionResult, argumentResult)
        case other =>
          throw IllegalArgumentException(
            s"the reference substitutes in pure terms, not $other"
          )
    )

  /** Every free variable of the term at or above the cutoff the amount higher.
    */
  private def lifted(
      term: DeBruijnTerm,
      cutoff: Int,
      amount: Int
  ): Stepped[DeBruijnTerm] =
    stepTaken.flatMap(_ =>
      term match
        case DeBruijnTerm.Variable(index) =>
          Computation.pure(if index >= cutoff then
            DeBruijnTerm.Variable(index + amount)
          else term)
        case DeBruijnTerm.Lambda(body) =>
          lifted(body, cutoff + 1, amount).map(DeBruijnTerm.Lambda(_))
        case DeBruijnTerm.Apply(function, argument) =>
          for
            functionLifted <- lifted(function, cutoff, amount)
            argumentLifted <- lifted(argument, cutoff, amount)
          yield DeBruijnTerm.Apply(functionLifted, argumentLifted)
        case other =>
          throw IllegalArgumentException(
            s"the reference lifts pure terms, not $other"
          )
    )

  /** Every eta redex of a beta normal term contracted, bottom up. The terms are
    * the normal forms of terms the budget let normalise, small enough for the
    * JVM stack.
    */
  private def etaContracted(term: DeBruijnTerm): DeBruijnTerm = term match
    case DeBruijnTerm.Variable(_)               => term
    case DeBruijnTerm.Apply(function, argument) =>
      DeBruijnTerm.Apply(etaContracted(function), etaContracted(argument))
    case DeBruijnTerm.Lambda(body) =>
      etaContracted(body) match
        case DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(0))
            if !occursFree(function, 0) =>
          shiftedDown(function, 0)
        case contracted => DeBruijnTerm.Lambda(contracted)
    case other =>
      throw IllegalArgumentException(
        s"the reference contracts pure terms, not $other"
      )

  private def shiftedDown(term: DeBruijnTerm, cutoff: Int): DeBruijnTerm =
    term match
      case DeBruijnTerm.Variable(index) =>
        if index >= cutoff then DeBruijnTerm.Variable(index - 1) else term
      case DeBruijnTerm.Lambda(body) =>
        DeBruijnTerm.Lambda(shiftedDown(body, cutoff + 1))
      case DeBruijnTerm.Apply(function, argument) =>
        DeBruijnTerm.Apply(
          shiftedDown(function, cutoff),
          shiftedDown(argument, cutoff)
        )
      case other =>
        throw IllegalArgumentException(
          s"the reference shifts pure terms, not $other"
        )

  /** The variable of the index occurs free in the term. */
  def occursFree(term: DeBruijnTerm, index: Int): Boolean = occursFreeIn(
    List((term, index))
  )

  @tailrec
  private def occursFreeIn(pending: List[(DeBruijnTerm, Int)]): Boolean =
    pending match
      case Nil                                           => false
      case (DeBruijnTerm.Variable(found), index) :: rest =>
        found == index || occursFreeIn(rest)
      case (DeBruijnTerm.Lambda(body), index) :: rest =>
        occursFreeIn((body, index + 1) :: rest)
      case (DeBruijnTerm.Apply(function, argument), index) :: rest =>
        occursFreeIn((function, index) :: (argument, index) :: rest)
      case _ :: rest => occursFreeIn(rest)
