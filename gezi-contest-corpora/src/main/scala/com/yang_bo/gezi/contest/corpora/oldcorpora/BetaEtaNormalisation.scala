package com.yang_bo.gezi.contest.corpora.oldcorpora

import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.DeBruijnTerm.Apply
import com.yang_bo.gezi.frontend.DeBruijnTerm.Choice
import com.yang_bo.gezi.frontend.DeBruijnTerm.Lambda
import com.yang_bo.gezi.frontend.DeBruijnTerm.Parallel
import com.yang_bo.gezi.frontend.DeBruijnTerm.Variable
import com.yang_bo.gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The beta eta normal form of a de Bruijn term, the port of
  * `gezi/prolog/gezi/old_corpora/beta_eta_normalisation.pl`: the normaliser
  * that computed the attractors' normal forms
  * (`problems/attractor_normal_forms`), kept for the problem corpora's tests
  * only: the pipeline, which works on the IR, needs no beta eta normalisation
  * on de Bruijn trees, and only legacy problem-corpus tests use it; the
  * pipeline (the library, the strategies, the compilation) must not.
  *
  * Leftmost outermost beta reduction by substitution with shifting, bounded by
  * FUEL, a count of beta contractions (the same count as the Prolog's, which is
  * no SWI-Prolog inference count), followed by eta contraction bottom up. A
  * choice is inert under beta, its members normalised one by one and kept
  * without repetition in a fixed order; a parallel is an inert constructor
  * whose sides are normalised in place. A constant has no normal form here and
  * throws.
  *
  * The order of a choice's members: the Prolog sorted them in the standard
  * order of terms; here they are sorted by their text (`toString`), another
  * fixed order, so that a choice's normal form does not depend on the order or
  * the repetitions its spelling lists its members in, as in the Prolog. The
  * members of a choice are those of its right `+` spine
  * (`DeBruijnTerm.choiceMembers`), and a normalised choice is nested to the
  * right again (`DeBruijnTerm.nestedChoice`), so that the binary choice
  * normalises as the member list did.
  */
object BetaEtaNormalisation:

  /** A choice read as the members of its right spine. */
  private object Members:
    def unapply(term: DeBruijnTerm): Option[Vector[DeBruijnTerm]] = term match
      case Choice(_, _) => Some(DeBruijnTerm.choiceMembers(term))
      case _            => None

  /** The members, at least one, nested to the right. */
  private def chain(members: Vector[DeBruijnTerm]): DeBruijnTerm =
    DeBruijnTerm.nestedChoice(members)

  /** `normalised(Term, Fuel, NormalForm)`: the beta eta normal form, or none
    * when the beta reduction needs more than `fuel` contractions.
    */
  def normalised(term: DeBruijnTerm, fuel: Long): Option[DeBruijnTerm] =
    betaNormalised(term, fuel).result.map((normal, _) =>
      etaContracted(normal).result
    )

  /** `beta_eta_normal(Term)`: no beta redex and no eta redex, and every
    * choice's members distinct and in order.
    */
  def betaEtaNormal(term: DeBruijnTerm): Boolean = term match
    case Variable(_)               => true
    case Apply(function, argument) =>
      (function match
        case Lambda(_) => false
        case _         => true
      ) && betaEtaNormal(function) && betaEtaNormal(argument)
    case Members(members) =>
      members == ordered(members) && members.forall(betaEtaNormal)
    case Parallel(left, right) => betaEtaNormal(left) && betaEtaNormal(right)
    case Lambda(body)          => !etaRedex(body) && betaEtaNormal(body)
    case other                 =>
      throw IllegalArgumentException(s"no normal form of $other here")

  private def ordered(members: Vector[DeBruijnTerm]): Vector[DeBruijnTerm] =
    members.distinct.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering)

  private def etaRedex(body: DeBruijnTerm): Boolean = body match
    case Apply(function, Variable(0)) => !occursFree(function, 0)
    case _                            => false

  private type Fuelled = TailRec[Option[(DeBruijnTerm, Long)]]

  private def betaNormalised(term: DeBruijnTerm, fuel: Long): Fuelled =
    term match
      case Variable(_)  => done(Some((term, fuel)))
      case Lambda(body) =>
        tailcall(betaNormalised(body, fuel)).map(
          _.map((normal, left) => (Lambda(normal), left))
        )
      case Members(members) =>
        membersNormalised(members, 0, fuel, Vector.empty).map(
          _.map((normals, left) => (chain(ordered(normals)), left))
        )
      case Parallel(left, right) =>
        tailcall(betaNormalised(left, fuel)).flatMap {
          case None                       => done(None)
          case Some((leftNormal, middle)) =>
            tailcall(betaNormalised(right, middle)).map(
              _.map((rightNormal, rest) =>
                (Parallel(leftNormal, rightNormal), rest)
              )
            )
        }
      case Apply(_, _) =>
        tailcall(headReduced(term, fuel)).flatMap {
          case None                                      => done(None)
          case Some((Apply(function, argument), middle)) =>
            tailcall(betaNormalised(function, middle)).flatMap {
              case None                          => done(None)
              case Some((normalFunction, inner)) =>
                tailcall(betaNormalised(argument, inner)).map(
                  _.map((normalArgument, rest) =>
                    (Apply(normalFunction, normalArgument), rest)
                  )
                )
            }
          case Some((head, middle)) => tailcall(betaNormalised(head, middle))
        }
      case other =>
        throw IllegalArgumentException(s"no normal form of $other here")

  private def membersNormalised(
      members: Vector[DeBruijnTerm],
      index: Int,
      fuel: Long,
      normals: Vector[DeBruijnTerm]
  ): TailRec[Option[(Vector[DeBruijnTerm], Long)]] =
    if index >= members.size then done(Some((normals, fuel)))
    else
      tailcall(betaNormalised(members(index), fuel)).flatMap {
        case None                   => done(None)
        case Some((normal, middle)) =>
          tailcall(
            membersNormalised(members, index + 1, middle, normals :+ normal)
          )
      }

  /** `head_reduced/4`: the term with its head redexes contracted, a lambda or
    * an application whose function is no lambda; none when the fuel runs out.
    */
  private def headReduced(term: DeBruijnTerm, fuel: Long): Fuelled = term match
    case Apply(function, argument) =>
      tailcall(headReduced(function, fuel)).flatMap {
        case None                         => done(None)
        case Some((Lambda(body), middle)) =>
          if middle > 0 then
            tailcall(
              headReduced(substituted(body, 0, argument).result, middle - 1)
            )
          else done(None)
        case Some((functionHead, middle)) =>
          done(Some((Apply(functionHead, argument), middle)))
      }
    case _ => done(Some((term, fuel)))

  private def substituted(
      term: DeBruijnTerm,
      depth: Int,
      argument: DeBruijnTerm
  ): TailRec[DeBruijnTerm] = term match
    case Variable(index) =>
      if index == depth then shifted(argument, 0, depth)
      else if index > depth then done(Variable(index - 1))
      else done(term)
    case Lambda(body) =>
      tailcall(substituted(body, depth + 1, argument)).map(Lambda(_))
    case Apply(function, operand) =>
      for
        newFunction <- tailcall(substituted(function, depth, argument))
        newOperand <- tailcall(substituted(operand, depth, argument))
      yield Apply(newFunction, newOperand)
    case Members(members) =>
      mapped(members, substituted(_, depth, argument)).map(chain)
    case Parallel(left, right) =>
      for
        newLeft <- tailcall(substituted(left, depth, argument))
        newRight <- tailcall(substituted(right, depth, argument))
      yield Parallel(newLeft, newRight)
    case other =>
      throw IllegalArgumentException(s"no normal form of $other here")

  private def shifted(
      term: DeBruijnTerm,
      cutoff: Int,
      amount: Int
  ): TailRec[DeBruijnTerm] = term match
    case Variable(index) =>
      done(if index >= cutoff then Variable(index + amount) else term)
    case Lambda(body) =>
      tailcall(shifted(body, cutoff + 1, amount)).map(Lambda(_))
    case Apply(function, argument) =>
      for
        newFunction <- tailcall(shifted(function, cutoff, amount))
        newArgument <- tailcall(shifted(argument, cutoff, amount))
      yield Apply(newFunction, newArgument)
    case Members(members) =>
      mapped(members, shifted(_, cutoff, amount)).map(chain)
    case Parallel(left, right) =>
      for
        newLeft <- tailcall(shifted(left, cutoff, amount))
        newRight <- tailcall(shifted(right, cutoff, amount))
      yield Parallel(newLeft, newRight)
    case other =>
      throw IllegalArgumentException(s"no normal form of $other here")

  private def mapped(
      members: Vector[DeBruijnTerm],
      step: DeBruijnTerm => TailRec[DeBruijnTerm]
  ): TailRec[Vector[DeBruijnTerm]] =
    TailRecFolds.folded(members, Vector.empty[DeBruijnTerm])((before, member) =>
      step(member).map(before :+ _)
    )

  /** `eta_contracted/2`, bottom up. */
  private def etaContracted(term: DeBruijnTerm): TailRec[DeBruijnTerm] =
    term match
      case Variable(_)               => done(term)
      case Apply(function, argument) =>
        for
          newFunction <- tailcall(etaContracted(function))
          newArgument <- tailcall(etaContracted(argument))
        yield Apply(newFunction, newArgument)
      case Members(members) =>
        mapped(members, etaContracted).map(contracted =>
          chain(ordered(contracted))
        )
      case Parallel(left, right) =>
        for
          newLeft <- tailcall(etaContracted(left))
          newRight <- tailcall(etaContracted(right))
        yield Parallel(newLeft, newRight)
      case Lambda(body) =>
        tailcall(etaContracted(body)).map {
          case Apply(function, Variable(0)) if !occursFree(function, 0) =>
            shiftedDown(function, 0)
          case contracted => Lambda(contracted)
        }
      case other =>
        throw IllegalArgumentException(s"no normal form of $other here")

  private def shiftedDown(term: DeBruijnTerm, cutoff: Int): DeBruijnTerm =
    term match
      case Variable(index) =>
        if index > cutoff then Variable(index - 1) else term
      case Lambda(body)              => Lambda(shiftedDown(body, cutoff + 1))
      case Apply(function, argument) =>
        Apply(shiftedDown(function, cutoff), shiftedDown(argument, cutoff))
      case Members(members)      => chain(members.map(shiftedDown(_, cutoff)))
      case Parallel(left, right) =>
        Parallel(shiftedDown(left, cutoff), shiftedDown(right, cutoff))
      case other =>
        throw IllegalArgumentException(s"no normal form of $other here")

  /** `occurs_free(Term, Index)`. */
  def occursFree(term: DeBruijnTerm, index: Int): Boolean = term match
    case Variable(found)           => found == index
    case Apply(function, argument) =>
      occursFree(function, index) || occursFree(argument, index)
    case Members(members)      => members.exists(occursFree(_, index))
    case Parallel(left, right) =>
      occursFree(left, index) || occursFree(right, index)
    case Lambda(body) => occursFree(body, index + 1)
    case _            => false
