package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.contest.corpora.claims
import com.yang_bo.gezi.frontend.Term

/** One corpus file's claim facts (`ClaimFact`) as the clauses it adds to the
  * tables of `contest_hard_answers` and `contest_hard_claims`
  * (`claims.HardFamily`), its points built by `program`: the hooks of the merge
  * and mixin families and of the empty-set reachability, read by the claims
  * group's `HardAnswers` and `HardClaims`.
  */
final class ClaimFactFamily(
    facts: Vector[ClaimFact],
    program: String => ProblemTerm
) extends claims.HardFamily:

  def points: Map[String, () => ProblemTerm] =
    facts
      .map(fact => fact.point)
      .distinct
      .map(point => point -> (() => program(point)))
      .toMap

  def intended: Vector[(String, claims.Intended)] =
    facts.collect { case ClaimFact.HardIntended(point, outcome, value) =>
      point -> claims.Intended(outcome, value)
    }

  def unreadFiniteHeads: Vector[(String, String)] = Vector.empty

  def cycles: Vector[(String, String, String)] = Vector.empty

  def cycleClaims: Vector[claims.CycleClaim] = Vector.empty

  override def scoredFiniteHeads: Vector[(String, Vector[claims.Template])] =
    facts.collect { case ClaimFact.ScoredFiniteHead(point, templates, _) =>
      point -> templates
    }

  override def noYieldTraps: Vector[(String, Vector[claims.Template])] =
    facts.collect { case ClaimFact.NoYieldTrap(point, templates, _) =>
      point -> templates
    }
