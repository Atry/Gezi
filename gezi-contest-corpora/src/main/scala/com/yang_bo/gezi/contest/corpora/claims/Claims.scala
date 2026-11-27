package com.yang_bo.gezi.contest.corpora.claims

import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies
import java.nio.file.Path

/** The claims group's generators over the files of `gezi/corpora` under `root`
  * (the directory `gezi`), each made once, and the tables of
  * `contest_hard_answers` and `contest_hard_claims` over the group's families
  * and the other groups' (`otherGroups`, the files of the merge and reduction
  * groups that add clauses to those tables, gathered by `common.HardCorpus`;
  * none when only the group's own files are read).
  */
final class Claims(
    root: Path,
    problems: ProblemFamilies,
    otherGroups: Vector[HardFamily]
):

  val corpora: Corpora = Corpora(root, problems)

  val clauses: HardClauses = HardClauses(corpora)

  val hard: Hard = Hard(corpora, clauses)

  /** The hidden families, by the name of their file. */
  val families: Vector[(String, HardFamily)] = Vector(
    "contest_api_capture_traps" -> ApiCaptureTraps(corpora),
    "contest_api_domain_traps" -> ApiDomainTraps(corpora),
    "contest_leading_zero_traps" -> LeadingZeroTraps(corpora),
    "contest_certificate_cycles" -> CertificateCycles(corpora, clauses),
    "contest_continuation_cycles" -> ContinuationCycles(corpora),
    "contest_respelled_cycles" -> RespelledCycles(corpora),
    "contest_arithmetic_theorems" -> ArithmeticTheorems(corpora),
    "contest_infinite_members" -> InfiniteMembers(corpora),
    "contest_easy_terms" -> EasyTerms(corpora),
    "contest_adder_tautologies" -> AdderTautologies(corpora),
    "contest_tautology_circuits" -> TautologyCircuits(corpora)
  )

  /** Every point of the group's files in `contest_hard`, by name. */
  val points: Map[String, () => ProblemTerm] =
    hard.points ++ clauses.points ++ families.flatMap(_._2.points)

  private val allFamilies: Vector[HardFamily] =
    families.map(_._2) ++ otherGroups

  val answers: HardAnswers = HardAnswers(corpora, allFamilies)

  /** The claims of every point of `contest_hard`, the group's and the other
    * groups'.
    */
  val claims: HardClaims = HardClaims(
    corpora,
    answers,
    allFamilies,
    points ++ otherGroups.flatMap(_.points)
  )

  val attractors: Attractors = Attractors(corpora)

  val qualifying: Qualifying = Qualifying(corpora, clauses)

  val contestAnswers: ContestAnswers =
    ContestAnswers(corpora, clauses.certificates)
