package com.yang_bo.gezi.contest.corpora.claims

import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies
import com.yang_bo.gezi.contest.corpora.common.ProblemFamily

import com.yang_bo.gezi.contest.corpora.merges
import java.nio.file.Path

/** The problem families of `gezi/problems` whose tables the claims group's
  * generators read, each read once, when first used. `root` is the directory
  * `gezi`.
  */
final class Corpora(root: Path, problems: ProblemFamilies):

  /** The directory `gezi`. */
  def lambdaJit: Path = root

  /** The prelude, `prelude_clauses.pl`, the merge group's port. */
  lazy val prelude: merges.Prelude = merges.Prelude(problems)

  /** The contest corpus, `problems/clauses`, the merge group's port. */
  lazy val contest: merges.Contest = merges.Contest(problems, prelude)

  /** The long runs, `long_runs_clauses.pl`, the merge group's port. */
  lazy val longRuns: merges.LongRuns = merges.LongRuns(prelude)

  /** The JIT witnesses, `jit_witnesses_clauses.pl`, the merge group's port,
    * over `case_two_clauses.pl`, whose judges one of its points calls.
    */
  lazy val jitWitnesses: merges.JitWitnesses =
    merges.JitWitnesses(prelude, merges.CaseTwo(problems, prelude))

  /** The binary arithmetic of `problems/merge_dynamic`, the merge group's port.
    */
  lazy val mergeDynamic: merges.MergeDynamic = merges.MergeDynamic(problems)

  /** The connectives of the deleted Prolog file (`git show
    * 6ab16a338^:lambda_jit/corpora/contest_tautology.pl`) over the prelude.
    */
  lazy val tautology: Tautology = Tautology(prelude)

  lazy val contestClauses: ProblemFamily = problems("clauses")
  lazy val contestHardClauses: ProblemFamily = problems("hard_clauses")
  lazy val contestHardClaims: ProblemFamily = problems("hard_claims")
  lazy val contestHardAnswers: ProblemFamily = problems("hard_answers")
  lazy val contestHardParameters: ProblemFamily = problems("hard_parameters")
  lazy val contestContinuationCycles: ProblemFamily = problems(
    "continuation_cycles"
  )
  lazy val contestRespelledCycles: ProblemFamily = problems("respelled_cycles")
  lazy val contestCertificateCycles: ProblemFamily = problems(
    "certificate_cycles"
  )
  lazy val contestEasyTerms: ProblemFamily = problems("easy_terms")
  lazy val contestArithmeticTheorems: ProblemFamily = problems(
    "arithmetic_theorems"
  )
  lazy val contestInfiniteMembers: ProblemFamily = problems("infinite_members")
  lazy val contestApiCaptureTraps: ProblemFamily = problems("api_capture_traps")
  lazy val contestApiDomainTraps: ProblemFamily = problems("api_domain_traps")
  lazy val contestLeadingZeroTraps: ProblemFamily = problems(
    "leading_zero_traps"
  )
  lazy val contestAdderTautologies: ProblemFamily = problems(
    "adder_tautologies"
  )
  lazy val contestAttractors: ProblemFamily = problems("attractors")
  lazy val contestAttractorNormalForms: ProblemFamily = problems(
    "attractor_normal_forms"
  )
  lazy val contestAnswers: ProblemFamily = problems("answers")
