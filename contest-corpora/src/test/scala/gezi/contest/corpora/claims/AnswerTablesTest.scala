package gezi.contest.corpora.claims

import gezi.contest.corpora.claims.ClaimsTesting.*

/** The verdict's parts of `problems/answers` that do not evaluate. */
class AnswerTablesTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of AnswerTablesTest, "contest_answers: the verdict of a point intended to have no head", takes 16.825 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(30, "s")

  test("contest_answers: the verdict of a point intended to have no head") {
    assertEquals(contestAnswers.failedVerdict(0), Verdict.Matches)
    assertEquals(contestAnswers.failedVerdict(1), Verdict.Differs)
  }

  test("contest_answers: the verdict from the decodings") {
    val value = IntendedValue.BooleanValue(true)
    assertEquals(contestAnswers.decodingsVerdict(Set(Decoding.Decoded("boolean(true)")), value), Verdict.Matches)
    assertEquals(
      contestAnswers.decodingsVerdict(Set(Decoding.Decoded("boolean(true)"), Decoding.Decoded("boolean(false)")), value),
      Verdict.Differs)
    assertEquals(
      contestAnswers.decodingsVerdict(
        Set(Decoding.Failure("not_a_natural"), Decoding.Failure("not_a_boolean"), Decoding.Decoded("boolean(true)")),
        value),
      Verdict.DecodeFailure("not_a_boolean"))
  }
