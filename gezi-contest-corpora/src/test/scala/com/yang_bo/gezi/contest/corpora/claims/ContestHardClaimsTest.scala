package com.yang_bo.gezi.contest.corpora.claims

import com.yang_bo.gezi.contest.corpora.claims.ClaimsTesting.*

/** The claims of `problems/hard_claims`: the normal form a claim's closed
  * program expects.
  */
class ContestHardClaimsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  test("the expected normal form is the curried identity") {
    val (_, expected) = claims.claimProgram(
      "easy_constant",
      Template.MemberTemplate(2, "natural")
    )
    assertEquals(form(expected), "λx_0. λx_1. λx_2. x_2")
  }
