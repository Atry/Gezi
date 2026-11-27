package com.yang_bo.gezi.contest.corpora.claims

import com.yang_bo.gezi.contest.corpora.claims.ClaimsTesting.*

/** The respelling of the attractors of `problems/attractors`. */
class ContestAttractorsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  test(
    "a respelled term is the direct one after a beta step at each variable head"
  ) {
    val term = Attractors.surface(attractors.attractorFunction("map"))
    assertEquals(
      form(Attractors.spelledSurface(Spelling.Respelled, term)),
      form(attractors.attractorSurface("map", Spelling.Respelled))
    )
  }
