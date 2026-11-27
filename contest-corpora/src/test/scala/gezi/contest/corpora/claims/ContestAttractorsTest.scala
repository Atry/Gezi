package gezi.contest.corpora.claims

import gezi.contest.corpora.claims.ClaimsTesting.*

/** The respelling of the attractors of `problems/attractors`. */
class ContestAttractorsTest extends gezi.generatedinputs.FailFastSuite:

  test(
    "a respelled term is the direct one after a beta step at each variable head"
  ) {
    val term = Attractors.surface(attractors.attractorFunction("map"))
    assertEquals(
      form(Attractors.spelledSurface(Spelling.Respelled, term)),
      form(attractors.attractorSurface("map", Spelling.Respelled))
    )
  }
