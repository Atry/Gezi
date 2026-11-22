package gezi.contest.corpora.reductions

import gezi.contest.corpora.claims

/** The attractors of the contest's API, `problems/attractors`: the claims
  * group's port (`claims.Attractors`), which the reduction group's
  * generators build their programs from.
  */
type Attractors = claims.Attractors

/** The spellings of closed terms (`claims.Attractors`'s companion). */
val Attractors = claims.Attractors

/** An attractor's spelling (`claims.Spelling`). */
type Spelling = claims.Spelling

/** The spellings, `Direct` and `Respelled` (`claims.Spelling`). */
val Spelling = claims.Spelling
