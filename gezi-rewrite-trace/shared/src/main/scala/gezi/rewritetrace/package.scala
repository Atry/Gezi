package gezi

/** The rewrite trace: a start term and the commands that rewrite it, round by
  * round, as the animation player reads them. [[Trace]] holds the commands and
  * replays them, computing what a command does not write (the replacement, the
  * provenance) from the equation it names ([[Statements]]); [[TraceText]]
  * writes a trace as a closed lambdalattice term of Scott data and reads it
  * back under the weak head (`gezi.knowledgereading.KnowledgeReading`). The
  * module depends on `ir`, `frontend` and `knowledge-reading`, so that the
  * player needs no proof, no library and no strategy; the flattening of an
  * article's proof into commands is `proofs`' `RewriteTrace`.
  */
package object rewritetrace
