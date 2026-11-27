package gezi.egraph

/** Whether a memo of a pure function keeps what it computed for later calls, an
  * option of the implementation that owns it, as every caching policy is
  * configurable: the e-graph's respelling memo (`EGraph.respellings`) and the
  * write-back's spelling cache (`gezi.strategies.LocalExtraction`). Either
  * changes only time: a value not kept is computed again.
  */
enum MemoRetention:

  /** Every value computed is kept for as long as the memo lives. */
  case Kept

  /** No value is kept: each call computes its own. */
  case NotKept
