package gezi

/** The trace player, compiled by Scala.js: a
  * page that plays a sequence of IR terms, step k showing term k, read from
  * the lambdalattice texts the page embeds. How a trace yields that sequence
  * (the trace format) and the transition within a step (the FLIP overlay)
  * are not built yet.
  *
  * The pure parts, run by the tests on Node.js: `Frame` (what a position
  * shows), `PlayState` (the state the URL hash spells), `TraceText` (the
  * terms of the texts), `NodeShape` and `CodeDisplay` (what a node draws),
  * `TracePageText` (the page's HTML). The parts that need a browser:
  * `TermView` and `PlayerView` (Binding.scala and html.scala), `PageLocation`
  * and `PageClock` (the hash and the animation frames, through
  * LatestEvent.scala), `TracePage` (the script's entry).
  */
package object traceplayer:
  /** The capability the player's replays and printers are given: a trace's terms are read under no facts, which hold no
    * storage, so the capability reads none; the player is the one place that sets it up.
    */
  private[traceplayer] given playerStorageAccess: gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()
