package gezi.contest.entries

/** The contest entry `contest-entries-osprey`:
  * [[OspreyEntryProvider]], registered with `java.util.ServiceLoader`,
  * compiles the baseline's library and gives an [[OspreyEntry]], which reads
  * each point's program by the baseline's JIT as the front end gives it, or,
  * when that reading does not finish, compiles it type checked, and keeps
  * the reading of each program met in the pass. It uses only the framework's
  * public API. It was copied from the baseline entry, since deleted.
  */
package object osprey
