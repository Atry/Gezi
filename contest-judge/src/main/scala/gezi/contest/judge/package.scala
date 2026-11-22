package gezi.contest

/** The contest judge:
  * a round's points file ([[PointsFile]], written with
  * `judgePointsFile` or [[PointsFile.written]]), the reference readers
  * ([[ReferenceEntry]], whose JVMs run `judgeReferenceRunner`), and the
  * supervisor ([[Supervisor]], `judgeSupervisor`), a separate process that
  * orders the points by the seed, starts each reader's JVM, measures the
  * setup and each point's wall time from outside, enforces the wall-clock
  * limits, and writes one row of a TSV for each reading. An entry's JVM runs
  * the runner of `gezi.contest.runner` on the entry's classpath and the
  * runner's, without this module or `contest-corpora`, in the sandbox
  * ([[Sandbox]]) unless `--sandbox none`; a reference reader's
  * JVM runs on this module's classpath, outside the sandbox. The module
  * depends on `contest-entry`, `contest-runner`, `contest-corpora` and
  * `jit`.
  */
package object judge
