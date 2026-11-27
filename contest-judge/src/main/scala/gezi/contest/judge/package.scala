package gezi.contest

import gezi.ir.NoFacts
import gezi.ir.StorageAccess

/** The contest judge: a round's points file ([[PointsFile]], written with
  * `judgePointsFile` or [[PointsFile.written]]), the reference readers
  * ([[ReferenceEntry]], whose JVMs run `judgeReferenceRunner`), and the
  * supervisor ([[Supervisor]], `judgeSupervisor`), a separate process that
  * orders the points by the seed, starts each reader's JVM, measures the setup
  * and each point's wall time from outside, enforces the wall-clock limits, and
  * writes one row of a TSV for each reading. An entry's JVM runs the runner of
  * `gezi.contest.runner` on the entry's classpath and the runner's, without
  * this module or `contest-corpora`, in the sandbox ([[Sandbox]]) unless
  * `--sandbox none`; a reference reader's JVM runs on this module's classpath,
  * outside the sandbox. The module depends on `contest-entry`,
  * `contest-runner`, `contest-corpora` and `jit`.
  */
package object judge:

  /** The judge reads and writes every term under no facts: the reference
    * readers' programs, the points file's lines, the entries' answer lines
    * (`gezi.contest.runner.PipeLines.answerRead`). An entry's own configuration
    * is its JVM's.
    */
  private[judge] given NoFacts.type = NoFacts

  /** The capability to read a storage's view under no facts, which have no
    * storage: the judge's own, granted here.
    */
  private[judge] given StorageAccess = StorageAccess.granted()
