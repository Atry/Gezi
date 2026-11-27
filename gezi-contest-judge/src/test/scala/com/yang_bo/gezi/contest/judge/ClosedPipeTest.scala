package com.yang_bo.gezi.contest.judge

/** The supervisor's write to a reader whose end of the pipe is closed
  * (`Supervisor.pointWritten`): it reports the point undelivered instead of
  * throwing, and a write to an open pipe is delivered. Its purpose is to catch
  * the pass ending on a "Broken pipe" when an entry's JVM ends between the
  * liveness check and the write. The closed pipe is a child process that closes
  * its standard input and stays alive, so that the write meets a pipe with no
  * reader, deterministically.
  */
class ClosedPipeTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  test("aWriteToAClosedPipeIsUndeliveredAndToAnOpenOneDelivered") {
    val closed = ProcessBuilder("sh", "-c", "exec 0<&-; sleep 5").start()
    val open = ProcessBuilder("sh", "-c", "cat > /dev/null").start()
    Thread.sleep(500)
    val line = "point\tevaluation\t" + ("x" * 100000) + "\n"
    assertEquals(Supervisor.pointWritten(closed.getOutputStream, line), false)
    assertEquals(Supervisor.pointWritten(open.getOutputStream, line), true)
    closed.destroyForcibly()
    open.destroyForcibly()
  }
