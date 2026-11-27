package gezi.standardlibrary

import java.nio.file.Files
import java.nio.file.Path
import scala.concurrent.ExecutionContext
import scala.concurrent.Future
import scala.concurrent.blocking
import scala.jdk.StreamConverters.*

/** The runner of the Lean package's `lake` (`gezi/lean`), for the tests that
  * read the package and for the verifier of round certificates
  * (`gezi.proofs.ArticleVerification`). `lake` must be on the path.
  */
object LeanProcesses:

  /** What `lake` with the arguments writes on its standard output, run in the
    * package `leanDirectory`; its standard error goes to this JVM's. Throws
    * `IllegalStateException` with the output when it exits with a status other
    * than 0.
    *
    * When `stopped` completes (a `stoppableTest`'s stop request, completed at
    * the test's deadline) while `lake` runs, the process and every process
    * under it (the `lean` it starts) are destroyed (`processTreeDestroyed`), so
    * that a run that overruns leaves no Lean build running; `lake` then exits
    * with a status other than 0 and this throws. Nothing interrupts a thread:
    * the stop is a callback on the future.
    */
  def lakeOutput(
      leanDirectory: Path,
      arguments: Seq[String],
      stopped: Future[Unit]
  ): String =
    val outputFile = Files.createTempFile("lake", ".out")
    val process = ProcessBuilder(("lake" +: arguments)*)
      .directory(leanDirectory.toFile)
      .redirectOutput(outputFile.toFile)
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .start()
    stopped.foreach(_ => processTreeDestroyed(process.toHandle))(using
      ExecutionContext.parasitic
    )
    val status = process.waitFor()
    val output = Files.readString(outputFile)
    Files.delete(outputFile)
    if status != 0 then
      val cause =
        if stopped.isCompleted then " (stopped at the test's deadline)" else ""
      throw IllegalStateException(
        s"lake ${arguments.mkString(" ")} exited with $status$cause:\n$output"
      )
    output

  /** The seconds a destroyed process is given to exit before it is destroyed
    * forcibly.
    */
  private val destroyGraceSeconds: Long = 5

  /** Asks the process and every process under it to terminate (SIGTERM on
    * Linux), the processes under it first, taken before any is asked so that
    * none escapes by being reparented when its parent exits; after
    * `destroyGraceSeconds`, on the global execution context, destroys forcibly
    * (SIGKILL) those still alive. Does nothing for a process that has exited.
    */
  def processTreeDestroyed(root: ProcessHandle): Unit =
    if root.isAlive then
      val tree = root.descendants().toScala(Vector) :+ root
      tree.foreach(_.destroy())
      Future {
        blocking(Thread.sleep(destroyGraceSeconds * 1000))
        tree.filter(_.isAlive).foreach(_.destroyForcibly())
      }(using ExecutionContext.global)
      ()
