package gezi.contest.judge

import java.io.File
import java.nio.file.Files
import java.nio.file.Paths

/** The bubblewrap sandbox in the judge's tests: whether it can run here, and
  * the sandbox of the test JVM's JDK. A suite that runs an entry in it first
  * assumes `unavailable` is empty, so that it is skipped, saying why, where the
  * mechanism itself is missing; the monorepo's dev shell provides `bwrap`, and
  * the machine allows user namespaces.
  */
object TestSandbox:

  /** Why the sandbox cannot run here, if it cannot: no directory of `PATH`
    * holds an executable `bwrap`, or the kernel allows no user namespace
    * (`/proc/sys/user/max_user_namespaces` is missing or 0).
    */
  def unavailable: Option[String] =
    val onPath = sys.env
      .getOrElse("PATH", "")
      .split(File.pathSeparator)
      .toVector
      .filter(_.nonEmpty)
      .exists(directory => Files.isExecutable(Paths.get(directory, "bwrap")))
    val namespaces = Paths.get("/proc/sys/user/max_user_namespaces")
    val namespacesAllowed = Files.isReadable(namespaces) && Files
      .readString(namespaces)
      .trim
      .toLongOption
      .exists(_ > 0)
    Vector(
      Option.when(!onPath)(
        "bwrap is on no directory of PATH (the monorepo's dev shell provides it)"
      ),
      Option.when(!namespacesAllowed)("the kernel allows no user namespace")
    ).flatten.reduceOption(_ + "; " + _)

  /** The bubblewrap sandbox of the test JVM's JDK in this build. */
  lazy val bubblewrap: Sandbox = Sandbox.bubblewrap(
    Paths.get(System.getProperty("java.home")),
    Paths.get(sys.props("gezi.buildRoot"))
  )
