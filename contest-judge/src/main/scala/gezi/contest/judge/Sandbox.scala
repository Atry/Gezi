package gezi.contest.judge

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths

/** The sandbox an entry's JVM runs in; the reference readers' JVMs
  * run outside it.
  *
  *   - `Bubblewrap(readablePaths)`, the default: the JVM is started by
  *     `bwrap` in new user, mount, process, network, IPC and UTS namespaces
  *     (`bubblewrapWords`). It sees a file system of its own, read only:
  *     the readable paths (the Nix store paths the JDK needs, and the
  *     framework's standard library, which every entry compiles), each
  *     element of its classpath and the entry's directory, plus `/proc` of its own
  *     process namespace, a minimal `/dev`, and a fresh private `/tmp` of at
  *     most `temporarySize` bytes, the one place it can write. Its
  *     environment is empty but for the locale. It has no network but its
  *     own loopback, sees no other process, and is killed when `bwrap` is
  *     killed (the supervisor's kill) or its parent dies. The runner
  *     installs the execution filter (`gezi.contest.runner.ExecutionFilter`)
  *     before it loads the entry, so no program can be executed: bubblewrap
  *     cannot deny `execve` itself, since it loads a seccomp filter before it
  *     executes the JVM, which that filter would deny.
  *     The writable paths, none in a scored pass, are bound writable at
  *     their own places: the article directory of the judge's article
  *     re-read, a fresh
  *     directory for each point.
  *   - `Unconfined` (`--sandbox none`): the JVM runs as the supervisor's
  *     process does, for tests that cannot use the sandbox.
  */
enum Sandbox:
  case Unconfined
  case Bubblewrap(readablePaths: Vector[Path], writablePaths: Vector[Path] = Vector.empty)

  /** The sandbox with the directory also writable: bound writable inside
    * bubblewrap; outside any sandbox it is writable already.
    */
  def writable(directory: Path): Sandbox = this match
    case Unconfined                                => Unconfined
    case Bubblewrap(readablePaths, writablePaths) => Bubblewrap(readablePaths, writablePaths :+ directory)

/** The bubblewrap sandbox's command words. */
object Sandbox:

  /** The size limit of the sandbox's `/tmp`, 64 MiB: the JVM writes its
    * performance data file there (32 KiB); what an entry writes there is
    * held in memory.
    */
  val temporarySize: Long = 64L << 20

  /** The bubblewrap sandbox of a JVM of the JDK at `javaHome` in the build
    * at `buildRoot`: the readable paths are the closure, in the Nix store,
    * of the store path holding the JDK (`nix-store --query --requisites`),
    * and the build's source tree, `corpora`, whose library and knowledge
    * files every entry reads. Throws `IllegalArgumentException` when `javaHome` is not
    * in the Nix store.
    */
  def bubblewrap(javaHome: Path, buildRoot: Path): Sandbox =
    val store = Paths.get("/nix/store")
    val absolute = javaHome.toAbsolutePath.normalize
    if !absolute.startsWith(store) || absolute.getNameCount <= store.getNameCount then
      throw IllegalArgumentException(s"the sandbox binds the JDK's closure in the Nix store, and $absolute is not in it; --sandbox none runs without the sandbox")
    val storePath = store.resolve(absolute.getName(store.getNameCount))
    val query = ProcessBuilder("nix-store", "--query", "--requisites", storePath.toString)
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .start()
    val closure = String(query.getInputStream.readAllBytes(), StandardCharsets.UTF_8).split('\n').toVector.filter(_.nonEmpty).map(Paths.get(_))
    val status = query.waitFor()
    assert(status == 0, s"nix-store --query --requisites $storePath ended with status $status")
    assert(closure.contains(storePath), s"the closure of $storePath does not hold it: $closure")
    Bubblewrap(closure :+ buildRoot.toAbsolutePath.normalize.resolve("corpora"))

  /** The words that start a program in the bubblewrap sandbox of the
    * readable paths, for a JVM of the classpath reading the entry directory:
    * every path bound read only at its own place, the readable paths and the
    * entry directory required, the classpath's elements bound when they
    * exist (a JVM skips a missing one too), and then the writable paths,
    * each required and bound writable at its own place. The private `/tmp` is mounted
    * before the bindings, so that a binding under `/tmp` (a test's
    * temporary directory) is not covered by it; the root and `/dev` are
    * made read only last. The environment is cleared, so that no variable of
    * the supervisor's (a token of the shell that started it, say) reaches the
    * entry; the one variable set, `LC_ALL=C.UTF-8`, a locale built into
    * glibc, keeps the JVM's encoding of file names UTF-8: the host's locale
    * archive is outside the sandbox, and without a locale the JVM falls back
    * to ASCII.
    */
  def bubblewrapWords(readablePaths: Vector[Path], classpath: String, entryDirectory: Path, writablePaths: Vector[Path]): Vector[String] =
    val directory = entryDirectory.toAbsolutePath.normalize.toString
    val classpathElements = classpath.split(File.pathSeparator).toVector.filter(_.nonEmpty).map(Paths.get(_).toAbsolutePath.normalize.toString)
    Vector(
      "bwrap",
      "--unshare-all",
      "--die-with-parent",
      "--new-session",
      "--proc",
      "/proc",
      "--dev",
      "/dev",
      "--size",
      temporarySize.toString,
      "--tmpfs",
      "/tmp"
    ) ++
      readablePaths.flatMap(path => Vector("--ro-bind", path.toString, path.toString)) ++
      classpathElements.flatMap(element => Vector("--ro-bind-try", element, element)) ++
      Vector(
        "--ro-bind",
        directory,
        directory
      ) ++
      writablePaths.map(_.toAbsolutePath.normalize.toString).flatMap(path => Vector("--bind", path, path)) ++
      Vector(
        "--remount-ro",
        "/dev",
        "--remount-ro",
        "/",
        "--clearenv",
        "--setenv",
        "LC_ALL",
        "C.UTF-8",
        "--chdir",
        directory,
        "--"
      )
