package gezi.jupyter.kernel

import almond.channels.zeromq.ZeromqThreads
import almond.kernel.Kernel
import almond.kernel.KernelThreads
import almond.kernel.install.Install
import almond.kernel.install.Options as InstallOptions
import almond.logger.LoggerContext
import almond.util.ThreadUtil.singleThreadedExecutionContextExecutorService
import caseapp.CaseApp
import caseapp.HelpMessage
import caseapp.Recurse
import caseapp.RemainingArgs
import caseapp.core.help.Help
import caseapp.core.parser.Parser
import java.nio.file.Files
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.runner.EntryRunner
import scala.concurrent.duration.DurationInt

/** The options of the kernel's entry, in the shape of the options of almond's
  * own kernels (almond 0.15.0, `almond.echo.Options`): the connection file of a
  * kernel that serves cells, or `--install` with almond's install options. The
  * entry's directory is required in both uses: an install records the arguments
  * it was run with as the kernel's, so a kernel installed without it could not
  * start.
  */
final case class KernelOptions(
    @HelpMessage("the connection file Jupyter passes to the kernel it starts")
    connectionFile: Option[String] = None,
    @HelpMessage("the directory of the entry that runs the cells")
    entryDirectory: String,
    @HelpMessage(
      "the directory, relative to the kernel's working directory, where the cells' traces and their players are written and shown from"
    )
    traceDirectory: Option[String] = None,
    @HelpMessage(
      "the notebook whose cells the kernel serves, where Jupyter does not name it, as jupyter console does not"
    )
    notebook: Option[String] = None,
    @HelpMessage("install the kernel spec instead of serving cells")
    install: Boolean = false,
    @Recurse
    installOptions: InstallOptions = InstallOptions()
)

object KernelOptions:
  given parser: Parser[KernelOptions] = Parser.derive
  given help: Help[KernelOptions] = Help.derive

/** The kernel's entry, in the shape of almond's own kernels (almond 0.15.0,
  * `almond.echo.EchoKernel`).
  *
  * With `--install` it installs the kernel spec through almond's `Install`,
  * which writes `kernel.json` and derives the kernel's command from the
  * coursier launcher that runs it (the properties `coursier.mainJar` and
  * `coursier.main.arg-N`), copying the launcher beside the spec; this entry
  * derives no command. So `--install` is run through a coursier launcher, as
  * the build's task `jupyter-kernel/jupyterKernelInstall` does. The spec asks
  * for an interrupt as a message on the control channel: Jupyter's default, the
  * signal SIGINT, ends the JVM (measured 2026-11-10).
  *
  * Otherwise it serves cells on the connection file, the mixins of one notebook
  * (`CellInterpreter.started`), joined by choice with the tree of URIs whose
  * visible subtree is the entry directory's parent. The cells stand where
  * `location` says. A value a cell outputs is shown by the entry its classpath
  * registers (`EntryRunner.provider`, the framework's generic entry) of the
  * entry's directory, on a fresh cache service of the framework's default
  * (`Defaults.caches`). A directory with no `entry.lambdalattice` ends the
  * kernel at its start, saying where to put one: there is no default entry,
  * every preset being opt-in.
  *
  * With `--trace-directory`, also opt-in, the entry writes the trace of every
  * point it extracts (`ArticleDestination.WrittenWithTraces`) into the kernel's
  * own directory under it, and each cell's output shows the player of each
  * trace the cell wrote (`CellTraces`).
  */
@SuppressWarnings(
  Array("gezi.warts.NoJavaUtilConcurrent")
) // 可以用almond。可以把整个基于almond的适配层都当成”局部“ (the user, 2026-11-02)
object LambdalatticeKernel extends CaseApp[KernelOptions]:

  def run(options: KernelOptions, remainingArguments: RemainingArgs): Unit =
    if remainingArguments.all.nonEmpty then
      sys.error(
        s"the kernel takes options only, got ${remainingArguments.all.mkString("[", ", ", "]")}"
      )
    if options.install then
      val directory = Install.install(
        defaultId = "lambdalattice",
        defaultDisplayName = "lambdalattice",
        language = "lambdalattice",
        options = options.installOptions,
        defaultLogoOpt = None,
        connectionFileArgs = Install.defaultConnectionFileArgs,
        interruptMode = Some("message"),
        env = options.installOptions.envMap(),
        extraStartupClassPath = Nil
      )
      Console.err.println(
        s"installed the lambdalattice kernel under $directory"
      )
    else
      val connectionFile = options.connectionFile.getOrElse(
        sys.error("neither --install nor --connection-file was given")
      )
      val entryDirectory = Paths.get(options.entryDirectory)
      if !Files.isRegularFile(entryDirectory.resolve("entry.lambdalattice"))
      then
        sys.error(
          s"the entry directory $entryDirectory holds no entry.lambdalattice: there is no default entry; " +
            s"put an entry's entry.lambdalattice in $entryDirectory, or mount a directory holding one at $entryDirectory"
        )
      val treeRoot = entryDirectory.toAbsolutePath.normalize.getParent
      val traces = options.traceDirectory.map(directory =>
        CellTraces.started(Paths.get(directory), Paths.get(""))
      )
      val destination = traces.fold(ArticleDestination.Discarded)(shown =>
        ArticleDestination.WrittenWithTraces(shown.directory)
      )
      // The kernel's cache service is never cleared: a session is no contest's
      // round, and what one cell computed may serve every later cell; keeping
      // everything in memory and never clearing it is one of the options.
      val entry = EntryRunner
        .provider(getClass.getClassLoader)
        .initial(entryDirectory, Defaults.caches(Set.empty), destination)
      val location = LambdalatticeKernel.location(
        options.notebook,
        sys.env.get("JPY_SESSION_NAME"),
        Paths.get("").toAbsolutePath
      )
      val interpreter =
        CellInterpreter.started(treeRoot, location, entry, traces)
      val kernelThreads = KernelThreads.create("lambdalattice-kernel")
      Kernel
        .create(
          interpreter,
          singleThreadedExecutionContextExecutorService(
            "lambdalattice-interpreter"
          ),
          kernelThreads,
          singleThreadedExecutionContextExecutorService(
            "lambdalattice-cancellables"
          ),
          LoggerContext.nop
        )
        .flatMap(
          _.runOnConnectionFile(
            connectionFile,
            "lambdalattice",
            ZeromqThreads.create("lambdalattice-kernel"),
            Nil,
            autoClose = true,
            lingerDuration = 5.seconds,
            bindToRandomPorts = None
          )
        )
        .unsafeRunSync()(kernelThreads.ioRuntime)

  /** Where the cells the kernel serves stand: at the notebook `--notebook`
    * names, resolved against the working directory; else at the file that
    * Jupyter's `JPY_SESSION_NAME` names, which jupyter_server sets in a
    * kernel's environment to the session's path, relative to the server's root
    * or joined to the kernel's working directory (jupyter_server's
    * `SessionManager.get_kernel_env`), so its file name alone is taken in the
    * working directory, which jupyter_server makes the notebook's; else, as
    * under `jupyter console` and `jupyter run`, which name no notebook, at the
    * working directory itself, whose level of the tree the cells then join by
    * choice.
    */
  def location(
      option: Option[String],
      sessionName: Option[String],
      workingDirectory: java.nio.file.Path
  ): NotebookLocation =
    option
      .map(path => NotebookLocation.of(workingDirectory.resolve(path)))
      .orElse(
        sessionName.map(name =>
          NotebookLocation.of(
            workingDirectory.resolve(Paths.get(name).getFileName)
          )
        )
      )
      .getOrElse(NotebookLocation.of(workingDirectory))
