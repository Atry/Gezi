// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// The tests fork, and find the baseline's entry from the build's root.
Test / fork := true

Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"

// almond's kernel and its interpreter API (https://github.com/Atry/private-overlay/issues/1554,
// section 3.2.2, the user, 2026-11-02: "可以用almond").
// Its api module declares com.github.jupyter:jvm-repr, which only JitPack
// serves; no class of api_3 0.15.0 references it (its classes grepped for
// "jupyter", 2026-11-02), so it is left out rather than adding a resolver
// that builds artifacts from GitHub.
libraryDependencies += ("sh.almond" %% "kernel" % "0.15.0")
  .exclude("com.github.jupyter", "jvm-repr")

// The parser of the kernel's command line, as almond's own kernels have it
// (almond.echo.EchoKernel); the version is the one of the case-app-annotations
// that almond's kernel module brings.
libraryDependencies += "com.github.alexarchambault" %% "case-app" % "2.2.0"

// `jupyterKernelInstall` installs the kernel `lambdalattice` the way almond
// installs its own kernels (almond's docs/pages/install-other.md, the
// all-included launcher; the user, 2026-11-10: "完全照 almond 的方式：把内核打成
// coursier 启动器再运行它的 `--install`"; "能不能写成sbt的命令，在jupyter.nix中调用？"):
// it puts every jar of this project's runtime classpath into one coursier
// bootstrap launcher, made by coursier's own generator
// (project/coursier-launcher.sbt), and runs the launcher once with
// `--install`. almond's Install then writes
// <build root>/target/jupyter/kernels/lambdalattice/kernel.json, whose
// command it derives from the launcher's properties, and copies the launcher
// beside it; the temporary launcher is deleted. The dev shell's JUPYTER_PATH
// names <build root>/target/jupyter (the monorepo's modules/jupyter.nix), so
// Jupyter starts `java -cp <that launcher.jar> ...` itself: no sbt and no
// script at a kernel's start. The kernel runs the classpath as it was at the
// install, so the task is run again after the code changes.
// The entry is a data entry, read by the framework's generic entry
// (contest-entry-generic) from the directory given as the task's one
// argument, recorded in the spec as it is; there is no default entry (the
// user, 2026-11-13: "Presets are not 'default'. All presets should be
// opt-in"). The directory need not exist at the install: the kernel reads
// its entry.lambdalattice when it starts. The heap is the small one of a
// reference reader's JVM (the monorepo's AGENTS.md, "Small Limits Are a
// Debugging Instrument"), given through the spec's environment because
// almond's command has no place for an option of the JVM. An optional second
// argument, the trace directory relative to the kernel's working directory
// (the notebook's), is recorded as the kernel's `--trace-directory`
// (gezi.jupyter.kernel.CellTraces), also opt-in.
// The task writes files outside sbt's cache, so it is uncached.
lazy val jupyterKernelInstall =
  inputKey[File](
    "Installs the Jupyter kernel of lambdalattice cells under the build's target/jupyter, for the entry directory given and, optionally, the trace directory"
  )

jupyterKernelInstall := Def.uncached {
  val (entryDirectory, traceArguments) =
    Def.spaceDelimited("<entry directory> [<trace directory>]").parsed match {
      case Seq(directory) =>
        (file(directory).getAbsolutePath, Seq.empty[String])
      case Seq(directory, traces) =>
        (file(directory).getAbsolutePath, Seq("--trace-directory", traces))
      case arguments =>
        sys.error(
          s"jupyterKernelInstall takes the entry directory and, optionally, the trace directory, and was given ${arguments.size} arguments"
        )
    }
  val log = streams.value.log
  val buildRoot = baseDirectory.value.getParentFile
  val kernelsDirectory = buildRoot / "target" / "jupyter" / "kernels"
  val jars = (Runtime / fullClasspathAsJars).value.map(entry =>
    fileConverter.value.toPath(entry.data)
  )
  val launcherContent =
    coursier.launcher.ClassLoaderContent.withUniqueFileNames(
      Seq(
        coursier.launcher.ClassLoaderContent(
          jars.map(jar =>
            coursier.launcher.ClassPathEntry.Resource(
              jar.getFileName.toString,
              java.nio.file.Files.getLastModifiedTime(jar).toMillis,
              java.nio.file.Files.readAllBytes(jar)
            )
          )
        )
      )
    )
  IO.withTemporaryDirectory { temporaryDirectory =>
    val launcher = temporaryDirectory / "lambdalattice-kernel.jar"
    coursier.launcher.BootstrapGenerator.generate(
      coursier.launcher.Parameters
        .Bootstrap(launcherContent, "gezi.jupyter.kernel.LambdalatticeKernel")
        .withPreambleOpt(None),
      launcher.toPath
    )
    val exitCode = Fork.java(
      ForkOptions().withOutputStrategy(OutputStrategy.LoggedOutput(log)),
      Seq(
        "-jar",
        launcher.getAbsolutePath,
        "--install",
        "--force",
        "--jupyter-path",
        kernelsDirectory.getAbsolutePath,
        "--entry-directory",
        entryDirectory,
        "--env",
        // The kernel's heap holds what a cell's showing reads (CellInterpreter.showingSeconds):
        // the entry's reading of a value with no normal form, such as a function defined by
        // `fixpoint`, keeps the term it has built so far, which grows with its steps until the
        // showing's deadline. MEASURED 2026-11-20 (#1766, the image built at c8e90b55c, CPUs 0 to 3,
        // -Xmx3g, the GC log's peak after a collection), the tuple of a prelude file shown whole
        // until the deadline: list 1075 MB, natural 1108 MB, combinators 1361 MB; boolean, which
        // shows in 1 s, 288 MB. The heap is 1.5 times the largest; at -Xmx256m these ran out of
        // memory before the deadline.
        "JAVA_TOOL_OPTIONS=-Xmx2g"
      ) ++ traceArguments
    )
    if (exitCode != 0)
      sys.error(s"the launcher's --install exited with $exitCode")
  }
  kernelsDirectory / "lambdalattice"
}

// The trace player's files the kernel puts in the page of each trace of its
// cells (gezi.jupyter.kernel.CellTraces; https://github.com/Atry/private-overlay/issues/1497,
// section 6.5, use 3): the fully optimized script and the style sheets a page
// links (gezi.rewritetrace.TracePageText.playerStyleSheets) with the fonts
// the icons' style sheet loads, under gezi/jupyter/kernel/trace-player/ on
// the classpath, at their paths under the player's directory. CellTracesTest
// checks that the kernel finds every file a page needs. Only these files:
// the player's whole directory, with the webjars' other files, is 27 MB
// (measured 2026-11-19), these 4.5 MB. Uncached: the task copies files, and
// sbt 2 caches no task whose result is a File.
lazy val tracePlayerResources =
  taskKey[Seq[File]]("the trace player's files, as resources of the kernel")

tracePlayerResources := Def.uncached {
  val report = (LocalProject("trace-player") / Compile / fullLinkJS).value.data
  val linked = (LocalProject(
    "trace-player"
  ) / Compile / fullLinkJS / scalaJSLinkerOutputDirectory).value
  val styles = (LocalProject(
    "trace-player"
  ) / Assets / com.typesafe.sbt.web.Import.WebKeys.assets).value
  val scripts = report.publicModules.map(_.jsFileName).toVector
  assert(
    scripts == Vector("main.js"),
    s"the player links to one script, main.js: $scripts"
  )
  val sources = Vector("main.js" -> linked / "main.js") ++ Vector(
    "player.css",
    "lib/bootstrap/dist/css/bootstrap.min.css",
    "lib/bootstrap-icons/font/bootstrap-icons.min.css",
    "lib/bootstrap-icons/font/fonts/bootstrap-icons.woff2",
    "lib/bootstrap-icons/font/fonts/bootstrap-icons.woff"
  ).map(path => path -> styles / path)
  val root =
    (Compile / resourceManaged).value / "gezi" / "jupyter" / "kernel" / "trace-player"
  sources.map { case (path, source) =>
    assert(source.isFile, s"the player has no $path at $source")
    val target = root / path
    IO.copyFile(source, target)
    target
  }
}

Compile / resourceGenerators += tracePlayerResources.taskValue
