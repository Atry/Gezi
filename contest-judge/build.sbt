enablePlugins(Snapshot4sPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// Snapshots instead of hard-coded expected values (the user, 2026-10-31:
// "好，引入snapshot4s + munit吧。不要手写硬编码的assertion。"; CONTRIBUTING.md,
// "Snapshot Testing with snapshot4s"). Its munit module declares munit
// 1.3.4, which the 1.3.6 above supersedes within the series.
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

Test / fork := true

// The probe entries of the tests (ProbeEntries) copy the class files of a test
// class out of the directory its code source names. sbt 2 exports a project's
// products as jars by default (exportJars, sbt 1: false), so the code source
// became contest-judge's tests jar and the copy threw NotDirectoryException;
// this project's products stay directories, as under sbt 1. The entries' and
// the runner's classpaths, which the sandbox binds, are jars under sbt 2.
exportJars := false

// Tests that read the files of Gezi find them from the build's root, the
// parent of this project's directory.
Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"

/** The runtime classpath of each entry's project, as the property the
  * supervisor builds the classpath of `--entry <player>`'s JVM from, with
  * the runner's (`runnerClasspathOption`,
  * `SupervisorCommand.entryReaderClasspath`).
  */
lazy val entryClasspathOptions: Def.Initialize[Task[Seq[String]]] =
  entryClasspathOptionsOf(Set.empty)

// FIXME (2026-11-12, the setter's ruling relayed by lambda-typing): osprey's https://github.com/Atry/private-overlay/issues/2040
// entry does not compile since G3 deleted StandardLibrary.lemmasOf
// (https://github.com/Atry/private-overlay/issues/1517, section 13.3;
// contest-entries-osprey/src/main/scala/gezi/contest/entries/osprey/OspreyEntry.scala,
// lines 91 to 93), and the player ports its own code (the user, 2026-11-07:
// "我希望选手负责移植自己的代码"). The tests' JVM is therefore not handed
// osprey's classpath, which would compile it; the tests read the other players'.
// Put osprey back when its entry compiles.
lazy val playersLeftOutOfTests: Set[String] = Set("osprey")

/** The entry classpath properties of the build's players but those left
  * out, listed under the build's root, the parent of this project's base.
  */
def entryClasspathOptionsOf(leftOut: Set[String]): Def.Initialize[Task[Seq[String]]] = Def.taskDyn {
  EntryProjects
    .players(baseDirectory.value.getParentFile)
    .filterNot(leftOut)
    .map(player =>
      Def.task {
        given xsbti.FileConverter = fileConverter.value
        val classpath = (LocalProject(EntryProjects.projectName(player)) / Runtime / fullClasspath).value.files
        s"-Dgezi.judge.entryClasspath.$player=${classpath.mkString(java.io.File.pathSeparator)}"
      }
    )
    .join
}

/** The runtime classpath of `contest-runner`, as the property the supervisor
  * puts first on the classpath of every entry's JVM.
  */
lazy val runnerClasspathOption: Def.Initialize[Task[String]] = Def.task {
  given xsbti.FileConverter = fileConverter.value
  val classpath = (LocalProject("contest-runner") / Runtime / fullClasspath).value.files
  s"-Dgezi.judge.runnerClasspath=${classpath.mkString(java.io.File.pathSeparator)}"
}

/** The system properties a JVM of the judge's mains needs: the build's root,
  * each entry's classpath and the runner's.
  */
lazy val judgeSystemProperties: Def.Initialize[Task[Seq[String]]] = Def.task {
  s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}" +: (entryClasspathOptions.value :+ runnerClasspathOption.value)
}

lazy val exportRuntimeClasspath = taskKey[Seq[File]](
  "Writes the judge's runtime classpath to target/judge-classpath.txt and its system properties, as a java argument file, to target/judge-properties.txt"
)

Test / javaOptions ++= entryClasspathOptionsOf(playersLeftOutOfTests).value

Test / javaOptions += runnerClasspathOption.value

run / fork := true

run / javaOptions += "-Xmx256m"

run / javaOptions ++= judgeSystemProperties.value

// FIXME (2026-11-07, lambda-typing): under sbt 2's native client (sbtn, the https://github.com/Atry/private-overlay/issues/1996
// default `sbt` and `sbt --client`), `contest-judge/runMain
// gezi.contest.judge.judgePointsFile ...` throws NoClassDefFoundError for
// caffeine's Interner, a dependency of ir: the client forks the JVM on its
// own side (`NetworkClient.clientSideRun`, `ForkRun`), and with -verbose:class
// that JVM loaded classes only from scala-library and the projects' jars, no
// coursier jar. Measured on repeated_library_hotspots_calls_10000_hot with
// seed 20261031; with `sbt --server` (no native client) the same command
// writes the points. A defect of sbt's client-side run, not of this build;
// run the judge's mains with `sbt --server`, or through the exported
// classpath (`exportRuntimeClasspath`, then `java -cp "$(cat
// contest-judge/target/judge-classpath.txt)"
// @contest-judge/target/judge-properties.txt ...`) as a round's commands do.

// `contest-judge/exportRuntimeClasspath` writes what a JVM of the judge's
// mains needs, so that a round runs them with `java` outside sbt (the
// record's section 4.1): the runtime classpath, one line, to
// contest-judge/target/judge-classpath.txt, and the system properties, one
// quoted argument a line in the syntax of java's `@` argument files, to
// contest-judge/target/judge-properties.txt. `sbt runMain` writes its whole
// command line, a seed included, to the sbt server's global log
// (target/global-logging), and its forked JVM shows it in `ps`. The task
// writes files, a side effect sbt 2's cache would skip, so it is uncached.
exportRuntimeClasspath := Def.uncached {
  given xsbti.FileConverter = fileConverter.value
  // contest-judge/target, the directory the record's commands read: sbt 2's
  // `target` is the project's directory under the build's target/out.
  val classpathFile = baseDirectory.value / "target" / "judge-classpath.txt"
  val propertiesFile = baseDirectory.value / "target" / "judge-properties.txt"
  def quoted(argument: String): String =
    "\"" + argument.replace("\\", "\\\\").replace("\"", "\\\"") + "\""
  IO.write(classpathFile, (Runtime / fullClasspath).value.files.mkString(java.io.File.pathSeparator) + "\n")
  IO.write(propertiesFile, judgeSystemProperties.value.map(quoted).mkString("", "\n", "\n"))
  Seq(classpathFile, propertiesFile)
}
