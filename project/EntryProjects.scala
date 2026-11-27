import sbt._
import sbt.Keys._

/** The contest entries of the build: every directory `contest-entries-<name>/` of the build's
  * root that holds a `build.sbt` or a `src/` is the project of the same name,
  * which depends on `contest-entry` and on the baseline's public projects
  * (`jit`, `strategies`, `lemma-encoding-baseline`, `weakhead`,
  * `standardlibrary`, `frontend`, `narrow-blocks`), its tests also on `generatedinputs`
  * (generated inputs, Hedgehog and snapshots) and on `interface-laws` (the
  * laws of the replaceable interfaces, which a suite runs on a
  * replacement), and on the reusable modules
  * below, and on nothing else. None of these depends on `contest-corpora` or
  * `contest-judge`, at compile time or at run time, so the project's runtime
  * classpath, which with `contest-runner`'s is the whole classpath of the
  * entry's JVM, holds neither the problem
  * generators and their judges nor the judge's reference readers and
  * supervisor; the judge's `EntryClasspathTest` checks it in a JVM the
  * supervisor starts, and the conventions' `EntrySourcesTest` checks that no
  * source of an entry names either package. The `build.sbt` in the directory
  * holds the project's settings; it must not add a dependency on either
  * project. An sbt file defines a fixed set of projects, so the entries,
  * which are found on disk, are added by this plugin's `derivedProjects`
  * on the root; build.sbt aggregates them through the project
  * `contest-entries`, and contest-judge/build.sbt passes their classpaths
  * to the judge.
  *
  * A reusable module lives in a directory
  * `contest-modules-<name>/` of the build's root that holds a `build.sbt` or
  * a `src/`, the project of the same name. It depends on the baseline's
  * public projects above and on `contest-entry`, whose replaceable
  * interfaces it implements, such as an executor module
  * (`gezi.contest.entry.ExecutorModule`),
  * registered with `java.util.ServiceLoader` in its own
  * `META-INF/services`. It registers no `EntryProvider`: the conventions'
  * `EntrySourcesTest` checks that no module's `META-INF/services` names
  * one, so that an entry's JVM still finds exactly one provider. Every
  * entry's project, written as data or in Scala, depends on every module's,
  * so any entry may select it, and its registrations are on the entry's,
  * hence the runner's, classpath. A module does not depend on another
  * module.
  *
  * The suites that read the in-tree entries are the tests of one more
  * project, `contest-in-tree-entries` (`inTreeEntriesProjectName`), which
  * depends on every entry's project and so sees every module's
  * registrations.
  */
object EntryProjects extends AutoPlugin {

  /** The prefix of an entry's directory, and of its project's name. */
  private val entryPrefix = "contest-entries-"

  /** The prefix of a reusable module's directory, and of its project's
    * name.
    */
  private val modulePrefix = "contest-modules-"

  /** The prefix of an entry's natives project's directory, and of its
    * project's name.
    */
  private val nativesPrefix = "contest-natives-"

  /** The names after `prefix`, sorted, of the directories of the build's root
    * whose names start with `prefix` and that hold a `build.sbt`, a `src/`,
    * or one of the files `markers`.
    */
  private def suffixes(buildRoot: File, prefix: String, markers: Seq[String] = Seq.empty): Seq[String] =
    Option(buildRoot.listFiles).toSeq.flatten
      .filter(directory =>
        directory.isDirectory && directory.getName.startsWith(prefix) &&
          ((directory / "build.sbt").isFile || (directory / "src").isDirectory ||
            markers.exists(marker => (directory / marker).isFile))
      )
      .map(_.getName.stripPrefix(prefix))
      .sorted

  /** The files that make a directory an entry written as data:
    * `entry.lambdalattice`, and `entry.pl`, which `EntryData` rejects with a
    * message that says to write the settings in `entry.lambdalattice`, so
    * that an entry's directory left with an `entry.pl` fails with that
    * message and not with no project at all.
    */
  val entryDataFiles: Seq[String] = Seq("entry.lambdalattice", "entry.pl")

  /** The entries' names, sorted: the suffixes of the directories
    * `contest-entries-<name>` of the build's root that hold a `build.sbt`, a
    * `src/` or an entry data file.
    */
  def players(buildRoot: File): Seq[String] = suffixes(buildRoot, entryPrefix, entryDataFiles)

  /** Whether the entry is written as data: its directory holds an
    * entry data file and no Scala source, and its project then depends on
    * the framework's generic entry (`contest-entry-generic`), which
    * registers the one entry provider.
    */
  def writtenAsData(buildRoot: File, player: String): Boolean = {
    val directory = buildRoot / projectName(player)
    entryDataFiles.exists(file => (directory / file).isFile) && !(directory / "src" / "main" / "scala").isDirectory
  }

  /** The entries' natives projects, sorted: the directories
    * `contest-natives-<name>` that hold a `build.sbt` or a `src/`. Each
    * depends on `jit` alone, whose `NativesProvider` it implements; the
    * conventions check that it holds native implementations only.
    */
  def nativesProjects(buildRoot: File): Seq[String] = suffixes(buildRoot, nativesPrefix)

  /** The project of an entry's natives, which is also its directory's name. */
  def nativesProjectName(player: String): String = s"$nativesPrefix$player"

  /** The reusable modules, sorted: the directories `contest-modules-<name>`
    * of the build's root that hold a `build.sbt` or a `src/`.
    */
  def modules(buildRoot: File): Seq[String] = suffixes(buildRoot, modulePrefix)

  /** The project of the module, which is also the name of its directory. */
  def moduleProjectName(module: String): String = s"$modulePrefix$module"

  /** The baseline's public projects, which entries and modules depend on. */
  private val publicProjects: Seq[ClasspathDep[ProjectReference]] = Seq(
    LocalProject("jit"),
    LocalProject("strategies"),
    LocalProject("lemma-encoding-baseline"),
    LocalProject("weakhead"),
    LocalProject("standardlibrary"),
    LocalProject("frontend"),
    LocalProject("narrow-blocks"),
    LocalProject("generatedinputs") % Test,
    LocalProject("interface-laws") % Test
  )

  /** The project of the entry, which is also the name of its directory. */
  def projectName(player: String): String = s"$entryPrefix$player"

  /** The project that aggregates every entry's, every module's and the
    * in-tree entries' checks (`inTreeEntriesProjectName`), which
    * the build's root aggregates by this name: the root is defined in
    * build.sbt before the directories are listed, so it cannot name them.
    */
  val aggregateProjectName: String = "contest-entries"

  /** The project of the in-tree entries' checks, which is also its
    * directory's name: a project of tests only that depends on every entry's
    * project, through them on every module's, on `contest-entry-generic`,
    * whose provider its tests build, and at test scope on `generatedinputs`.
    * Its test classpath therefore holds every module's registrations, as an
    * entry's JVM does, so that an entry that selects a module
    * (`executor (module …)`, a round's `extractor`) reads there; the tests of
    * `contest-entry-generic` see no module, and the framework's project must
    * not depend on an entry's. Its name does not start with an entry's or a
    * module's prefix, so `players` and `modules` never list it. Its tests
    * get, as the property `gezi.entryAndModuleProjects`, the projects it
    * depends on for their registrations, so that they check that its
    * classpath sees each one's services.
    *
    * FIXME: the classpath holds the natives of every entry's natives https://github.com/Atry/private-overlay/issues/2000
    * project, while an entry's JVM holds its own alone, so an entry whose
    * library binds a native that only another entry's project implements
    * reads here and fails in the judge, and two entries that implement one
    * native make `NativesProvider.loaded` throw here. No
    * `contest-natives-*` project exists on 2026-11-21; candidates: read each
    * entry with the natives of its own project only, or run the check in a
    * JVM per entry on the entry's own classpath, as the judge does.
    */
  val inTreeEntriesProjectName: String = "contest-in-tree-entries"

  /** The entries', natives' and modules' projects, the in-tree entries'
    * checks and the aggregate of the build whose root is
    * the project this plugin is enabled on (build.sbt enables it on the root
    * alone), found under the root project's base directory. sbt hands
    * `derivedProjects` the project with its base resolved against the build
    * file's directory, so the build loads from any working directory: one sbt
    * server may load several builds, each a `RootProject` of a meta-build,
    * whose working directory is none of theirs.
    */
  override def derivedProjects(root: ProjectDefinition[?]): Seq[Project] = {
    val buildRoot = root.base
    assert(
      buildRoot.isAbsolute,
      s"sbt handed derivedProjects the root project ${root.id} with a relative base $buildRoot; the entries would be listed under the JVM's working directory"
    )
    val moduleProjects = modules(buildRoot).map(module =>
      Project(moduleProjectName(module), buildRoot / moduleProjectName(module)).dependsOn((LocalProject("contest-entry") +: publicProjects)*)
    )
    val moduleDependencies: Seq[ClasspathDep[ProjectReference]] =
      modules(buildRoot).map(module => LocalProject(moduleProjectName(module)): ClasspathDep[ProjectReference])
    val nativesProjectsMade = nativesProjects(buildRoot).map(player =>
      Project(nativesProjectName(player), buildRoot / nativesProjectName(player)).dependsOn(LocalProject("jit"))
    )
    val entryProjects = players(buildRoot).map { player =>
      val ownNatives: Seq[ClasspathDep[ProjectReference]] =
        if (nativesProjects(buildRoot).contains(player)) Seq(LocalProject(nativesProjectName(player)))
        else Seq.empty
      val entry: Seq[ClasspathDep[ProjectReference]] =
        if (writtenAsData(buildRoot, player))
          Seq[ClasspathDep[ProjectReference]](LocalProject("contest-entry"), LocalProject("contest-entry-generic")) ++ moduleDependencies
        else LocalProject("contest-entry") +: moduleDependencies
      Project(projectName(player), buildRoot / projectName(player)).dependsOn((entry ++ publicProjects ++ ownNatives)*)
    }
    val inTreeEntriesProject = Project(inTreeEntriesProjectName, buildRoot / inTreeEntriesProjectName)
      .dependsOn(
        (entryProjects.map(project => LocalProject(project.id): ClasspathDep[ProjectReference]) ++ Seq[ClasspathDep[ProjectReference]](
          LocalProject("contest-entry-generic"),
          LocalProject("generatedinputs") % Test,
          // The unique spelling's premise is checked on each entry's facts by jit's test checker
          // (`UniqueSpellingPremiseCheck`).
          LocalProject("jit") % "test->test"
        ))*
      )
      .settings(
        // Uncached: sbt 2 keys a cached task by the values it reads, and a
        // string computed when the build loads is none of them, so a cached
        // option kept the projects of an earlier load (measured 2026-11-21:
        // with contest-modules-solo-tiering added and the build reloaded, the
        // option still listed the four entries alone).
        Test / javaOptions += Def.uncached(
          s"-Dgezi.entryAndModuleProjects=${(entryProjects ++ moduleProjects).map(_.id).mkString(",")}"
        )
      )
    val aggregateProject = Project(aggregateProjectName, buildRoot / aggregateProjectName)
      .aggregate((entryProjects ++ moduleProjects :+ inTreeEntriesProject).map(project => LocalProject(project.id): ProjectReference)*)
    moduleProjects ++ nativesProjectsMade ++ entryProjects :+ inTreeEntriesProject :+ aggregateProject
  }
}
