// The settings of the in-tree entries' checks, a project of tests only that
// project/EntryProjects.scala derives: those of an entry's project, tests that
// fork with the small heap and see the build's root. Its dependencies, every
// entry's project and through them every module's, are given there.
enablePlugins(Snapshot4sPlugin)

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// Snapshots instead of hard-coded expected values (the user, 2026-10-31:
// "好，引入snapshot4s + munit吧。不要手写硬编码的assertion。"; CONTRIBUTING.md,
// "Snapshot Testing with snapshot4s"). Its munit module declares munit
// 1.3.4, which the 1.3.6 above supersedes within the series.
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Test / fork := true

Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
