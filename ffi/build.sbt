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



Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"

// TODO (https://github.com/Atry/private-overlay/issues/1797): the task
// ffi/jvmStubs that wrote the stubs of arbitrary Java constructs ahead of
// time (#1724, D1) is deleted with the stubs; the second step generates the
// computation graphs' wrappers. Read the task back with
// `git show ee10b3f9a:gezi/ffi/build.sbt`.
