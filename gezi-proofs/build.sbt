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

// Suites run one at a time in this project's JVM: several of them run lake in
// the Lean package, which must not run twice at once (project/LeanTests.scala).
Test / testForkedParallel := false

// The suites run lake in the Lean package: one such test group at a time
// (project/LeanTests.scala).
Test / test / testGrouping := Def.uncached(LeanTests.tagged((Test / test / testGrouping).value))

Test / testSelected / testGrouping := Def.uncached(LeanTests.tagged((Test / testSelected / testGrouping).value))

Test / testQuick / testGrouping := Def.uncached(LeanTests.tagged((Test / testQuick / testGrouping).value))

// Tests that read the files of Gezi find them from the build's root, the
// parent of this project's directory.
Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
moduleName := "gezi-proofs"
publish / skip := false
