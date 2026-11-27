enablePlugins(Snapshot4sPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// Hedgehog's core and runner, at the version generatedinputs/build.sbt pins
// and explains.
libraryDependencies ++= Seq(
  "qa.hedgehog" %% "hedgehog-core" % "0.15.1" % Test,
  "qa.hedgehog" %% "hedgehog-runner" % "0.15.1" % Test
)

Test / fork := true

// Snapshots instead of hard-coded expected values (the user, 2026-10-31:
// "好，引入snapshot4s + munit吧。不要手写硬编码的assertion。"; CONTRIBUTING.md,
// "Snapshot Testing with snapshot4s").
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test
