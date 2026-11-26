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
moduleName := "gezi-ematching-closures"
publish / skip := false
