// The sources of `generatedinputs` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section
// 6.5, "构建"): the infrastructure of generated test inputs, for the tests
// of the projects compiled for Scala.js, which run on Node.js.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

// The Scala.js builds of the libraries of generatedinputs/build.sbt, at its
// versions, which it explains. Under sbt 2, `%%` names the artifact of the
// project's platform (the setting `platform`, which the Scala.js plugin sets
// to sjs1), so `_sjs1_3`; sbt 1's `%%%` of sbt-platform-deps is absent.
libraryDependencies ++= Seq(
  "org.scalameta" %% "munit" % "1.3.6",
  "qa.hedgehog" %% "hedgehog-core" % "0.15.1",
  "qa.hedgehog" %% "hedgehog-runner" % "0.15.1",
  "com.siriusxm" %% "snapshot4s-munit" % "0.2.11"
)

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "generatedinputs" / "src" / "main" / "scala"

// Every source of `generatedinputs` but its FailFastSuite.scala, whose deadline
// needs threads and blocking, and its SeedLog.scala, whose java.util.logging
// Scala.js lacks; this project's own two files stand in
// their place.
Compile / unmanagedSources := {
  val jvmOnly = Set(
    baseDirectory.value.getParentFile / "generatedinputs" / "src" / "main" / "scala" / "gezi" / "generatedinputs" / "FailFastSuite.scala",
    baseDirectory.value.getParentFile / "generatedinputs" / "src" / "main" / "scala" / "gezi" / "generatedinputs" / "SeedLog.scala"
  )
  val sources = (Compile / unmanagedSources).value
  assert(jvmOnly.subsetOf(sources.toSet), s"the JVM-only sources $jvmOnly are not all sources of generatedinputs")
  sources.filterNot(jvmOnly.contains)
}
