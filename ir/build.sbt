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

// The canonicalization pool of instructions and codes (the user,
// 2026-11-01: "不用加进JMH，直接改Caffeine的weak interner"): an instruction is the
// canonical object of its layer, compared by reference and collected when
// unreachable. 3.3.1, released 2026-10-13, the latest release.
libraryDependencies += "com.github.ben-manes.caffeine" % "caffeine" % "3.3.1"
