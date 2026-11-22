// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

Test / fork := true

// Tests that read the files of Gezi find them from the build's root, the
// parent of this project's directory.
Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
