// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Test / fork := true

// Tests that read the files of Gezi, such as the standard library,
// find them from the build's root, the parent of this project's directory.
Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
