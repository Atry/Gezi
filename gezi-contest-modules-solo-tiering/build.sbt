// The settings of solo's tiering module project, those of the build's other projects
// that a module needs: tests fork with the small heap and see the build's
// root. It must not depend on the problem corpora or on the judge
// (project/EntryProjects.scala).
libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Test / fork := true

Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
