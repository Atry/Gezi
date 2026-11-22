enablePlugins(Snapshot4sPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

// WartRemover's Scala 3 traverser API, the base the custom warts of this
// project extend (https://www.wartremover.org/doc/ , "Custom wart"); the
// version is sbt-wartremover's (project/sbt-wartremover.sbt), and the
// library is cross-built for the full Scala version.
libraryDependencies += "org.wartremover" % "wartremover" % "3.6.3" cross CrossVersion.full

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// Snapshots instead of hard-coded expected values (CONTRIBUTING.md, "Snapshot
// Testing with snapshot4s").
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

// The warts of this project cannot check this project: the build-wide custom
// warts load this project's classes, so this project is compiled with the
// built-in warts alone.
wartremoverClasspaths := Seq.empty

wartremoverErrors := Seq(Wart.Var, Wart.MutableDataStructures, Wart.While)

Test / fork := true

publish / skip := true

// The test compiles the planted sources, which it reads from this project's
// directory.
Test / javaOptions += s"-Dgezi.wartsRoot=${baseDirectory.value}"
