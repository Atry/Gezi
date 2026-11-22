// The sources of `frontend` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section
// 6.5, "构建"), for the trace player: every source of `frontend`, none of
// which needs the JVM since the directory loader left it. Its tests are
// `frontend`'s generators of test inputs only (the package
// gezi.generatedinputs of frontend's tests), which the player's tests
// reach with test->test.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

// The Scala.js build of the parser combinators `frontend` uses, at its
// version (frontend/build.sbt); `%%` names the artifact of the platform
// (generatedinputs-js/build.sbt).
libraryDependencies += "com.github.j-mie6" %% "parsley" % "4.6.2"

// The Scala.js build of the CBOR encoder of literals `frontend` uses, at its
// version (frontend/build.sbt): borer-core_sjs1_3 1.18.0 is built with
// Scala.js 1.22.0, the version of project/sbt-scalajs.sbt.
libraryDependencies += "io.bullet" %% "borer-core" % "1.18.0"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "frontend" / "src" / "main" / "scala"

Test / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "frontend" / "src" / "test" / "scala" / "gezi" / "generatedinputs"
