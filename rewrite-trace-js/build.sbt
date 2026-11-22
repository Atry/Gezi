// The sources of `rewrite-trace` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section
// 6.5, "构建"): the trace's commands, its reading from text and its replay,
// with which the trace player computes every step's term (section 6.3: the
// file holds only the start and the commands).
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "rewrite-trace" / "src" / "main" / "scala"
