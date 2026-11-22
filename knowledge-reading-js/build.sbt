// The sources of `knowledge-reading` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section
// 6.5, "构建"): the generic reader of Scott data under weak head, which
// `rewrite-trace-js` reads a trace's text with (section 6.3, "读").
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "knowledge-reading" / "src" / "main" / "scala"
