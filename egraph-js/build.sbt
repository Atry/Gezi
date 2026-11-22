// The sources of `egraph` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section 6.9, step 2):
// the graph on which the trace player runs saturation's higher-order matching
// to replay a backward higher-order conversion.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "egraph" / "src" / "main" / "scala"
