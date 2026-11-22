// The sources of `locations` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section
// 6.5, "构建"), which `frontend-js` depends on as `frontend` does.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "locations" / "src" / "main" / "scala"
