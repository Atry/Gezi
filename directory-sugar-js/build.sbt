// The directory sugar for Scala.js (https://github.com/Atry/private-overlay/issues/1497,
// section 6.5, "构建"): none of `directory-sugar`'s sources,
// which read the file system, but this project's own DirectoryTree.scala,
// whose `expansion` the weak head reaches and a trace never calls.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"
