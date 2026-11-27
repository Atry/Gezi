// Scala.js, for the trace player: the projects whose sources are
// compiled to JavaScript as well, and the player `trace-player`. 1.22.0 is
// the first release with a build for sbt 2 (sbt-scalajs_sbt2_3 on Maven
// Central, 2026-11-09). sbt-crossproject 1.4.0 supports sbt 2.0.6+ and this
// Scala.js plugin version.
addSbtPlugin("org.portable-scala" % "sbt-scalajs-crossproject" % "1.4.0")
addSbtPlugin("org.scala-js" % "sbt-scalajs" % "1.22.0")
