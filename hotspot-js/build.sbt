// The sources of `hotspot` compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section
// 6.5, "构建"), because `weakhead-core` names its interfaces. Every source but
// Forks.scala, the fork and join primitive, which runs its tasks on the JDK's
// virtual thread executor, which Scala.js lacks; and, from `saturation`, its
// StopSignal.scala alone, the one source of `saturation` that `hotspot` and
// `weakhead-core` name (the rest of `saturation` is the e-graph's loop).
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "hotspot" / "src" / "main" / "scala"

Compile / unmanagedSources := {
  val jvmOnly = Set(
    baseDirectory.value.getParentFile / "hotspot" / "src" / "main" / "scala" / "gezi" / "hotspot" / "Forks.scala"
  )
  val sources = (Compile / unmanagedSources).value
  assert(
    jvmOnly.subsetOf(sources.toSet),
    s"the JVM-only sources $jvmOnly are not all sources of hotspot"
  )
  sources.filterNot(jvmOnly.contains) :+
    (baseDirectory.value.getParentFile / "saturation" / "src" / "main" / "scala" / "gezi" / "saturation" / "StopSignal.scala")
}
