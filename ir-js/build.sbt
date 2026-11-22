// The sources of `ir` compiled for Scala.js (https://github.com/Atry/private-overlay/issues/1497,
// section 6.5, "构建"), for the trace player. Every source
// of `ir` but its Canonicalization.scala, whose Caffeine weak interner has
// no Scala.js build; this project's own Canonicalization.scala, a pool of
// weak references, stands in its place.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "ir" / "src" / "main" / "scala"

Compile / unmanagedSources := {
  val jvmOnly = Set(
    baseDirectory.value.getParentFile / "ir" / "src" / "main" / "scala" / "gezi" / "ir" / "Canonicalization.scala"
  )
  val sources = (Compile / unmanagedSources).value
  assert(jvmOnly.subsetOf(sources.toSet), s"the JVM-only sources $jvmOnly are not all sources of ir")
  sources.filterNot(jvmOnly.contains)
}

// The tests of `ir`, run on Node.js: InterningLawTest checks that a term built
// again is the very object of the term, which under Scala.js is this
// project's pool's work.
Test / unmanagedSourceDirectories += baseDirectory.value.getParentFile / "ir" / "src" / "test" / "scala"
