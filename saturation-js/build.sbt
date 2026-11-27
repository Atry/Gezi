// Saturation's higher-order matching compiled for Scala.js
// (https://github.com/Atry/private-overlay/issues/1497, section 6.9, step 2):
// `HigherOrderMatching`, which depends on `egraph` and `ir` alone, so that the
// trace player replays a backward higher-order conversion with the matching
// the saturator runs, with `ConstantStorageStop`, the round's stop it reads,
// which depends on `egraph` alone. The rest of `saturation` depends on
// `ematching` and is not compiled here; `StopSignal` is compiled into
// `hotspot-js`.
enablePlugins(ScalaJSPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

Compile / unmanagedSources +=
  baseDirectory.value.getParentFile / "saturation" / "src" / "main" / "scala" / "gezi" / "saturation" / "HigherOrderMatching.scala"

Compile / unmanagedSources +=
  baseDirectory.value.getParentFile / "saturation" / "src" / "main" / "scala" / "gezi" / "saturation" / "ConstantStorageStop.scala"
