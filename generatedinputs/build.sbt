// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

// The libraries of the tests, which this test-support project takes at
// compile scope and every other project at test scope.
libraryDependencies += "org.scalameta" %% "munit" % "1.3.6"

// Generated inputs (the user, 2026-10-31: "但是不管是law还是 snapshot，我希望输入都
// 是随机生成的。因为编写生成器的过程可以强迫你想清楚你到底想要测试什么"). Hedgehog's
// core and runner only: its munit module's suite replaces munit's assertions
// by ones that return a value, so that a false assertion in an ordinary
// munit test of such a suite passes silently (`GeneratedProperties` says
// how this was measured). The version is pinned: a seeded snapshot is
// reproducible only while the random source and the combinators stay this
// version's.
libraryDependencies ++= Seq(
  "qa.hedgehog" %% "hedgehog-core" % "0.15.1",
  "qa.hedgehog" %% "hedgehog-runner" % "0.15.1"
)

// Snapshots instead of hard-coded expected values (the user, 2026-10-31:
// "好，引入snapshot4s + munit吧。不要手写硬编码的assertion。"). Its munit module
// declares munit 1.3.4, which the 1.3.6 above supersedes within the series.
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11"

// The tests fork, as every JVM project's do: in-process they would run in the
// sbt server's JVM, with its system properties and without the test JVM's
// options (project/TestHeap.scala).
Test / fork := true
