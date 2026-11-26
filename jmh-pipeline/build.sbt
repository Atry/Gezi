enablePlugins(JmhPlugin)

// The snapshot of the compiled run's deterministic counts
// (`CompiledRunCountsTest`).
enablePlugins(Snapshot4sPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// Snapshots instead of hard-coded expected values (the user, 2026-10-31:
// "好，引入snapshot4s + munit吧。不要手写硬编码的assertion。"; CONTRIBUTING.md,
// "Snapshot Testing with snapshot4s"). Its munit module declares munit
// 1.3.4, which the 1.3.6 above supersedes within the series.
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

// JMH forks each trial's JVM with the arguments of the JVM that runs it, so
// the runner is forked, not run in sbt's own JVM, and gets the options of the
// tests, the configuration Jmh extending Test: the heap of 256 MB and the
// property gezi.buildRoot, which the inputs are read by (JMH's
// "# VM options" line shows them). The benchmarks' `@Fork` appends the heap
// and the serial collector.
//
Test / fork := true

Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"

publish / skip := true

// sbt 2 (read in the 2.0.12 sources, confirmed on this build's 2.1.0-RC3) runs
// `run` on the client side by default (`run / clientSide`) when the command
// comes from `sbt --client`: sbtn then starts its own
// worker JVM, whose java.class.path holds only the worker and which loads the
// project classpath through a class loader. JMH forks each trial with -cp
// taken from java.class.path, so every fork fails with "Could not find or
// load main class org.openjdk.jmh.runner.ForkedMain". With clientSide false
// the runner is forked from the server, inside the server's slice and CPU set,
// with the full classpath on -cp.
Jmh / run / clientSide := false

Jmh / run / fork := true
