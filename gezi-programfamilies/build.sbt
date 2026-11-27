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

// The tests' heap is TestHeap's (project/TestHeap.scala). The runs' heap is
// 400 MB, the algorithm's measured cost, set by CriterionFourTest's list
// item, whose list-1024 graph has 94,371 classes; the same item is the
// largest live set of the tests. Since 2026-11-13 the extraction keeps each class's least finite
// tree (`com.yang_bo.gezi.extraction.CountedExtraction`, THE DEFINITION) in three
// passes, the costs, the least entries whatever their cost and the entries
// at their costs, so that at the end of the last the first pass's costs,
// the least entries and the last pass's entries are live together, each
// with its classes' costs (`ModuleCost`). Measured 2026-11-13 (the item
// alone, taskset -c 0,1, the test JVM's live heap read by jcmd
// GC.class_histogram every 10 s): at -Xmx304m it failed with
// OutOfMemoryError at 51 s, the live heap 311 MB at the last reading; at
// 352m it failed at 55 s, 358 MB; at 376m it passed in 33 s, 339 MB at the
// largest reading; at 400m it passed in 31 s, and the whole suite passed in
// 114 s, its largest reading 346 MB. 400 MB is one step above the smallest
// heap that passed, so that the run does not depend on the collector's
// timing at the edge. Before the three passes the heap was 304 MB: the
// largest live set after a collection 253.9 MB on main 2ba4e7da4
// (2026-11-10, JFR jdk.ObjectCountAfterGC), and G1's full collections left
// 262 to 268 MB.
Test / fork := true

// Tests that read the files of Gezi find them from the build's root, the
// parent of this project's directory.
Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"

run / fork := true

run / javaOptions ++= Seq(
  "-Xmx400m",
  s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
)
