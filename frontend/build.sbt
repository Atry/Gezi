enablePlugins(Snapshot4sPlugin)

// A Scala 2 option sbt-best-practice adds, which Scala 3 ignores with a
// warning.
scalacOptions -= "-Xcheckinit"

Test / scalacOptions -= "-Xcheckinit"

libraryDependencies += "org.scalameta" %% "munit" % "1.3.6" % Test

// The parser combinators of the lambdalattice reader (the user, 2026-11-09:
// "Please migrate the parsers all to Parsley"): Parsley's machine keeps its
// stack on the heap, so a term 100,000 deep reads without the JVM stack
// (measured on 2026-11-09 on a 1 MB thread stack, where cats-parse,
// fastparse, parboiled2 and scala-parser-combinators overflowed at 1,000 to
// 10,000). 4.6.2 is the latest stable release; 5.0 is a milestone.
libraryDependencies += "com.github.j-mie6" %% "parsley" % "4.6.2"

// The CBOR encoder of literals
// (https://github.com/Atry/private-overlay/issues/1514, section 2.4, and its principle P7, the user, 2026-11-16:
// "我认为我们最好不要自己解析CBOR literal，我们的解析器应该只识别出CBOR的范围，然后找
// 一个现有的库解析。"; "因为我想支持Scala.js，所以别的JVM的库不太行"): the reader of the
// diagnostic notation builds borer's data model, and borer writes its bytes.
// Pure Scala, for the JVM, Scala.js and Scala Native; built with Scala 3.3.8.
libraryDependencies += "io.bullet" %% "borer-core" % "1.18.0"

// Snapshots instead of hard-coded expected values (the user, 2026-10-31:
// "好，引入snapshot4s + munit吧。不要手写硬编码的assertion。"; CONTRIBUTING.md,
// "Snapshot Testing with snapshot4s"). Its munit module declares munit
// 1.3.4, which the 1.3.6 above supersedes within the series.
libraryDependencies += "com.siriusxm" %% "snapshot4s-munit" % "0.2.11" % Test

Test / fork := true

// Tests that read the files of Gezi find them from the build's root, the
// parent of this project's directory.
Test / javaOptions += s"-Dgezi.buildRoot=${baseDirectory.value.getParentFile}"
