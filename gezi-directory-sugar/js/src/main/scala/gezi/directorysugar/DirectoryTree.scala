package gezi.directorysugar

import gezi.ir.Instruction

/** The directory sugar under Scala.js, in place of
  * `gezi-directory-sugar/jvm/src/main/scala/gezi/directorysugar/DirectoryTree.scala`,
  * which reads directories and files with `java.nio.file`, a package Scala.js's
  * Java library lacks. The weak-head evaluator compiled for the trace player
  * (`weakhead-core-js`) calls `expansion` on a URI node; a trace has none,
  * since its terms are written as the front end reads them and the surface
  * syntax has no URI node, so the call never happens there.
  */
object DirectoryTree:

  /** No expansion under Scala.js: throws `UnsupportedOperationException`. */
  def expansion(node: Instruction): Instruction =
    throw UnsupportedOperationException(s"no file system to expand the URI node $node under Scala.js")
