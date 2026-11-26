package gezi.directorysugar

import gezi.ir.{Configured, NativeSpecializer}

/** The directory sugar under Scala.js, in place of
  * `directory-sugar/src/main/scala/gezi/directorysugar/DirectoryTree.scala`,
  * which reads directories and files with `java.nio.file`, a package Scala.js's
  * Java library lacks. The weak-head evaluator compiled for the trace player
  * (`weakhead-core-js`) calls `expansionRead` on a URI node; a trace has none,
  * since its terms are written as the front end reads them and the surface
  * syntax has no URI node, so the call never happens there.
  */
object DirectoryTree:

  /** A URI node's expansion, of which none is made under Scala.js. */
  final case class ReadExpansion[C <: NativeSpecializer & Singleton](expansion: Configured[C])

  /** No expansion under Scala.js: throws `UnsupportedOperationException`. */
  def expansion[C <: NativeSpecializer & Singleton](node: Configured[C])(using C): Configured[C] =
    throw UnsupportedOperationException(s"no file system to expand the URI node $node under Scala.js")

  /** No expansion under Scala.js: throws `UnsupportedOperationException`. */
  def expansionRead[C <: NativeSpecializer & Singleton](node: Configured[C], earlier: Option[ReadExpansion[C]])(using C): ReadExpansion[C] =
    throw UnsupportedOperationException(s"no file system to expand the URI node $node under Scala.js")
