package com.yang_bo.gezi.programfamilies

/** What the tests of this module share: the two configurations compiled once
  * for the forked test JVM.
  */
object CompiledConfigurations:

  /** Each configuration compiled, by name. */
  lazy val byName: Map[String, CompiledConfiguration] =
    FixedPointLines.compiledConfigurations
