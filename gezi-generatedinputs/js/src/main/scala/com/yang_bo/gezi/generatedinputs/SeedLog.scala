package com.yang_bo.gezi.generatedinputs

/** The log of the seeds `GeneratedProperties` draws under Scala.js, in place of
  * `gezi-generatedinputs/jvm/src/main/scala/com/yang_bo/gezi/generatedinputs/SeedLog.scala`,
  * whose `java.util.logging` Scala.js's Java library lacks: the message on
  * Node.js's standard error, where the test run's output goes.
  */
object SeedLog:

  /** Writes the message to the standard error. */
  def logged(message: String): Unit = System.err.println(message)
