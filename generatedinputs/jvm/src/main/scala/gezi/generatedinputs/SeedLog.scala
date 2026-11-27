package gezi.generatedinputs

/** The log of the seeds `GeneratedProperties` draws, on the JVM through
  * `java.util.logging`. The project `generatedinputs-js` compiles its own
  * object of this name in place of this file, since Scala.js's Java library
  * has no `java.util.logging`.
  */
object SeedLog:

  private val logger: java.util.logging.Logger = java.util.logging.Logger.getLogger(classOf[GeneratedProperties].getName)

  /** Logs the message at the level `INFO`. */
  def logged(message: String): Unit = logger.info(message)
