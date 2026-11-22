import sbt.*
import sbt.Keys.*

/** A postcondition of a project's test compilation: a project with test
  * sources has test classes. A worktree whose first full compilation ran out
  * of memory went on taking `weakhead`'s test classes as an empty directory
  * from sbt 2's disk cache, every later `Test/compile` reporting success
  * from the cache, and the empty classes surfaced only as a
  * `ClassNotFoundException` in another project's tests. The check makes
  * such a result fail at the compilation that took it, naming the remedy.
  * MEASURED 2026-11-20 (sbt 2.1.0-RC3, the main checkout): with the files
  * under `weakhead`'s test class directory deleted, `weakhead/Test/compile`
  * reported success from the cache and restored none of them; with this
  * check it fails, and `weakhead/Test/clean` then `Test/compile` restored
  * the 96 classes.
  */
object TestClassesPresent extends AutoPlugin {

  override def trigger = allRequirements

  override def requires = plugins.JvmPlugin

  override def projectSettings: Seq[Setting[?]] = Seq(
    Test / compile := Def.uncached {
      val analysis = (Test / compile).value
      val testSources = (Test / sources).value.filter(source => source.getName.endsWith(".scala") || source.getName.endsWith(".java"))
      val classes = (Test / classDirectory).value
      if (testSources.nonEmpty && (classes ** "*.class").get().isEmpty)
        throw new MessageOnlyException(
          s"${thisProject.value.id} has ${testSources.size} test sources and no test class under $classes: " +
            s"a test compilation's result taken empty, possibly from the disk cache (https://github.com/Atry/private-overlay/issues/1769); " +
            s"run ${thisProject.value.id}/Test/clean and compile again"
        )
      analysis
    }
  )
}
