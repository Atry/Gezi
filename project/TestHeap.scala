import sbt.*
import sbt.Keys.*

/** How every project's forked test JVM runs: one JVM at a time (build.sbt,
  * `workerMaxInstances`), its suites in threads, one at a time unless the run
  * asks for more, with the heap the server was started with. Tests run in
  * parallel by threads in a single worker, not by processes, so that the worker
  * may use nearly all the memory.
  *
  * THE PARALLELISM is the run's choice, not the build's, which sets no global
  * munit parallelism: the build runs a JVM's suites one at a time, and a run
  * that wants n threads says so before its command, `set every Test /
  * testForkedParallelism := Some(n)`, within the cores its server may use and
  * its heap.
  *
  * THE HEAP. The small limit of a test is its deadline (FailFastSuite) and its
  * reading budgets, not its heap: a JVM's footprint is large, and a small heap
  * would stop the footprint rather than the test. The heap is fixed where the
  * memory is granted: on the command that starts the server,
  * `-Dgezi.testHeap=<size>` (a size `-Xmx` takes, such as `6g`), 4g when it is
  * absent. Several servers may share one memory pool, each granted part of it,
  * so a test JVM's heap must stay within its server's grant: then a test that
  * runs out gets the JVM's own OutOfMemoryError, not a kernel kill of the pool.
  * A `set` of `Test / javaOptions` does not replace it (measured 2026-11-16: a
  * `set every … ~=` left the plugin's option in place). FIXME (2026-11-16):
  * https://github.com/Atry/private-overlay/issues/2003 the heap is to let the
  * short-task server, which may use every core, run many threads without
  * running out of memory, with a rule of thumb for the heap per thread. It is
  * not measured yet: the 4g default is a choice that fits a grant, not a
  * measurement.
  *
  * The class loader: sbt 2 hands a forked JVM its test classpath through a
  * class loader instead of -cp; tests that start child JVMs from
  * java.class.path (the judge's supervisor and readers) need -cp, which
  * `ClassLoaderLayeringStrategy.Raw` keeps.
  *
  * THE RUN BUDGET's two properties for the test JVM (FailFastSuite), only when
  * the server was started with `-Dgezi.testRunBudget` (the short-task server,
  * whose munit runs are bounded to about 15 s each, for debugging and never a
  * run of every suite): the budget, and the start of the command, one time for
  * every project the command runs (`testRunStarted`, a global task that sbt
  * evaluates once per command), so that the budget bounds the command's tests
  * together. Compiling in the same command counts against it: on the short-task
  * server, compile first, then test. A server without the budget adds neither
  * property, and its tests' options and cache are unchanged. They reach only a
  * forked test JVM, so every JVM project's tests fork.
  */
object TestHeap extends AutoPlugin {

  override def trigger = allRequirements

  object autoImport {

    /** The start of the command, in epoch milliseconds, read by every project's
      * test options under a run budget.
      */
    val testRunStarted =
      taskKey[Long]("The start of the command, for the run budget of the tests")
  }

  import autoImport.*

  /** The test JVM's heap, from the server's `-Dgezi.testHeap`. */
  private val heap: String = sys.props.getOrElse("gezi.testHeap", "4g")

  override def globalSettings: Seq[Setting[?]] = Seq(
    testRunStarted := Def.uncached(System.currentTimeMillis)
  )

  /** Whether the option is one this plugin gives the test JVM (the heap, the
    * collector, the run budget's properties).
    */
  def isTestJvmOption(option: String): Boolean =
    option == "-XX:+UseZGC" || option == s"-Xmx$heap" || option.startsWith(
      "-Dgezi.test."
    )

  override def projectSettings: Seq[Setting[?]] = Seq(
    Test / testForkedParallel := true,
    Test / testForkedParallelism := Some(1),
    Test / classLoaderLayeringStrategy := ClassLoaderLayeringStrategy.Raw,
    // Uncached: sbt 2 keys a cached task by its inputs, and a system property
    // of the server is none, so a cached value kept the heap of the server
    // that first computed it (measured 2026-11-16: -Xmx4g on a server started
    // with -Dgezi.testHeap=3g). On the Test configuration, which the test
    // groups' fork options read (an option set on a test task's scope does not
    // reach them: measured 2026-11-16, a 1 s budget on testSelected's scope
    // let testOnly pass); a configuration that extends Test drops them
    // (TestHeapOutsideJmh).
    Test / javaOptions ++= Def.uncached(Seq("-XX:+UseZGC", s"-Xmx$heap"))
  ) ++ sys.props
    .get("gezi.testRunBudget")
    .toSeq
    .map(budget =>
      Test / javaOptions ++= Def.uncached(
        Seq(
          s"-Dgezi.test.runBudget=$budget",
          s"-Dgezi.test.runStarted=${(Global / testRunStarted).value}"
        )
      )
    )
}

/** sbt-jmh's `Jmh` configuration extends `Test` and so inherits TestHeap's
  * options, which reached every JMH fork, whose `@Fork` owns its JVM's options
  * (found 2026-11-16: `-XX:+UseZGC` beside a benchmark's `-XX:+UseSerialGC`
  * stopped every fork with "Multiple garbage collectors selected"). Every
  * project with JMH drops them from `Jmh / javaOptions`.
  */
object TestHeapOutsideJmh extends AutoPlugin {

  override def trigger = allRequirements

  override def requires = pl.project13.scala.sbt.JmhPlugin

  override def projectSettings: Seq[Setting[?]] = Seq(
    pl.project13.scala.sbt.JmhPlugin.JmhKeys.Jmh / javaOptions := Def.uncached(
      (pl.project13.scala.sbt.JmhPlugin.JmhKeys.Jmh / javaOptions).value
        .filterNot(TestHeap.isTestJvmOption)
    )
  )
}
