package gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Property
import hedgehog.Result
import hedgehog.core.OK
import hedgehog.core.PropertyConfig
import hedgehog.core.Seed
import hedgehog.core.SuccessCount
import hedgehog.runner.SeedSource
import hedgehog.runner.Test
import scala.concurrent.Future

/** Property tests in a munit suite: a law checked by Hedgehog on generated
  * inputs (`CONTRIBUTING.md`, "Tests").
  *
  * WHY NOT `hedgehog.munit.HedgehogSuite`: that suite mixes in
  * `HedgehogAssertions`, whose `assertEquals` and the rest return a Hedgehog
  * `Result` instead of throwing. In an ordinary munit `test` of such a suite
  * the result is discarded, so a false `assertEquals(1 + 1, 3)` passes
  * silently (measured on 2026-10-31 with hedgehog-munit 0.15.1 and munit
  * 1.3.6: one failure out of a false property and a false munit assertion).
  * This trait keeps munit's assertions as they are and runs a property with
  * Hedgehog's core, failing the munit test with Hedgehog's report, which
  * shows the shrunk counterexample and the seed.
  *
  * The seed is Hedgehog's: the environment variable `HEDGEHOG_SEED` when it
  * holds a number, so that a failure is replayed by setting it to the seed
  * the report prints, and the clock otherwise, so that every run draws other
  * inputs. A test whose output is recorded uses a fixed seed instead
  * (`SeededSnapshots`).
  */
trait GeneratedProperties extends gezi.generatedinputs.FailFastSuite:

  /** A munit test that checks the property with
    * `GeneratedProperties.defaultConfiguration` (20 passing inputs, sizes
    * growing from small to large), changed by `configured`.
    */
  def property(
      name: String,
      configured: PropertyConfig => PropertyConfig = identity
  )(law: => Property)(using munit.Location): Unit =
    stoppableProperty(name, configured)(_ => law)

  /** `property` whose law receives the test's stop request (the read-only
    * future of `stoppableTest`), to hand to the computations it runs.
    */
  def stoppableProperty(
      name: String,
      configured: PropertyConfig => PropertyConfig = identity
  )(law: Future[Unit] => Property)(using munit.Location): Unit =
    stoppableTest(name) { stopped =>
      val seedSource = SeedSource.fromEnvOrTime()
      // The seed is logged before the check, not only in the failure's report:
      // an Error such as OutOfMemoryError escapes `Property.check` before any
      // report is rendered, and a run of BaselineJitEvaluatorLawTest on
      // 2026-11-09 exhausted its heap that way with a seed nobody could replay.
      SeedLog.logged(s"${getClass.getName} / $name: ${seedSource.renderLog}")
      val propertyTest = Test(name, GeneratedProperties.untilStopped(stopped)(law(stopped)))
      val report = Property.check(
        configured(GeneratedProperties.defaultConfiguration),
        propertyTest.result,
        Seed.fromLong(seedSource.seed)
      )
      if report.status != OK then
        fail(
          Test.renderReport(getClass.getName, propertyTest, report, ansiCodesSupported = false) +
            "\n" + seedSource.renderLog
        )
    }

/** The default configuration of `GeneratedProperties.property`; the seeds it
  * draws are logged by `SeedLog`.
  */
object GeneratedProperties:

  /** Hedgehog's default configuration with 20 passing inputs instead of 100.
    * Tests fail fast (`CONTRIBUTING.md`, "Tests fail fast"). 20 still spans every size: Hedgehog's `Property.check`
    * (hedgehog-core 0.15.1, `PropertyT.scala`) raises the size by
    * 100 / testLimit after each input, so 20 inputs draw at sizes 5, 10, ...,
    * 100, as 100 inputs draw at 1, 2, ..., 100. A property that needs more
    * inputs (a `cover` threshold, a rare case) sets its own `testLimit` at
    * its site, with the reason.
    */
  val defaultConfiguration: PropertyConfig = PropertyConfig.default.copy(testLimit = SuccessCount(20))

  /** The property that, for each input Hedgehog draws, first reads the stop
    * request and, when it has been made, runs nothing (an input that passes
    * at once) instead of `law`. The deadline of a test fails the test but
    * stops no thread (`FailFastSuite.bounded`), so an overrunning property
    * that kept drawing would run all its inputs on its daemon thread and take
    * the processors of the tests after it; with this read before every input,
    * at most the input in progress runs on after the request. The request is
    * read when the input is drawn, not when the property is built: a `Gen`'s
    * `map` function runs at each draw.
    */
  def untilStopped(stopped: Future[Unit])(law: Property): Property =
    for
      stopRequested <- Gen.constant(()).map(_ => stopped.isCompleted).forAll
      result <- if stopRequested then Gen.constant(Result.success).forAll else law
    yield result
