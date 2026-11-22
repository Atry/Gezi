package gezi.jmh

/** The JMH benchmarks of Gezi's pipeline and of the classic
  * Hindley-Milner reference, run through sbt-jmh (`CONTRIBUTING.md`,
  * "Timings are JMH benchmarks": a timing written by hand on the JVM falls
  * into its many traps, so the harness owns forks, warm-up and measurement):
  * one benchmark per stage of
  * `gezi.programfamilies.Pipeline` (`PipelineBenchmarks`) and one for
  * `gezi.programfamilies.ClassicHindleyMilner.programType`
  * (`ClassicHindleyMilnerBenchmark`), on the eight size families of
  * `Pipeline.sizeFamilies`; and one for the native solver of each natively
  * solved contest family (`NativeSolverBenchmark`), the family's yardstick.
  * The inputs are built in a trial's setup (`LibraryInput`, `ItemInput`,
  * `NativeSolverInput`) and are not timed. The warm-up of each benchmark
  * class is set from the readings of its warm-up iterations, as its Scaladoc
  * says. This package holds
  * benchmarks only; what they run is the code of `gezi.programfamilies`
  * and `gezi.contest.corpora.reductions`.
  */
package object pipeline
