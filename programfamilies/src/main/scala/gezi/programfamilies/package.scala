package gezi

/** The program families of the two configurations ([[Configurations]]), written
  * in the higher-order abstract syntax over the library's names
  * ([[ProgramFamilies]], [[Configurations]]), and their runs: each
  * configuration's library and orientations compiled once ([[FixedPointRuns]]),
  * a program put through the front end, the graph saturated and the form of its
  * fixed point computed by the module `backendcomparison`. The entry points
  * `FixedPoints` and `CriterionFourCounts` write the fixed point of every item
  * and the counts of each stage ([[StageCountTable]]). The module
  * `jmh-pipeline`'s `PipelineBenchmarks` and `ClassicHindleyMilnerBenchmark`
  * time the pipeline against [[ClassicHindleyMilner]], a classic type inference
  * kept outside the pipeline as a measuring instrument only.
  *
  * The module depends on `standardlibrary`, `strategies`, `orientation` and
  * `backendcomparison`; `jmh-pipeline` depends on it.
  */
package object programfamilies
