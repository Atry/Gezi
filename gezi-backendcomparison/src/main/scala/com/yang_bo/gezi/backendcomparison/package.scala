package com.yang_bo.gezi

/** The backends by name ([[Backends]]), a run's input compiled by one of them
  * ([[RunInput]], [[Compiled]]) and the form of the fixed point its saturation
  * reaches ([[FixedPoint]]). Its tests check on generated programs that the
  * three backends agree.
  *
  * The module depends on `ematching-indexing`, `saturation` and the three
  * backends `ematching-interpretation`, `ematching-closures` and
  * `ematching-bytecode`; `programfamilies` depends on it.
  *
  * TODO: a JMH benchmark (`CONTRIBUTING.md`, "Timings are JMH benchmarks") of
  * the three e-graph matching backends, interpretation
  * (`ematching-interpretation`), closures (`ematching-closures`) and bytecode
  * (`ematching-bytecode`), on inputs generated from `programfamilies`' HOAS
  * program families instead of the deleted Prolog fixtures, to compare their
  * speed. The deleted benchmark, which timed one backend on one fixture item,
  * reads back with
  * `git show 5fcdaf4d7^:lambda_jit/jmh-ematching/src/main/scala/lambdajit/jmh/ematching/BackendBenchmark.scala`.
  */
package object backendcomparison
