package com.yang_bo.gezi.strategies

// TODO: HindleyMilnerBaselineTest stood here. Its purpose: the port of `gezi/tests/hindley_milner_baseline.plt`: the HM
// baseline on the e-graph saturated to one least fixed point, on native_types and hindley_milner_unions, the root's judgments
// read as types and compared with HM's verdicts by `FixpointVerdicts`, and the front end's counts per element.
// It named library terms by Term.define, LibraryFiles.programNames, StrategyTesting.programInput and
// FixpointVerdicts.judgedTypes, a free variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
// Its replacement reads the library terms it needs as members of
// a fixture file under tests/ by projection and composes them with the HOAS case of a closed instruction.
// The deleted code: git show 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/HindleyMilnerBaselineTest.scala.
