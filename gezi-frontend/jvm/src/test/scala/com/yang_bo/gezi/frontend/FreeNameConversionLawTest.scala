package com.yang_bo.gezi.frontend

// TODO: FreeNameConversionLawTest stood here. Its purpose: converting a locally nameless term with names
// (`Defunctionalization.thunkInstruction(term, names)(using com.yang_bo.gezi.ir.NoFacts)`, `FreeNames.Allowed`, which stays) gives the instruction of
// the term with each free name replaced by the constant of its instruction, so that a conversion does not tell two
// closed subterms apart by the spelling of free names whose instructions are equal.
// It named library terms by Term.define leaves of HoasGenerators.closedTerm over library names, a free variable
// (blacklisted) and a table of library files deleted when the library became files reached by paths. Its replacement generates lambdalattice text with free names directly and converts it with the
// names. The deleted code: git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/FreeNameConversionLawTest.scala.
