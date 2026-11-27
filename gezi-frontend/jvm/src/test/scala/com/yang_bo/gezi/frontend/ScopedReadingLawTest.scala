package com.yang_bo.gezi.frontend

// TODO: ScopedReadingLawTest stood here. Its purpose: the laws of reading a text in the scope of enclosing names
// (`Lambdalattice.termInScope`): a text read in the scope of enclosing names is the text under their abstractions,
// and a text is rejected for its first name that the enclosing names leave free.
// It named library terms by Term.define leaves of HoasGenerators.closedTerm over library names, a free variable
// (blacklisted) and a table of library files deleted when the library became files reached by paths. Its replacement generates lambdalattice text with free names directly, or reads the library terms
// it needs as members of a fixture file under tests/ by projection and composes them with the HOAS case of a
// closed instruction. The deleted code: git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/ScopedReadingLawTest.scala.
