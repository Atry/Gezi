package com.yang_bo.gezi.programfamilies

// TODO: ClassicHindleyMilnerTest stood here. Its purpose: the classic Hindley-Milner reference against the types the Prolog's
// `program_type/2` gave the same programs (`src/test/references/classic_types.tsv`), and 200 closed programs drawn over the
// table's names from a fixed seed (`GeneratedProgram`): their types as a snapshot, and three laws on them.
// It named library terms by Term.define, of the names of the type table and of a name outside it, a free variable
// (blacklisted) and a table of library files deleted when the library became files reached by paths.
// Its replacement reads the library terms it needs as members of a fixture file under tests/ by projection and composes them
// with the HOAS case of a closed instruction.
// The deleted code: git show 2908bffd5:lambda_jit/programfamilies/src/test/scala/lambdajit/programfamilies/ClassicHindleyMilnerTest.scala.
