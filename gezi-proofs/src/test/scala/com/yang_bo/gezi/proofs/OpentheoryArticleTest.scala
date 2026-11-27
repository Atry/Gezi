package com.yang_bo.gezi.proofs

// TODO: OpentheoryArticleTest stood here. Its purpose: the port of the unit `opentheory_article` of
// `gezi/tests/opentheory_article.plt`, over the library [prelude, guard_laws, parallel_types,
// filtered_recursion_naturals]: the renderer of the sides against the encoding written out by hand. (Its other test, the Lean
// module of the expected articles' lines against the committed one, reads no library term and is ExpectedArticlesModuleTest.)
// It named library terms by LibraryFiles.namedInstruction over LibraryFiles.preludeDirectories, a free variable (blacklisted)
// and a table of library files deleted when the library became files reached by paths. Its replacement
// reads the library terms it needs as members of a fixture file under tests/ by projection and composes them with the HOAS case
// of a closed instruction. The deleted code: git show 2908bffd5:lambda_jit/proofs/src/test/scala/lambdajit/proofs/OpentheoryArticleTest.scala.
