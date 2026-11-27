package gezi.standardlibrary

// TODO: StandardLibraryTest stood here. Its purpose: the port of `gezi/tests/standard_library.plt`: the loader of the
// library files and the declarations `lemma`, `native` and the combinator properties, on prelude, on prelude with the
// knowledge files compiled with it, and on small valid and malformed libraries of `tests/standard_library_fixtures`.
// It named library terms by LibraryFiles.namedInstruction and read libraries by LibraryFiles.compiledDeclaring, a free
// variable (blacklisted) and a table of library files deleted when the library became files reached by paths. Its replacement reads the library terms it needs as members of a fixture file under tests/ by projection and
// composes them with the HOAS case of a closed instruction.
// The deleted code: git show 2908bffd5:lambda_jit/standardlibrary/src/test/scala/lambdajit/standardlibrary/StandardLibraryTest.scala.
