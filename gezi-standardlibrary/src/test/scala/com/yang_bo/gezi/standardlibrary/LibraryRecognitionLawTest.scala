package com.yang_bo.gezi.standardlibrary

// TODO: LibraryRecognitionLawTest stood here. Its purpose: the laws of the front-end stage `LibraryRecognition`: on a closed
// program over the library's names and on the same program with every name inlined, the stage leaves the program's IR instruction
// unchanged and gives the same term for both, so that a recognition that changes the program or misses an inlined body is caught.
// It named library terms by Term.define and HoasGenerators.openTerm over the names of the library's files, a free variable
// (blacklisted) and a table of library files deleted when the library became files reached by paths.
// Its replacement reads the library terms it needs as members of a fixture file under tests/ by projection and composes them
// with the HOAS case of a closed instruction.
// The deleted code: git show 2908bffd5:lambda_jit/standardlibrary/src/test/scala/lambdajit/standardlibrary/LibraryRecognitionLawTest.scala.
