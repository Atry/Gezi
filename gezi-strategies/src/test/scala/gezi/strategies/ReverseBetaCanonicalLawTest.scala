package gezi.strategies

// TODO: ReverseBetaCanonicalLawTest stood here. Its purpose: reverse beta spells its abstraction as the front end does: for a
// term T that holds the names G1 to Gn, the abstraction of `ReverseBeta.redex(T, names)` is the instruction the front end makes
// of `λx1 ... λxn. T[G1 := x1, ..., Gn := xn]`, so that an emission that numbers the slots otherwise is caught.
// It named its opaque leaves by Term.define and HoasGenerators.openTerm over the name "named", a free variable (blacklisted)
// and a table of library files deleted when the library became files reached by paths. Its replacement
// takes its opaque leaves by the HOAS case of a closed instruction.
// The deleted code: git show 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/ReverseBetaCanonicalLawTest.scala.
