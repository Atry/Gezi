package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.frontend.ProgramPurity
import gezi.ir.Instruction
import gezi.generatedinputs.GeneratedProperties

/** The laws of `ProgramPurity.pure` on generated terms: a term built of
  * variables, abstractions and applications only is pure, and a term with a
  * choice, a parallel or a constant at any
  * position is not. Its purpose is to catch an impure term read as pure,
  * which would give traps to a program whose reference is not proved
  * complete, or a pure term read as impure, which would withhold them.
  */
class ProgramPurityLawTest extends GeneratedProperties:

  /** An instruction for the constants: the interned identity. */
  private val constantInstruction: Instruction =
    Defunctionalization.thunkInstruction(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))

  private val variables: Gen[DeBruijnTerm] = Gen.int(Range.constant(0, 3)).map(DeBruijnTerm.Variable(_))

  /** Pure terms of at most the depth. */
  private def pureTerms(depth: Int): Gen[DeBruijnTerm] =
    if depth == 0 then variables
    else
      Gen.choice1(
        variables,
        pureTerms(depth - 1).map(DeBruijnTerm.Lambda(_)),
        for
          function <- pureTerms(depth - 1)
          argument <- pureTerms(depth - 1)
        yield DeBruijnTerm.Apply(function, argument)
      )

  /** A choice of two or three members, a parallel or a constant, its
    * members pure. A choice has no one-member form: a chain of one member is
    * that member.
    */
  private def impureNodes(depth: Int): Gen[DeBruijnTerm] =
    Gen.choice1(
      pureTerms(depth).list(Range.constant(2, 3)).map(members => DeBruijnTerm.nestedChoice(members.toVector)),
      for
        left <- pureTerms(depth)
        right <- pureTerms(depth)
      yield DeBruijnTerm.Parallel(left, right),
      Gen.constant(DeBruijnTerm.Constant(constantInstruction))
    )

  /** Terms of at most the depth with an impure node at a generated
    * position, under abstractions and on either side of applications.
    */
  private def impureTerms(depth: Int): Gen[DeBruijnTerm] =
    if depth == 0 then impureNodes(0)
    else
      Gen.choice1(
        impureNodes(depth - 1),
        impureTerms(depth - 1).map(DeBruijnTerm.Lambda(_)),
        for
          function <- impureTerms(depth - 1)
          argument <- pureTerms(depth - 1)
        yield DeBruijnTerm.Apply(function, argument),
        for
          function <- pureTerms(depth - 1)
          argument <- impureTerms(depth - 1)
        yield DeBruijnTerm.Apply(function, argument)
      )

  property("a term of variables, abstractions and applications is pure") {
    for term <- pureTerms(5).forAll
    yield Result.assert(ProgramPurity.pure(term)).log(s"read as impure: $term")
  }

  property("a term with a choice, a parallel or a constant anywhere is not pure") {
    for term <- impureTerms(5).forAll
    yield Result.assert(!ProgramPurity.pure(term)).log(s"read as pure: $term")
  }

  /** A variable arguments partial function of a generated literal applied to
    * the literal's bits and to further arguments, its body and the arguments
    * drawn pure or not: the redex `pure` contracts.
    */
  private def literalApplications(depth: Int): Gen[DeBruijnTerm] =
    for
      written <- Gen.string(Gen.alphaNum, Range.linear(0, 3))
      body <- Gen.choice1(pureTerms(depth), impureTerms(depth))
      later <- Gen.choice1(pureTerms(depth), impureTerms(depth)).list(Range.linear(0, 2))
    yield
      val literal = Literal.text(written)
      (Literals.arguments(literal) ++ later).foldLeft(Literals.partialFunction(literal, body))(DeBruijnTerm.Apply(_, _))

  /** A closed term: the term under four abstractions, which bind the
    * generated variables.
    */
  private def closedTerms(depth: Int): Gen[DeBruijnTerm] =
    Gen
      .choice1(pureTerms(depth), impureTerms(depth), literalApplications(depth - 1))
      .map(term => (1 to 4).foldLeft(term)((body, _) => DeBruijnTerm.Lambda(body)))

  // Purpose: catch the IR check disagreeing with the readback's, which is its definition: a redex of a bit missed on
  // the IR (traps withheld) or contracted where the readback has none (traps given to an impure program).
  property("the purity of an instruction is the purity of its readback") {
    for term <- closedTerms(4).forAll
    yield
      val instruction = Defunctionalization.thunkInstruction(term)
      Result.diff(ProgramPurity.pureInstruction(instruction), ProgramPurity.pure(Defunctionalization.instructionTerm(instruction)))(_ == _)
  }

  // Purpose: catch a purity check that walks a shared instruction at each of its occurrences, whose tree here has 2^40
  // copies of the closed term at its leaves.
  property("the purity of a program sharing a closed term 2^40 times is decided at the size of its graph") {
    for term <- closedTerms(4).forAll
    yield
      val leaf = Defunctionalization.thunkInstruction(term)
      val shared = (1 to 40).foldLeft(leaf)((below, _) => Instruction.Apply(below, below))
      Result.diff(ProgramPurity.pureInstruction(shared), ProgramPurity.pureInstruction(leaf))(_ == _)
  }

  // Purpose: catch the IR check missing the contraction of a bit (each bit's miss is top, which holds a parallel), which
  // would withhold the traps of every program that uses the library's markers.
  property("a partial function of a literal applied to its literal, its body and later arguments pure, is pure on the IR") {
    for
      written <- Gen.string(Gen.alphaNum, Range.linear(1, 3)).forAll
      body <- pureTerms(4).forAll
      later <- pureTerms(4).list(Range.linear(0, 2)).forAll
    yield
      val literal = Literal.text(written)
      val applied = (Literals.arguments(literal) ++ later).foldLeft(Literals.partialFunction(literal, body))(DeBruijnTerm.Apply(_, _))
      Result.assert(ProgramPurity.pureInstruction(Defunctionalization.thunkInstruction((1 to 4).foldLeft(applied)((term, _) => DeBruijnTerm.Lambda(term)))))
  }
