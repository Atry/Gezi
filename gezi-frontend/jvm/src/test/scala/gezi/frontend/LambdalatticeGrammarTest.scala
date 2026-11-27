package gezi.frontend

import gezi.ir.Configured
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts

/** The port of `gezi/tests/lambdalattice.plt`, unit
  * `lambdalattice_grammar`: the text syntax of a lambdalattice file.
  */
class LambdalatticeGrammarTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  import DeBruijnTerm.*

  /** An instruction for each name a test refers to; the Prolog test interned a
    * fresh layer for each, and a de Bruijn constant only holds the instruction.
    */
  private val testNames: Map[String, NoFactsTerm] =
    Map("fixpoint" -> NoFacts.opaque("fixpoint"), "true" -> NoFacts.opaque("true"))

  /** The term of a text that binds every name it uses. */
  private def term(text: String): DeBruijnTerm =
    Lambdalattice.term(text)

  /** Five abstractions around the body. */
  private def fiveLambdas(body: DeBruijnTerm): DeBruijnTerm =
    Lambda(Lambda(Lambda(Lambda(Lambda(body)))))

  private def problem(text: String): LambdalatticeProblem =
    intercept[LambdalatticeMalformed](term(text)).problem

  private def syntax(error: SyntaxError, position: Int): LambdalatticeProblem =
    LambdalatticeProblem.Syntax(error, position)

  test("true") {
    assertEquals(term("λt.λ_.t"), Lambda(Lambda(Variable(1))))
  }

  test("cons") {
    assertEquals(
      term("λh.λt.λ_.λc.c h t"),
      Lambda(
        Lambda(
          Lambda(Lambda(Apply(Apply(Variable(0), Variable(3)), Variable(2))))
        )
      )
    )
  }

  test("fixpoint") {
    assertEquals(
      term("(λx.λf.f (x x f)) (λx.λf.f (x x f))"),
      Apply(
        Lambda(Lambda(Apply(Variable(0), Apply(Apply(Variable(1), Variable(1)), Variable(0))))),
        Lambda(Lambda(Apply(Variable(0), Apply(Apply(Variable(1), Variable(1)), Variable(0)))))
      )
    )
  }

  // A chain of + over two lambdas, with a comment, is the choice of the two
  // lambdas, the one after the + its left side.
  test("mixinNaturalBooleanData") {
    assertEquals(
      term("""(λ_.λx2.λ_.λ_.λ_.x2 (λ_.λx7.λ_.λ_.λ_.x7 (λx11.λ_.x11)))
                    + (λ_.λ_.λx15.λ_.λ_.x15 (λ_.λx19.λ_.λ_.λ_.x19 (λ_.λx24.x24))) # a comment
                   """),
      Choice(
        fiveLambdas(Apply(Variable(2), fiveLambdas(Apply(Variable(3), Lambda(Lambda(Variable(0))))))),
        fiveLambdas(Apply(Variable(3), fiveLambdas(Apply(Variable(3), Lambda(Lambda(Variable(1)))))))
      )
    )
  }

  // A name continues over digits: f0 is one name, not f followed by 0, a
  // digit, which starts no token.
  test("aNameContinuesOverAZero") {
    assertEquals(term("λf0.f0"), Lambda(Variable(0)))
  }

  // A + takes the operand after it as the choice's left side and the chain
  // before it as its right side, so a chain nests in its right sides with its
  // members in the reverse of the text's order.
  test("aChainOfChoicesNestsInItsRightSides") {
    assertEquals(
      term("λa.λb.λc.(a + b + c)"),
      Lambda(Lambda(Lambda(Choice(Variable(0), Choice(Variable(1), Variable(2))))))
    )
  }

  test("aChoiceInParenthesesNests") {
    assertEquals(
      term("λa.λb.λc.((a + b) + c)"),
      Lambda(
        Lambda(
          Lambda(
            Choice(Variable(0), Choice(Variable(1), Variable(2)))
          )
        )
      )
    )
    assertEquals(
      term("λa.λb.λc.(a + (b + c))"),
      Lambda(
        Lambda(
          Lambda(
            Choice(Choice(Variable(0), Variable(1)), Variable(2))
          )
        )
      )
    )
  }

  test("aChainOfParallelsNestsToTheLeft") {
    assertEquals(
      term("λa.λb.λc.(a ∥ b ∥ c)"),
      Lambda(
        Lambda(
          Lambda(Parallel(Parallel(Variable(2), Variable(1)), Variable(0)))
        )
      )
    )
  }

  test("applicationBindsTighterThanParallel") {
    assertEquals(
      term("λf.λx.λg.λy.(f x ∥ g y)"),
      Lambda(
        Lambda(
          Lambda(
            Lambda(
              Parallel(
                Apply(Variable(3), Variable(2)),
                Apply(Variable(1), Variable(0))
              )
            )
          )
        )
      )
    )
  }

  // + and ∥ have one precedence and mix in one left-associative chain: each
  // operator takes the chain before it, a ∥ as its left side, a + as its
  // right side.
  test("choiceAndParallelMixInOneChain") {
    assertEquals(
      term("λa.λb.λc.(a ∥ b + c)"),
      Lambda(Lambda(Lambda(Choice(Variable(0), Parallel(Variable(2), Variable(1))))))
    )
    assertEquals(
      term("λa.λb.λc.(a + b ∥ c)"),
      Lambda(Lambda(Lambda(Parallel(Choice(Variable(1), Variable(2)), Variable(0)))))
    )
    assertEquals(
      term("λa.λb.λc.((a ∥ b) + c)"),
      Lambda(Lambda(Lambda(Choice(Variable(0), Parallel(Variable(2), Variable(1))))))
    )
  }

  test("anAbstractionBodyStopsBeforeAChoice") {
    assertEquals(
      term("λx.x + λy.y"),
      Choice(Lambda(Variable(0)), Lambda(Variable(0)))
    )
    assertEquals(
      term("λx.(x + x)"),
      Lambda(Choice(Variable(0), Variable(0)))
    )
  }

  test("defineReference") {
    val parsed = Lambdalattice.term("λx.true x", FreeNames.Allowed)
    assertEquals(parsed, Lambda(Apply(Free("true"), Variable(0))))
    assert(
      Configured.same(
        Defunctionalization.thunkInstruction[NoFacts.type](parsed, testNames),
        Defunctionalization.thunkInstruction[NoFacts.type](Lambda(Apply(Constant(testNames("true")), Variable(0))))
      )
    )
  }

  test("bindingShadowsDefine") {
    assertEquals(Lambdalattice.term("λtrue.true"), Lambda(Variable(0)))
  }

  test("codesAccepted") {
    assertEquals(
      Lambdalattice.term(Vector('λ'.toInt, 'x'.toInt, '.'.toInt, 'x'.toInt)),
      Lambda(Variable(0))
    )
  }

  test("unboundName") {
    assertEquals(problem("λx.y"), LambdalatticeProblem.UnboundName("y"))
  }

  test("underscoreReferenced") {
    assertEquals(problem("λ_._"), LambdalatticeProblem.UnboundName("_"))
  }

  test("unclosedParenthesis") {
    assertEquals(
      problem("(λx.x"),
      syntax(SyntaxError.Expected(Expectation.CloseParenthesis, TokenKind.End), 5)
    )
  }

  test("abstractionAsChoiceOperand") {
    assertEquals(term("(λx.x) + λy.y"), Choice(Lambda(Variable(0)), Lambda(Variable(0))))
  }

  test("abstractionAsParallelOperand") {
    assertEquals(term("(λx.x) ∥ λy.y"), Parallel(Lambda(Variable(0)), Lambda(Variable(0))))
  }

  test("choiceWithoutARightOperand") {
    assertEquals(
      problem("λx.x +"),
      syntax(SyntaxError.Expected(Expectation.Atom, TokenKind.End), 6)
    )
  }

  // A comma stands only inside a literal (an array's or a map's separator),
  // so outside one it is no token.
  test("aCommaOutsideALiteralIsNoToken") {
    assertEquals(
      problem("(λx.x), (λy.y)"),
      syntax(SyntaxError.UnexpectedCharacter(','), 6)
    )
  }

  // U+222A UNION, U+2229 INTERSECTION and U+2205 EMPTY SET, the spellings of
  // the choice, the parallel and the empty choice before 2026-10-04, are no tokens: the spelling is + and ∥ only.
  test("theUnionSignIsNoToken") {
    assertEquals(
      problem("λx.x ∪ x"),
      syntax(SyntaxError.UnexpectedCharacter(0x222a), 5)
    )
  }

  test("theIntersectionSignIsNoToken") {
    assertEquals(
      problem("λx.x ∩ x"),
      syntax(SyntaxError.UnexpectedCharacter(0x2229), 5)
    )
  }

  test("theEmptySetSignIsNoToken") {
    assertEquals(
      problem("λf.f ∅"),
      syntax(SyntaxError.UnexpectedCharacter(0x2205), 5)
    )
  }

  test("uppercaseName") {
    assertEquals(term("λX.X"), Lambda(Variable(0)))
  }

  test("emptyText") {
    assertEquals(
      problem(""),
      syntax(SyntaxError.Expected(Expectation.Atom, TokenKind.End), 0)
    )
  }
