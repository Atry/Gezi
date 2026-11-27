package gezi.frontend

/** The object language written in Scala (HOAS, `Term`): its de Bruijn terms
  * are the ones the lambdalattice text of the same programs gives.
  */
class HigherOrderSyntaxTest extends gezi.generatedinputs.FailFastSuite:

  import Term.*

  private def lambdalattice(text: String): DeBruijnTerm =
    Lambdalattice.term(text)

  private def converted(term: Term): DeBruijnTerm = term.locallyNamelessTerm

  test("anAbstractionIsAScalaFunction") {
    assertEquals(converted(λ(x => x)), lambdalattice("λx.x"))
    assertEquals(converted(λ(k => λ(_ => k))), lambdalattice("λk.λ_.k"))
  }

  test("applicationIsCurried") {
    assertEquals(
      converted(λ(f => λ(x => λ(y => f(x)(y))))),
      lambdalattice("λf.λx.λy.f x y")
    )
    assertEquals(
      converted(λ(x => λ(f => f(x(x)(f)))) (λ(x => λ(f => f(x(x)(f)))))),
      lambdalattice("(λx.λf.f (x x f)) (λx.λf.f (x x f))")
    )
  }

  // A HOAS chain is the IR's right-nested choice of its members in their
  // order, which a file writes with its members in the reverse order.
  test("aChainOfChoicesNestsToTheRight") {
    assertEquals(
      converted(λ(a => λ(b => λ(c => a + b + c)))),
      lambdalattice("λa.λb.λc.(c + b + a)")
    )
  }

  test("aNestedChoiceIsWrittenWithChoice") {
    assertEquals(
      converted(λ(a => λ(b => λ(c => choice(a, b) + c)))),
      lambdalattice("λa.λb.λc.(c + (b + a))")
    )
    assertEquals(
      converted(λ(a => λ(b => λ(c => a + choice(b, c))))),
      lambdalattice("λa.λb.λc.((c + b) + a)")
    )
  }

  test("parallelNestsToTheLeftAndBindsLooserThanApplication") {
    assertEquals(
      converted(λ(a => λ(b => λ(c => a ∥ b ∥ c)))),
      lambdalattice("λa.λb.λc.(a ∥ b ∥ c)")
    )
    assertEquals(
      converted(λ(a => λ(b => λ(c => a ∥ b + c)))),
      lambdalattice("λa.λb.λc.(c + (a ∥ b))")
    )
    assertEquals(
      converted(λ(a => λ(b => λ(c => a + b ∥ c)))),
      lambdalattice("λa.λb.λc.((b ∥ c) + a)")
    )
    assertEquals(
      converted(λ(f => λ(x => λ(g => λ(y => f(x) ∥ g(y)))))),
      lambdalattice("λf.λx.λg.λy.(f x ∥ g y)")
    )
  }

  // TODO: aDefineIsResolvedThroughTheMap and anUnknownDefineIsAnError stood here. Their purpose: a library name
  // in a HOAS term converts to the free name of the same lambdalattice text and resolves to its instruction through
  // the map, and a name the map does not hold is an error. They named library terms by Term.define, a free
  // variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
  // Their replacement reads the library terms it
  // needs as members of a fixture file under tests/ by projection and composes them with the HOAS case of a
  // closed instruction. The deleted code:
  // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/HigherOrderSyntaxTest.scala.

  test("aVariableOutsideItsAbstractionIsAnError") {
    assertEquals(
      intercept[LambdaError](converted(λ(_ => BoundVariable(1)))).reason,
      LambdaErrorReason.VariableOutsideItsAbstraction(1, 1)
    )
  }
