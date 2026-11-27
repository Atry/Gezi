package gezi.jit

import gezi.jit.NativesTesting.*
import gezi.weakhead.Mode
import gezi.ir.{Configured, Value}

/** The refinement of `Refinement` (jit_strategies.pl, THE REFINEMENT), on
  * outputs written in the IR over the native route's library with the backend's
  * modules: no Prolog test exercised it apart from the native route's
  * compilation, whose schedule the module `strategies` ports; these check the
  * rules of the Prolog module comment one by one. The library terms are members
  * of `JitTesting.libraryTermsFile`, each read by projection, so no name is
  * resolved.
  */
class RefinementTest extends gezi.generatedinputs.FailFastSuite:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private val library = nativesOn
  private val facts = BackendFacts.of(library)
  private val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private def name(key: String): Configured[encoding.type] =
    JitTesting.libraryInstruction[encoding.type](key)

  private def apply(
      function: Configured[encoding.type],
      argument: Configured[encoding.type]
  ): Configured[encoding.type] =
    encoding.application(function, argument)

  private def choice(
      left: Configured[encoding.type],
      right: Configured[encoding.type]
  ): Configured[encoding.type] =
    encoding.choice(left, right)

  private def parallel(
      left: Configured[encoding.type],
      right: Configured[encoding.type]
  ): Configured[encoding.type] =
    encoding.parallel(left, right)

  private def specialization(
      criterion: Configured[encoding.type]
  ): Configured[encoding.type] =
    val filteredZero = parallel(name("zero"), criterion)
    val typedApplication = apply(name("successor"), filteredZero)
    val typed = parallel(typedApplication, criterion)
    val untyped = apply(name("successor"), name("zero"))
    choice(untyped, typed)

  private def refinedAtTheRoot: Configured[encoding.type] =
    val filteredZero = parallel(name("zero"), name("nat_type"))
    val point = choice(name("zero"), filteredZero)
    apply(name("successor"), point)

  test(
    "aSpecializationChoiceOnTheRootsPathBecomesTheFunctionOnAFallbackPoint"
  ) {
    val output = specialization(name("nat_type"))
    val refined = Refinement(encoding).refined(output)
    assert(Configured.same(refined, refinedAtTheRoot))
  }

  test(
    "aSpecializationChoiceOffTheRootsPathIsAlsoUnderTheRangesFallbackPoint"
  ) {
    val choiceOffTheRoot = specialization(name("nat_type"))
    val output = apply(name("successor"), choiceOffTheRoot)
    val refined = Refinement(encoding).refined(output)
    val application = refinedAtTheRoot
    val filteredApplication = parallel(application, name("nat_type"))
    val point = choice(application, filteredApplication)
    val expected = apply(name("successor"), point)
    assert(Configured.same(refined, expected))
  }

  test("aJudgmentBecomesItsTerm") {
    val filtered = parallel(name("zero"), name("nat_type"))
    val judgment = choice(name("zero"), filtered)
    val refined = Refinement(encoding).refined(judgment)
    assert(Configured.same(refined, name("zero")))
  }

  test("noFallbackPointIsWrittenForACriterionThatIsNoDecodingCriterion") {
    val output = specialization(name("successor"))
    val refined = Refinement(encoding).refined(output)
    val expected = apply(name("successor"), name("zero"))
    assert(Configured.same(refined, expected))
  }

  test("theRefinedTermReadsTheOutputsNormalForms") {
    val choiceOffTheRoot = specialization(name("nat_type"))
    val output = apply(name("successor"), choiceOffTheRoot)
    val refined = Refinement(encoding).refined(output)
    val successor = JitTesting.libraryTerm[encoding.type]("successor")
    val plain = JitTesting.termValue(
      successor(successor(JitTesting.libraryTerm[encoding.type]("zero")))
    )
    val jit = Jit(configurationOf(encoding))
    val reference = normalFormsSpent(
      Mode.TablingWeakHead,
      JitTesting.referenceConfiguration(jit),
      plain,
      normalFormLimit
    ).outcome
    val read = normalFormsSpent(jit, Value.of(refined), normalFormLimit)
    assert(
      JitTesting.sameOutcomes(read.outcome, reference),
      s"${read.outcome} against $reference"
    )
    assert(JitTesting.counts(read.jitState).nativeCalls > 0)
  }
