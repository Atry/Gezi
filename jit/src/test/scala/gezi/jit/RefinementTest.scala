package gezi.jit

import gezi.jit.NativesTesting.*
import gezi.weakhead.Mode
import gezi.weakhead.Value
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir

/** The refinement of `Refinement` (jit_strategies.pl, THE REFINEMENT), on
  * outputs written in the IR over the native route's library with the
  * backend's modules: no Prolog test exercised it apart from the native
  * route's compilation, whose schedule the module `strategies` ports; these
  * check the rules of the Prolog module comment one by one. The library
  * terms are members of `JitTesting.libraryTermsFile`, each read by
  * projection, so no name is resolved.
  */
class RefinementTest extends gezi.generatedinputs.FailFastSuite:

  private val library = nativesOn
  private val facts = BackendFacts.of(library)
  private def name(key: String): Instruction =
    JitTesting.libraryTerms.getOrElse(key, throw IllegalArgumentException(s"${JitTesting.libraryTermsFile} has no member $key"))

  /** The instructions of the layers, interned in turn. */
  private final case class Building():
    def layer(found: Layer[Instruction]): (Building, Instruction) = (this, Instruction(found))

  /** The specialization choice of successor zero beside its typed version
    * by the domain and range nat_type, (successor (zero ∥ nat_type)) ∥
    * nat_type, and the parts it is built of.
    */
  private def specialization(start: Building, criterion: Instruction): (Building, Instruction) =
    val (afterFiltered, filteredZero) = start.layer(ir.Parallel(name("zero"), criterion))
    val (afterTyped, typedApplication) = afterFiltered.layer(ir.Apply(name("successor"), filteredZero))
    val (afterRange, typed) = afterTyped.layer(ir.Parallel(typedApplication, criterion))
    val (afterUntyped, untyped) = afterRange.layer(ir.Apply(name("successor"), name("zero")))
    afterUntyped.layer(ir.Choice(untyped, typed))

  /** successor [zero, zero ∥ nat_type], the root's refinement. */
  private def refinedAtTheRoot(start: Building): (Building, Instruction) =
    val (afterFiltered, filteredZero) = start.layer(ir.Parallel(name("zero"), name("nat_type")))
    val (afterPoint, point) = afterFiltered.layer(ir.Choice(name("zero"), filteredZero))
    afterPoint.layer(ir.Apply(name("successor"), point))

  test("aSpecializationChoiceOnTheRootsPathBecomesTheFunctionOnAFallbackPoint") {
    val (built, output) = specialization(Building(), name("nat_type"))
    val refined = Refinement(facts).refined(output)
    val (_, expected) = refinedAtTheRoot(Building())
    assertEquals(refined, expected)
  }

  test("aSpecializationChoiceOffTheRootsPathIsAlsoUnderTheRangesFallbackPoint") {
    val (built, choice) = specialization(Building(), name("nat_type"))
    val (withOutput, output) = built.layer(ir.Apply(name("successor"), choice))
    val refined = Refinement(facts).refined(output)
    val (afterApplication, application) = refinedAtTheRoot(Building())
    val (afterFiltered, filteredApplication) = afterApplication.layer(ir.Parallel(application, name("nat_type")))
    val (afterPoint, point) = afterFiltered.layer(ir.Choice(application, filteredApplication))
    val (_, expected) = afterPoint.layer(ir.Apply(name("successor"), point))
    assertEquals(refined, expected)
  }

  test("aJudgmentBecomesItsTerm") {
    val (afterFiltered, filtered) = Building().layer(ir.Parallel(name("zero"), name("nat_type")))
    val (built, judgment) = afterFiltered.layer(ir.Choice(name("zero"), filtered))
    val refined = Refinement(facts).refined(judgment)
    assertEquals(refined, name("zero"))
  }

  // A filter by a criterion that is no decoding criterion is read by no
  // decode point, so no fallback point is written for it.
  test("noFallbackPointIsWrittenForACriterionThatIsNoDecodingCriterion") {
    val (built, output) = specialization(Building(), name("successor"))
    val refined = Refinement(facts).refined(output)
    val (_, expected) = Building().layer(ir.Apply(name("successor"), name("zero")))
    assertEquals(refined, expected)
  }

  // The refined term equals the output: the JIT reads of it the normal forms
  // the reference reads of the untyped member, successor zero.
  test("theRefinedTermReadsTheOutputsNormalForms") {
    val (built, choice) = specialization(Building(), name("nat_type"))
    val (withOutput, output) = built.layer(ir.Apply(name("successor"), choice))
    val refined = Refinement(facts).refined(output)
    val successor = JitTesting.libraryTerm("successor")
    val plain = JitTesting.termValue(successor(successor(JitTesting.libraryTerm("zero"))))
    val reference = normalFormsSpent(Mode.TablingWeakHead, plain, normalFormLimit).outcome
    val read = normalFormsSpent(Mode.Jit(Jit(configurationOf(library))), refined, normalFormLimit)
    assertEquals(read.outcome, reference)
    assert(JitTesting.counts(read.jitState).nativeCalls > 0)
  }
