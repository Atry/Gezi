import LambdaJit.EndToEndFixtures

/-!
# The axioms of the end-to-end theorem and of its fixtures

`#print axioms` for the end-to-end theorem of module `EndToEnd`, its corollary for sides that read
as terms of the calculus, its form on an import set that `importChecked` accepts, the soundness of
the import equations of each kind, the splitting of a text into its lines (module
`ArticleLines`), the lemma `identity_applied`, and the two theorems of each expected article of
module `EndToEndFixtures`, printed on every build of this module. Recorded 2026-11-16, and 2026-11-17 for
`conversionCheckedDerivable`
(Lean 4.35.0, beta-canonical-residual):

    'LambdaJit.EndToEnd.endToEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.endToEndRead' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.endToEndOfChecked' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.numberedEquationSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.fillEquationSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.bodyEquationSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.etaEquationSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.respellCheckedDerivable' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEnd.conversionCheckedDerivable' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Interpretation.interpretOfAgree' depends on axioms: [propext, Quot.sound]
    'LambdaJit.EndToEnd.Statement.importedSound' depends on axioms: [propext, Quot.sound]
    'LambdaJit.ArticleLines.articleLinesJoin' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.identityAppliedSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.congruenceOnlySound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.congruenceOnlyContextualEquivalence' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.oneLemmaInstanceSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.oneLemmaInstanceContextualEquivalence' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.twoInstancesAndACongruenceSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.twoInstancesAndACongruenceContextualEquivalence' depends on
      axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.etaShapedConstantSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.etaShapedConstantContextualEquivalence' depends on axioms:
      [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, no placeholder of an unfinished
proof, and no `Lean.ofReduceBool`, since the fixtures are evaluated by the kernel
(`decide +kernel`), not by compiled code.
-/

#print axioms LambdaJit.EndToEnd.endToEnd
#print axioms LambdaJit.EndToEnd.endToEndRead
#print axioms LambdaJit.EndToEnd.endToEndOfChecked
#print axioms LambdaJit.EndToEnd.numberedEquationSound
#print axioms LambdaJit.EndToEnd.fillEquationSound
#print axioms LambdaJit.EndToEnd.bodyEquationSound
#print axioms LambdaJit.EndToEnd.etaEquationSound
#print axioms LambdaJit.EndToEnd.respellCheckedDerivable
#print axioms LambdaJit.EndToEnd.conversionCheckedDerivable
#print axioms LambdaJit.Interpretation.interpretOfAgree
#print axioms LambdaJit.EndToEnd.Statement.importedSound
#print axioms LambdaJit.ArticleLines.articleLinesJoin
#print axioms LambdaJit.EndToEndFixtures.identityAppliedSound
#print axioms LambdaJit.EndToEndFixtures.congruenceOnlySound
#print axioms LambdaJit.EndToEndFixtures.congruenceOnlyContextualEquivalence
#print axioms LambdaJit.EndToEndFixtures.oneLemmaInstanceSound
#print axioms LambdaJit.EndToEndFixtures.oneLemmaInstanceContextualEquivalence
#print axioms LambdaJit.EndToEndFixtures.twoInstancesAndACongruenceSound
#print axioms LambdaJit.EndToEndFixtures.twoInstancesAndACongruenceContextualEquivalence
#print axioms LambdaJit.EndToEndFixtures.etaShapedConstantSound
#print axioms LambdaJit.EndToEndFixtures.etaShapedConstantContextualEquivalence
