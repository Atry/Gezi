import LambdaJit.EndToEnd

/-!
# The steps of a round certificate

A round certificate is a declaration whose type is `EquationSound signature input output`, the
round's input and output contextually equivalent (DdLP96's Definition 14) under every valuation,
and whose value is a tree of the theorems of this module applied to explicit arguments: the
writer of the certificate writes
the proof the article writer builds, node by node, in Lean's export format, and the checker
(nanoda, or Lean's kernel) checks it. No OpenTheory reader runs: every term, the signature and
each substitution are Lean data in the certificate.

Each theorem takes every argument explicitly, so the writer elaborates nothing: an import is
accepted by evaluation (`imported`, its `checked` argument `Eq.refl true`), and the others are
the rules of `Article.Derivable` restated over `EquationSound`.
-/

namespace LambdaJit.RoundCertificate

open LambdaJit.Interpretation LambdaJit.EndToEnd LambdaJit.ContextualPreorder

/-- The instantiation of a substitution written as data: each listed variable, by its name and
type, replaced by its term, every other variable kept, every type kept. -/
def substitution (entries : List ((Article.Name × Article.LogicType) × Article.Term)) :
    Article.Instantiation where
  typeImage name := .typeVariable name
  termImage name type := (entries.lookup (name, type)).getD (.termVariable name type)

/-- Every term equals itself. -/
theorem reflexive (signature : Signature) (term : Article.Term) :
    EquationSound signature term term :=
  fun _ => ContextualEquivalence.reflexive _

/-- An equation turned. -/
theorem symmetric (signature : Signature) (left right : Article.Term)
    (sound : EquationSound signature left right) : EquationSound signature right left :=
  fun valuation => (sound valuation).symmetric

/-- Two equations chained. -/
theorem transitive (signature : Signature) (first second third : Article.Term)
    (firstSound : EquationSound signature first second)
    (secondSound : EquationSound signature second third) :
    EquationSound signature first third :=
  fun valuation => (firstSound valuation).transitive (secondSound valuation)

/-- Congruence of application: `f = g` and `x = y` give `f x = g y`. -/
theorem congruence (signature : Signature) (leftFunction rightFunction leftArgument rightArgument : Article.Term)
    (functions : EquationSound signature leftFunction rightFunction)
    (arguments : EquationSound signature leftArgument rightArgument) :
    EquationSound signature (.application leftFunction leftArgument)
      (.application rightFunction rightArgument) :=
  fun valuation => ContextualEquivalence.application (functions valuation) (arguments valuation)

/-- An instance of a sound equation is sound: the instantiation is a change of valuation
(`Interpretation.interpretInstantiate`). -/
theorem instantiated (signature : Signature) (left right : Article.Term)
    (entries : List ((Article.Name × Article.LogicType) × Article.Term))
    (sound : EquationSound signature left right) :
    EquationSound signature (left.instantiate (substitution entries))
      (right.instantiate (substitution entries)) := by
  intro valuation
  rw [interpretInstantiate, interpretInstantiate]
  exact sound _

/-- An import that `importChecked` accepts is sound (`EndToEnd.importCheckedSound`). -/
theorem imported (signature : Signature) (lemmas : List Statement)
    (lemmasSound : ∀ lemma ∈ lemmas, lemma.Sound) (left right : Article.Term)
    (checked : importChecked signature lemmas (left, right) = true) :
    EquationSound signature left right :=
  importCheckedSound lemmasSound checked

/-- The empty list of library statements is sound: the certificates of rounds that use no
library lemma pass it. -/
theorem noLemmasSound : ∀ lemma ∈ ([] : List Statement), lemma.Sound :=
  fun _ member => nomatch member

/-! ## The ξ step

The body of a ξ step is proved at one valuation, the scope's: the abstraction rule
(`Justification.Abstraction` of the e-graph) unites a closure with a thunk once their bodies,
opened at fresh eigenvariables, are united, and the article writes each eigenvariable as a term
variable. Inside the step, the equations hold where the eigenvariables are the de Bruijn variables
of the abstractions they open, the innermost the variable 0; `abstracted` then wraps the body's
equivalence in those abstractions, which ≃_O, a congruence, keeps. No substitution lemma is needed:
an equation is never used at another valuation than the one it was proved at, and an import, sound
at every valuation, is specialized (`specialized`). -/

/-- The position of an entry in a scope, its length when absent. -/
def scopePosition (entry : Article.Name × Article.LogicType) :
    List (Article.Name × Article.LogicType) → Nat
  | [] => 0
  | head :: rest => if head = entry then 0 else scopePosition entry rest + 1

/-- The valuation of a scope of eigenvariables, the innermost first: each as the de Bruijn variable
of its position, every other variable as the variable past the scope. -/
def scopeValuation (scope : List (Article.Name × Article.LogicType)) : Valuation :=
  fun name type => .boundVariable (scopePosition (name, type) scope)

/-- The equation holds at the valuation of the scope. -/
def ScopedSound (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) : Prop :=
  ContextualEquivalence (interpret signature (scopeValuation scope) left)
    (interpret signature (scopeValuation scope) right)

/-- A sound equation holds at every scope's valuation. -/
theorem specialized (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) (sound : EquationSound signature left right) :
    ScopedSound signature scope left right :=
  sound _

/-- An equation of terms with no variable that holds in a scope is sound: its sides'
interpretations do not depend on the valuation (`Interpretation.interpretAgree`). -/
theorem unscoped (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term)
    (closed : (termVariables left ++ termVariables right).isEmpty = true)
    (sound : ScopedSound signature scope left right) : EquationSound signature left right := by
  have bothEmpty : termVariables left = [] ∧ termVariables right = [] := by
    simpa [List.isEmpty_iff, List.append_eq_nil_iff] using closed
  intro valuation
  have leftAgree := interpretAgree (signature := signature) (first := valuation)
    (second := scopeValuation scope) left (by intro occurrence member; rw [bothEmpty.1] at member; cases member)
  have rightAgree := interpretAgree (signature := signature) (first := valuation)
    (second := scopeValuation scope) right (by intro occurrence member; rw [bothEmpty.2] at member; cases member)
  rw [leftAgree, rightAgree]
  exact sound

theorem scopedReflexive (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (term : Article.Term) : ScopedSound signature scope term term :=
  ContextualEquivalence.reflexive _

theorem scopedSymmetric (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) (sound : ScopedSound signature scope left right) :
    ScopedSound signature scope right left :=
  sound.symmetric

theorem scopedTransitive (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (first second third : Article.Term) (firstSound : ScopedSound signature scope first second)
    (secondSound : ScopedSound signature scope second third) :
    ScopedSound signature scope first third :=
  firstSound.transitive secondSound

theorem scopedCongruence (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (leftFunction rightFunction leftArgument rightArgument : Article.Term)
    (functions : ScopedSound signature scope leftFunction rightFunction)
    (arguments : ScopedSound signature scope leftArgument rightArgument) :
    ScopedSound signature scope (.application leftFunction leftArgument)
      (.application rightFunction rightArgument) :=
  ContextualEquivalence.application functions arguments

/-- Whether the search of β conversions joins the interpretations of two terms at the scope's
valuation, open terms whose free variables are the eigenvariables. -/
def scopedConversionChecked (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) : Bool :=
  let leftTerm := interpret signature (scopeValuation scope) left
  let rightTerm := interpret signature (scopeValuation scope) right
  Semantics.betaReducesDeepening (Semantics.conversionFuel leftTerm rightTerm) leftTerm rightTerm

/-- A β conversion the search accepts at the scope's valuation holds there. -/
theorem scopedConversion (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) (checked : scopedConversionChecked signature scope left right = true) :
    ScopedSound signature scope left right :=
  contextualEquivalenceOfDerivableLatticeEta
    (Semantics.DerivableLatticeEta.betaReducesDeepeningDerivable checked)

/-- Whether an instance of an import, a lemma the article names no library statement of, is
accepted: the import is one `importChecked` accepts with no library statement, or the instance is a
β conversion at the scope's valuation (`scopedConversionChecked`). -/
def schemaChecked (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) (entries : List ((Article.Name × Article.LogicType) × Article.Term)) :
    Bool :=
  importChecked signature [] (left, right) ||
    scopedConversionChecked signature scope (left.instantiate (substitution entries))
      (right.instantiate (substitution entries))

/-- An instance that `schemaChecked` accepts holds at the scope's valuation. -/
theorem schemaInstance (signature : Signature) (scope : List (Article.Name × Article.LogicType))
    (left right : Article.Term) (entries : List ((Article.Name × Article.LogicType) × Article.Term))
    (checked : schemaChecked signature scope left right entries = true) :
    ScopedSound signature scope (left.instantiate (substitution entries))
      (right.instantiate (substitution entries)) := by
  unfold schemaChecked at checked
  cases imports : importChecked signature [] (left, right) with
  | true =>
      exact specialized _ _ _ _
        (instantiated _ _ _ _ (imported signature [] noLemmasSound left right imports))
  | false =>
      rw [imports, Bool.false_or] at checked
      exact scopedConversion _ _ _ _ checked

/-- The term with its head redexes contracted in head order, at most `fuel` of them. -/
def headReduced : Nat → Semantics.Term → Semantics.Term
  | 0, term => term
  | fuel + 1, term =>
      match Semantics.headContracted term with
      | some reduced => headReduced fuel reduced
      | none => term

theorem headReducedDerivable : ∀ (fuel : Nat) (term : Semantics.Term),
    Semantics.DerivableLatticeEta (fun _ _ => False) term (headReduced fuel term)
  | 0, term => Semantics.DerivableLatticeEta.reflexive term
  | fuel + 1, term => by
      unfold headReduced
      split
      · rename_i reduced contracted
        exact .transitive (Semantics.DerivableLatticeEta.headContractedDerivable contracted)
          (headReducedDerivable fuel reduced)
      · exact Semantics.DerivableLatticeEta.reflexive term

/-- Whether the closure's interpretation at the scope's valuation, its head redexes contracted (the
thunk constant's abstractions applied to its fillings), is reached by β steps from the abstractions,
one per eigenvariable, over the body's interpretation at the scope the eigenvariables extend (the
outermost eigenvariable first in `eigenvariables`): the body, read from the closure's code at its
fillings and the eigenvariables, reduces to what the closure's code reduces to under its holes. -/
def abstractionChecked (signature : Signature) (scope eigenvariables : List (Article.Name × Article.LogicType))
    (closure body : Article.Term) : Bool :=
  let closureTerm := interpret signature (scopeValuation scope) closure
  let opened := headReduced (Semantics.conversionFuel closureTerm closureTerm) closureTerm
  let abstracted := Readback.abstractions eigenvariables.length
    (interpret signature (scopeValuation (eigenvariables.reverse ++ scope)) body)
  Semantics.betaReducesDeepening (Semantics.conversionFuel abstracted opened) abstracted opened

/-- A closure that `abstractionChecked` accepts with its body is ≃_O to the abstractions over the
body. -/
theorem abstractionCheckedEquivalent {signature : Signature}
    {scope eigenvariables : List (Article.Name × Article.LogicType)} {closure body : Article.Term}
    (checked : abstractionChecked signature scope eigenvariables closure body = true) :
    ContextualEquivalence (interpret signature (scopeValuation scope) closure)
      (Readback.abstractions eigenvariables.length
        (interpret signature (scopeValuation (eigenvariables.reverse ++ scope)) body)) :=
  contextualEquivalenceOfDerivableLatticeEta
    (.transitive (headReducedDerivable _ _)
      (.symmetric (Semantics.DerivableLatticeEta.betaReducesDeepeningDerivable checked)))

/-- ≃_O under abstractions: a congruence (`ContextualEquivalence.fill`). -/
theorem abstractionsEquivalent : ∀ (count : Nat) {left right : Semantics.Term},
    ContextualEquivalence left right →
      ContextualEquivalence (Readback.abstractions count left) (Readback.abstractions count right)
  | 0, _, _, equivalent => equivalent
  | count + 1, _, _, equivalent => (abstractionsEquivalent count equivalent).fill (.abstraction .hole)

/-- The abstraction rule ξ: two closures whose bodies, opened at the eigenvariables, are equal in the
scope the eigenvariables extend are equal, each closure checked to be the abstractions over its body
(`abstractionChecked`). -/
theorem abstracted (signature : Signature) (scope eigenvariables : List (Article.Name × Article.LogicType))
    (first second body spelling : Article.Term)
    (firstChecked : abstractionChecked signature scope eigenvariables first body = true)
    (secondChecked : abstractionChecked signature scope eigenvariables second spelling = true)
    (inner : ScopedSound signature (eigenvariables.reverse ++ scope) body spelling) :
    ScopedSound signature scope first second :=
  (abstractionCheckedEquivalent firstChecked).transitive
    ((abstractionsEquivalent eigenvariables.length inner).transitive
      (abstractionCheckedEquivalent secondChecked).symmetric)

end LambdaJit.RoundCertificate
