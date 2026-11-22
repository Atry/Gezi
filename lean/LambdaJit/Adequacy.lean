import LambdaJit.Defunctionalization
import LambdaJit.Confluence

/-!
# D3's items on the defunctionalized IR

This module collects what is proved of the items of design decision D3
(`lean/README.md`, "Design decisions"; `defunctionalizationFacts`), gives the consistent normal
forms of the defunctionalization of a closed term (`consistentNormalFormsDefunctionalize`), and
proves that the converse direction of D3's item 4 does not hold for
⊢^{defunctionalized}_{λ-lattice-η} as module `Theory` states it (`converseFails`), with three
witnesses. NF◇_{λ-lattice-η} is formalised in module `LatticeEtaDerivability` on the terms of the
calculus, the readback's codomain (module `Terms`); the consistent normal forms of an IR term are
NF◇_{λ-lattice-η} of its readback (D3's S_IR).

## What is proved

- Item 1 holds by construction: `readback` (module `Readback`) is a function of the finite term,
  and α-equivalent de Bruijn terms are one term.
- Item 2 holds by construction: α-equivalent terms are one de Bruijn term, and `defunctionalize`
  is a function of the de Bruijn term (module `Defunctionalization`). What is proved is its
  converse, the injectivity of the defunctionalization (`Defunctionalization.defunctionalizeInjective`):
  two closed terms with one defunctionalization are one term, which follows from item 3.
- Item 3 (`Defunctionalization.readbackDefunctionalize`): a closed term has a defunctionalization,
  and its readback is the term itself. So the consistent normal forms of the defunctionalization
  are those of the term (`consistentNormalFormsDefunctionalize`).
- Item 4, the soundness direction (`Readback.readbackSound`): two finite terms equal in
  λ-lattice-η on defunctionalized terms whose readbacks are defined have readbacks whose
  equation is derivable by ⊢_{λ-lattice-η}, under any hypotheses, the first clause of the
  defunctionalized β rule being one beta step, its second clause no step, and the defunctionalized
  η rule one eta step.
- Item 5 (`Defunctionalization.Witness.addressesFinerThanAlpha`): there are closed terms
  `M = λx. B` and `A` such that the first clause of the defunctionalized β rule (`Equal.betaFill`),
  applied to the application of the defunctionalization of `M`, a thunk with a hole, to that of
  `A`, gives a finite term that reads back to the contractum `N = B[x := A]` of `M A` and is not
  the defunctionalization of `N`. So two different finite terms read back to one term.

## The converse of item 4, refuted

Item 4 also asks that every step of ⊢_{λ-lattice-η} on readbacks have a corresponding
derivation on the IR. For ⊢^{defunctionalized}_{λ-lattice-η} as module `Theory` states it,
this is false, even for derivations without hypotheses between the defunctionalizations of closed
terms (`converseFails`). The proof is module `Confluence`: a reduction that contains the rules of
`Equal` oriented from left to right, and more (a thunk without holes reduces to the instance of its
code under a total slot reading, `instantiateClamped`, which agrees with `Equal`'s instance wherever
that is defined), is confluent, and every equation of `Equal` is joinable in it; no step of that
reduction rewrites inside a code, so a thunk with holes that is no η redex keeps its code and its
holes under every reduction (`reducesManyThunkKeeps`). Three witnesses:

1. A rule under a binder (`converseFailsUnderBinder`). `λx. x ((λy. y) x)` and `λx. x x` are
   equal by the β rule in the body of the abstraction, the congruence of ⊢_{λ-lattice-η}
   under λ; their defunctionalizations are thunks with one hole and the different codes
   `apply (slot 0) (apply (slot 1) (slot 0))` and `apply (slot 0) (slot 0)`, which `Equal` never
   relates. This is the FIXME of module `Theory` on rules under a binder, now proved.
2. The β rule at the root (`converseFailsForBeta`). D3's item 5 witness:
   `(λx1.λx2. x2 (x1 c)) a` equals `λx2. x2 (a c)` by one β step, but the first clause of the
   defunctionalized β rule takes the defunctionalization of the redex to a thunk that keeps `a` and
   `c` in two slots, while the defunctionalization of the contractum hoists the closed subterm
   `a c` into one; the two thunks have one readback and different codes, and `Equal` does not
   relate them (`converseFailsOnOneReadback`).
3. The numbered equations (`converseFailsWithoutNumberedEquations`). `K + I` equals `I + K` by
   equation (1), the commutativity of the choice; `Equal` has congruence only for choices (the
   other FIXME of module `Theory`), and a choice reduces side by side, so the two choices are
   never related.

So, on finite terms whose readbacks are defined, ⊢^{defunctionalized}_{λ-lattice-η} is
contained in the pullback of ⊢_{λ-lattice-η} along the readback (item 4's soundness
direction), and is not that pullback.

A program that names a library define and the same program with the name replaced by the define's
body give two such finite terms as well (`libraryNameOneReadback`, from the witness that link (i) of
D6 is stated on readbacks, in the section on the agreement with the Prolog of module
`Defunctionalization`): one readback, and not equal in the IR theory.

## Candidate routes for the converse

The candidates below are unbuilt, and whether any of them makes a converse of item 4 hold is
open.

- A leaf of `FiniteTerm` for a free variable or a fresh constant, through which a rule under a
  binder (the ξ rule, or the extensionality rule `M c = N c ⟹ M = N` with a fresh constant `c`)
  is stated on finite terms.
- A theory on codes: the β rule on codes and the inlining or hoisting of filled slots, a slot of a
  code (`Code.slot`) being already a leaf for a free variable, lifted to thunks by a congruence on
  the code.
- A weaker statement: the converse for a relation weaker than ⊢_{λ-lattice-η} on readbacks.

The third witness needs, besides, numbered equations on the IR, which of them and in what form
not being settled (FIXME in `Theory`): the witness rests on (1), an axiom of ⊢_{λ-lattice-η}, which
the IR theory does not have.

TODO (https://github.com/Atry/private-overlay/issues/1561, D2 and D3):
- Whether module `Theory`'s relation gains a rule under a binder, a design question still open
  (D3); the candidate routes are listed above.
- Item 4's soundness direction for the numbered equations written on the IR, which of them and in
  what form not being settled (FIXME in `Theory`).
-/

namespace LambdaJit.Adequacy

open LambdaJit.Semantics
open LambdaJit.Readback
open LambdaJit.Defunctionalization
open LambdaJit.Confluence

/-- Facts of the defunctionalization and the readback, by D3's items (2026-10-07): item 3; the
injectivity of the defunctionalization, the converse of item 2, which holds by construction; the
soundness direction of item 4, into ⊢_{λ-lattice-η}, for ⊢^{defunctionalized}_{λ-lattice-η}
without the numbered equations, as module `Theory` states it; and item 5, the statement of
`Witness.addressesFinerThanAlpha`. Item 1 holds by construction. -/
theorem defunctionalizationFacts :
    (∀ term : Term, Term.Closed term →
      ∃ finiteTerm, defunctionalize term = some finiteTerm ∧ readback finiteTerm = some term) ∧
    (∀ (left right : Term) (finiteTerm : FiniteTerm),
      defunctionalize left = some finiteTerm → defunctionalize right = some finiteTerm →
        left = right) ∧
    (∀ (hypotheses : Term → Term → Prop) (left right : FiniteTerm) (leftTerm rightTerm : Term),
      Equal left right → readback left = some leftTerm → readback right = some rightTerm →
        DerivableLatticeEta hypotheses leftTerm rightTerm) ∧
    (∃ (chain body argument contractum : Term) (code : Code) (hole : Hole) (holes : List Hole)
      (fillings : List FiniteTerm) (argumentFinite canonicalFinite : FiniteTerm),
      chain = .abstraction body ∧ contractum = Term.instantiate body argument ∧
      defunctionalize chain = some (.thunk code (hole :: holes) fillings) ∧
        defunctionalize argument = some argumentFinite ∧
          Equal (.apply (.thunk code (hole :: holes) fillings) argumentFinite)
            (.thunk code holes (fill hole holes fillings argumentFinite)) ∧
            (∀ hypotheses, DerivableLatticeEta hypotheses (.application chain argument) contractum) ∧
              readback (.thunk code holes (fill hole holes fillings argumentFinite)) =
                some contractum ∧
                defunctionalize contractum = some canonicalFinite ∧
                  readback canonicalFinite = some contractum ∧
                    FiniteTerm.thunk code holes (fill hole holes fillings argumentFinite) ≠
                      canonicalFinite) :=
  ⟨fun _ closed => readbackDefunctionalize closed,
    fun _ _ _ leftDefunctionalized rightDefunctionalized =>
      defunctionalizeInjective leftDefunctionalized rightDefunctionalized,
    fun _ _ _ _ _ equal leftReadback rightReadback =>
      readbackSound equal leftReadback rightReadback,
    Witness.addressesFinerThanAlpha⟩

/-- The consistent normal forms of the defunctionalization of a closed term, defined as
NF◇_{λ-lattice-η} of its readback (D3), are those of the term: item 3. -/
theorem consistentNormalFormsDefunctionalize {term : Term} (closed : Term.Closed term) :
    ∃ finiteTerm readBack, defunctionalize term = some finiteTerm ∧
      readback finiteTerm = some readBack ∧
        ∀ candidate, ConsistentNormalFormLatticeEta readBack candidate ↔
          ConsistentNormalFormLatticeEta term candidate := by
  obtain ⟨finiteTerm, defunctionalized, readBack⟩ := readbackDefunctionalize closed
  exact ⟨finiteTerm, term, defunctionalized, readBack, fun _ => Iff.rfl⟩

/-! ## The converse of item 4 -/

namespace Converse

/-- `λx. x x`, the contractum of `Agreement.binderRedex`, `λx. x ((λy. y) x)`, under its binder. -/
def binderContractum : Term :=
  .abstraction (.application (.boundVariable 0) (.boundVariable 0))

/-- The defunctionalization of `λx. x x`. -/
def binderContractumThunk : FiniteTerm :=
  .thunk (.apply (.slot 0) (.slot 0)) [.slot 0] []

theorem binderContractumDefunctionalized :
    defunctionalize binderContractum = some binderContractumThunk := rfl

/-- `λx. x ((λy. y) x) = λx. x x` by the β rule in the body of the abstraction, under any
hypotheses. -/
theorem binderDerivable {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses Agreement.binderRedex binderContractum :=
  .congruenceAbstraction (.congruenceArgument _ (.beta (.boundVariable 0) (.boundVariable 0)))

/-- The two defunctionalizations are not equal in λ-lattice-η on defunctionalized terms:
thunks with one hole, no η redexes, and different codes. -/
theorem binderNotEqual : ¬ Equal Agreement.binderRedexThunk binderContractumThunk :=
  notEqualThunks (by simp) rfl (by simp) rfl (Or.inl (by intro equal; cases equal))

/-- The choice `K + I`. -/
def choiceFirstIdentity : Term := .choice first Readback.Witness.identityTerm

/-- The choice `I + K`. -/
def choiceIdentityFirst : Term := .choice Readback.Witness.identityTerm first

theorem choiceFirstIdentityDefunctionalized :
    defunctionalize choiceFirstIdentity =
      some (.choice Readback.Witness.first Readback.Witness.identity) := rfl

theorem choiceIdentityFirstDefunctionalized :
    defunctionalize choiceIdentityFirst =
      some (.choice Readback.Witness.identity Readback.Witness.first) := rfl

/-- `K + I = I + K` by equation (1), under any hypotheses. -/
theorem choiceDerivable {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses choiceFirstIdentity choiceIdentityFirst :=
  .choiceCommutative _ _

/-- The two defunctionalizations are not equal in λ-lattice-η on defunctionalized terms: their
left sides are thunks with different holes. -/
theorem choiceNotEqual :
    ¬ Equal (.choice Readback.Witness.first Readback.Witness.identity)
      (.choice Readback.Witness.identity Readback.Witness.first) :=
  notEqualChoices (by simp) rfl (by simp) rfl (Or.inr (by intro equal; cases equal))

end Converse

/-- The filled thunk of D3's item 5 and the defunctionalization of its readback have one readback
and are not equal in λ-lattice-η on defunctionalized terms. -/
theorem converseFailsOnOneReadback :
    readback Witness.filled = readback Witness.canonical ∧
      ¬ Equal Witness.filled Witness.canonical :=
  ⟨by rw [Witness.filledReadback, Witness.canonicalReadback],
    notEqualThunks (by simp) rfl (by simp) rfl
      (Or.inl (by intro equal; cases equal))⟩

/-- The two finite terms of the witness that link (i) of D6 is stated on readbacks
(`Defunctionalization.Agreement.libraryNameReadback`, `libraryNameFrontEnd`): `λ_. false`
through `thunk_instruction/2` with the handle of `false` solved, and the defunctionalization of the
same program with the name replaced by the body of `false`, have one readback and are not equal in
λ-lattice-η on defunctionalized terms. -/
theorem libraryNameOneReadback :
    readback Agreement.namedFalseThunk = readback Agreement.falseInlinedThunk ∧
      ¬ Equal Agreement.namedFalseThunk Agreement.falseInlinedThunk :=
  ⟨by rw [Agreement.libraryNameReadback.2.1, Agreement.libraryNameReadback.2.2.2],
    notEqualThunks (by simp) rfl (by simp) rfl (Or.inr (by simp))⟩

/-- The converse of item 4 fails under a binder: `λx. x ((λy. y) x)` and `λx. x x`, equal by the
β rule in the body of the abstraction, have defunctionalizations that are not equal in
λ-lattice-η on defunctionalized terms. -/
theorem converseFailsUnderBinder :
    defunctionalize Agreement.binderRedex = some Agreement.binderRedexThunk ∧
      defunctionalize Converse.binderContractum = some Converse.binderContractumThunk ∧
        (∀ hypotheses, DerivableLatticeEta hypotheses Agreement.binderRedex
          Converse.binderContractum) ∧
          ¬ Equal Agreement.binderRedexThunk Converse.binderContractumThunk :=
  ⟨Agreement.binderReadTwice, Converse.binderContractumDefunctionalized,
    fun _ => Converse.binderDerivable, Converse.binderNotEqual⟩

/-- The converse of item 4 fails for the β rule at the root: the redex `(λx1.λx2. x2 (x1 c)) a`
and its contractum `λx2. x2 (a c)`, the instance of the body `λx2. x2 (x1 c)` at `a`, have
defunctionalizations that are not equal in λ-lattice-η on defunctionalized terms. -/
theorem converseFailsForBeta :
    Agreement.chainTerm = .abstraction Agreement.chainBody ∧
      Witness.contractumTerm = Term.instantiate Agreement.chainBody first ∧
        defunctionalize (.application Agreement.chainTerm first) =
            some (.apply Agreement.chainThunk Readback.Witness.first) ∧
          defunctionalize Witness.contractumTerm = some Witness.canonical ∧
            (∀ hypotheses, DerivableLatticeEta hypotheses
              (.application Agreement.chainTerm first) Witness.contractumTerm) ∧
              ¬ Equal (.apply Agreement.chainThunk Readback.Witness.first) Witness.canonical := by
  refine ⟨rfl, Witness.contractumInstantiates, rfl, Witness.contractumDefunctionalized,
    fun _ => Witness.applicationContracts, ?_⟩
  intro equal
  exact converseFailsOnOneReadback.2
    (.transitive (.symmetric Witness.applicationFilled) equal)

/-- The converse of item 4 fails without the numbered equations: `K + I` and `I + K`, equal by
equation (1), have defunctionalizations that are not equal in λ-lattice-η on
defunctionalized terms. -/
theorem converseFailsWithoutNumberedEquations :
    defunctionalize Converse.choiceFirstIdentity =
        some (.choice Readback.Witness.first Readback.Witness.identity) ∧
      defunctionalize Converse.choiceIdentityFirst =
          some (.choice Readback.Witness.identity Readback.Witness.first) ∧
        (∀ hypotheses, DerivableLatticeEta hypotheses Converse.choiceFirstIdentity
          Converse.choiceIdentityFirst) ∧
          ¬ Equal (.choice Readback.Witness.first Readback.Witness.identity)
            (.choice Readback.Witness.identity Readback.Witness.first) :=
  ⟨Converse.choiceFirstIdentityDefunctionalized, Converse.choiceIdentityFirstDefunctionalized,
    fun _ => Converse.choiceDerivable, Converse.choiceNotEqual⟩

/-- The converse of D3's item 4 is false for ⊢^{defunctionalized}_{λ-lattice-η} as module
`Theory` states it, even restricted to the defunctionalizations of closed terms and to derivations
in ⊢_{λ-lattice-η} without hypotheses: `converseFailsUnderBinder` is a counterexample. -/
theorem converseFails :
    ¬ ∀ (left right : Term) (leftFinite rightFinite : FiniteTerm),
        defunctionalize left = some leftFinite → defunctionalize right = some rightFinite →
          (∀ hypotheses, DerivableLatticeEta hypotheses left right) →
            Equal leftFinite rightFinite := by
  intro converse
  obtain ⟨leftDefunctionalized, rightDefunctionalized, derivable, notEqual⟩ :=
    converseFailsUnderBinder
  exact notEqual (converse _ _ _ _ leftDefunctionalized rightDefunctionalized derivable)

end LambdaJit.Adequacy
