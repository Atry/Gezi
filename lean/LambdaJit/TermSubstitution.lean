import LambdaJit.Semantics

/-!
# Lowering, eta contraction and the commutation of shifting with substitution

Lemmas about lowering, eta contraction and the commutation of shifting with substitution on the
de Bruijn terms of module `Terms`, used by `BetaEtaConfluence`, `Normalisation` and `Readback`.
The module imports only `Semantics`, so that the semantic modules that use it do not depend on the
IR side.
-/

namespace LambdaJit.Semantics

namespace Term

/-! ## Free occurrence decided, and lowering -/

/-- `OccursFree index term` is decided by recursion on `term`, following its definition. -/
instance decideOccursFree : (index : Nat) → (term : Term) → Decidable (OccursFree index term)
  | index, boundVariable other => inferInstanceAs (Decidable (other = index))
  | index, abstraction body => decideOccursFree (index + 1) body
  | index, application function argument =>
      have := decideOccursFree index function
      have := decideOccursFree index argument
      inferInstanceAs (Decidable (OccursFree index function ∨ OccursFree index argument))
  | index, choice left right =>
      have := decideOccursFree index left
      have := decideOccursFree index right
      inferInstanceAs (Decidable (OccursFree index left ∨ OccursFree index right))
  | index, parallel left right =>
      have := decideOccursFree index left
      have := decideOccursFree index right
      inferInstanceAs (Decidable (OccursFree index left ∨ OccursFree index right))

/-- `lowerFrom cutoff term` lowers by one every index of `term` that, counted at the root of
`term`, is above `cutoff`: an occurrence under `depth` abstractions of `term` is lowered when its
index is above `cutoff + depth`. An occurrence of the index `cutoff` itself is left as it is. On
a term in which the index `cutoff` does not occur free, `shiftFrom cutoff` undoes
`lowerFrom cutoff` (`shiftFromLowerFrom`); the eta contraction lowers only such terms, with
`cutoff` 0. -/
def lowerFrom : Nat → Term → Term
  | cutoff, boundVariable index =>
      if cutoff < index then boundVariable (index - 1) else boundVariable index
  | cutoff, abstraction body => abstraction (lowerFrom (cutoff + 1) body)
  | cutoff, application function argument =>
      application (lowerFrom cutoff function) (lowerFrom cutoff argument)
  | cutoff, choice left right => choice (lowerFrom cutoff left) (lowerFrom cutoff right)
  | cutoff, parallel left right => parallel (lowerFrom cutoff left) (lowerFrom cutoff right)

/-- `lower term` takes `term` out from under one abstraction that binds no occurrence in it:
every free index is lowered by one. -/
def lower (term : Term) : Term := lowerFrom 0 term

/-- When the index `cutoff` does not occur free in `term`, lowering the indices above `cutoff`
and then raising the indices at or above `cutoff` gives `term` back. -/
theorem shiftFromLowerFrom : ∀ (term : Term) (cutoff : Nat),
    ¬ OccursFree cutoff term → shiftFrom cutoff (lowerFrom cutoff term) = term
  | boundVariable index, cutoff, absent => by
      have notEqual : index ≠ cutoff := absent
      by_cases above : cutoff < index
      · have notBelow : ¬ index - 1 < cutoff := by omega
        have restored : index - 1 + 1 = index := by omega
        simp [lowerFrom, shiftFrom, above, notBelow, restored]
      · have below : index < cutoff := by omega
        simp [lowerFrom, shiftFrom, above, below]
  | abstraction body, cutoff, absent => by
      simp only [lowerFrom, shiftFrom, shiftFromLowerFrom body (cutoff + 1) absent]
  | application function argument, cutoff, absent => by
      simp only [OccursFree, not_or] at absent
      simp only [lowerFrom, shiftFrom, shiftFromLowerFrom function cutoff absent.1,
        shiftFromLowerFrom argument cutoff absent.2]
  | choice left right, cutoff, absent => by
      simp only [OccursFree, not_or] at absent
      simp only [lowerFrom, shiftFrom, shiftFromLowerFrom left cutoff absent.1,
        shiftFromLowerFrom right cutoff absent.2]
  | parallel left right, cutoff, absent => by
      simp only [OccursFree, not_or] at absent
      simp only [lowerFrom, shiftFrom, shiftFromLowerFrom left cutoff absent.1,
        shiftFromLowerFrom right cutoff absent.2]

/-- The function of an eta redex is the shift of its contractum: when index 0 does not occur
free in `function`, `function` is `shift (lower function)`, which is the shape of the function
in `DerivableLatticeEta.eta`. -/
theorem shiftLower (function : Term) (absent : ¬ OccursFree 0 function) :
    shift (lower function) = function :=
  shiftFromLowerFrom function 0 absent

/-- After `shiftFrom cutoff`, the index `cutoff` does not occur free: the indices below `cutoff`
stay below it, and the others are raised past it. -/
theorem notOccursFreeShiftFrom : ∀ (term : Term) (cutoff : Nat),
    ¬ OccursFree cutoff (shiftFrom cutoff term)
  | boundVariable index, cutoff => by
      by_cases below : index < cutoff
      · simp only [shiftFrom, below, if_true, OccursFree]
        omega
      · simp only [shiftFrom, below, if_false, OccursFree]
        omega
  | abstraction body, cutoff => notOccursFreeShiftFrom body (cutoff + 1)
  | application function argument, cutoff => by
      simp only [shiftFrom, OccursFree, not_or]
      exact ⟨notOccursFreeShiftFrom function cutoff, notOccursFreeShiftFrom argument cutoff⟩
  | choice left right, cutoff => by
      simp only [shiftFrom, OccursFree, not_or]
      exact ⟨notOccursFreeShiftFrom left cutoff, notOccursFreeShiftFrom right cutoff⟩
  | parallel left right, cutoff => by
      simp only [shiftFrom, OccursFree, not_or]
      exact ⟨notOccursFreeShiftFrom left cutoff, notOccursFreeShiftFrom right cutoff⟩

/-- `lowerFrom cutoff` undoes `shiftFrom cutoff` on every term. -/
theorem lowerFromShiftFrom : ∀ (term : Term) (cutoff : Nat),
    lowerFrom cutoff (shiftFrom cutoff term) = term
  | boundVariable index, cutoff => by
      by_cases below : index < cutoff
      · have notAbove : ¬ cutoff < index := by omega
        simp [shiftFrom, lowerFrom, below, notAbove]
      · have above : cutoff < index + 1 := by omega
        simp [shiftFrom, lowerFrom, below, above]
  | abstraction body, cutoff => by
      simp only [shiftFrom, lowerFrom, lowerFromShiftFrom body (cutoff + 1)]
  | application function argument, cutoff => by
      simp only [shiftFrom, lowerFrom, lowerFromShiftFrom function cutoff,
        lowerFromShiftFrom argument cutoff]
  | choice left right, cutoff => by
      simp only [shiftFrom, lowerFrom, lowerFromShiftFrom left cutoff,
        lowerFromShiftFrom right cutoff]
  | parallel left right, cutoff => by
      simp only [shiftFrom, lowerFrom, lowerFromShiftFrom left cutoff,
        lowerFromShiftFrom right cutoff]

/-! ## Eta contraction -/

/-- The contractum of the abstraction of `body` when that abstraction is an eta redex λx. F x
with x ∉ FV(F), which is F with its free indices lowered by one, `lower F`; `none` otherwise.
The test is the one `EtaRedex` states: `body` is the application of some F to index 0, and
index 0 does not occur free in F. -/
def etaContractum : Term → Option Term
  | application function (boundVariable 0) =>
      if OccursFree 0 function then none else some (lower function)
  | _ => none

/-- The eta contraction finds exactly the eta redexes of `EtaRedex`: it answers
`some contractum` when `body` is `application function (boundVariable 0)` with index 0 not free
in `function`, and then `contractum` is `lower function`. -/
theorem etaContractumEqualSome {body contractum : Term} :
    etaContractum body = some contractum ↔
      ∃ function, body = application function (boundVariable 0) ∧ ¬ OccursFree 0 function ∧
        contractum = lower function := by
  constructor
  · intro found
    unfold etaContractum at found
    split at found
    · next function =>
        split at found
        · cases found
        · next absent =>
            exact ⟨function, rfl, absent, (Option.some.inj found).symm⟩
    · cases found
  · rintro ⟨function, rfl, absent, rfl⟩
    simp [etaContractum, absent]

/-- The eta contraction finds every left side of `DerivableLatticeEta.eta`, with its right side as
the contractum: the body `application (shift function) (boundVariable 0)` contracts to `function`.
With `etaContractumEqualSome` and `shiftLower`, the abstractions the eta contraction rewrites
are exactly the left sides of `DerivableLatticeEta.eta`. -/
theorem etaContractumShift (function : Term) :
    etaContractum (application (shift function) (boundVariable 0)) = some function :=
  etaContractumEqualSome.mpr
    ⟨shift function, rfl, notOccursFreeShiftFrom function 0,
      (lowerFromShiftFrom function 0).symm⟩

/-! ## Shifting and substitution -/

/-- Shifting commutes with substitution below the substituted index: substituting the shifted
replacement at `depth + 1` into the shifted term is shifting the result of substituting at
`depth`, for a cutoff at most `depth`. -/
theorem substituteShiftFromCommute : ∀ (term : Term) (cutoff depth : Nat) (replacement : Term),
    cutoff ≤ depth →
      Term.substitute (depth + 1) (Term.shiftFrom cutoff replacement) (Term.shiftFrom cutoff term) =
        Term.shiftFrom cutoff (Term.substitute depth replacement term)
  | .boundVariable index, cutoff, depth, replacement, ordered => by
      by_cases belowCutoff : index < cutoff
      · have belowDepth : index < depth := by omega
        have belowNext : index < depth + 1 := by omega
        simp [Term.shiftFrom, Term.substitute, belowCutoff, belowDepth, belowNext]
      · by_cases belowDepth : index < depth
        · have belowNext : index + 1 < depth + 1 := by omega
          simp [Term.shiftFrom, Term.substitute, belowCutoff, belowDepth, belowNext]
        · by_cases atDepth : index = depth
          · subst atDepth
            simp [Term.shiftFrom, Term.substitute, belowCutoff]
          · have notNext : ¬ index + 1 < depth + 1 := by omega
            have notLowered : ¬ index - 1 < cutoff := by omega
            have restored : index - 1 + 1 = index := by omega
            simp [Term.shiftFrom, Term.substitute, belowCutoff, belowDepth, atDepth, notNext,
              notLowered, restored]
  | .abstraction body, cutoff, depth, replacement, ordered => by
      have shifted : Term.shift (Term.shiftFrom cutoff replacement) =
          Term.shiftFrom (cutoff + 1) (Term.shift replacement) :=
        Term.shiftFromShiftFrom replacement cutoff 0 (Nat.zero_le cutoff)
      simp only [Term.shiftFrom, Term.substitute, shifted,
        substituteShiftFromCommute body (cutoff + 1) (depth + 1) (Term.shift replacement) (by omega)]
  | .application function argument, cutoff, depth, replacement, ordered => by
      simp only [Term.shiftFrom, Term.substitute,
        substituteShiftFromCommute function cutoff depth replacement ordered,
        substituteShiftFromCommute argument cutoff depth replacement ordered]
  | .choice left right, cutoff, depth, replacement, ordered => by
      simp only [Term.shiftFrom, Term.substitute,
        substituteShiftFromCommute left cutoff depth replacement ordered,
        substituteShiftFromCommute right cutoff depth replacement ordered]
  | .parallel left right, cutoff, depth, replacement, ordered => by
      simp only [Term.shiftFrom, Term.substitute,
        substituteShiftFromCommute left cutoff depth replacement ordered,
        substituteShiftFromCommute right cutoff depth replacement ordered]

end Term

end LambdaJit.Semantics
