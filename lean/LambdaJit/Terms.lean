/-!
# The terms of the calculus

The terms of the calculus, the λ-lattice terms Λ_{+∥} of DdLP96 (M. Dezani-Ciancaglini,
U. de'Liguoro, A. Piperno, TCS 170, 1996) that the formal definition of the calculus takes, with de Bruijn indices: their substitution, their free indices, the closed βη normal
forms, the one-hole contexts, and the lemmas on shifting and substitution that the other modules
share. Module `FourEquations` derives equations between them, and module `LatticeEtaDerivability`
defines the derivability ⊢_{λ-lattice-η} and the consistent normal forms NF◇_{λ-lattice-η} on them;
the declarations of this module are in the namespace `LambdaJit.Semantics` as well.

Formulation choices the paper leaves open:

- Terms use de Bruijn indices, so α-equivalent terms are one term, as the formal definition
  itself writes NF_βη. The paper's named variable x of λx. M is index 0 of the body.
- Substitution lowers as it substitutes: `substitute depth replacement term` replaces index
  `depth` by `replacement` and lowers every index above it, shifting `replacement` once per
  abstraction it is carried under; `instantiate body argument` is M[x := N] for the redex
  (λx. M) N.
-/

namespace LambdaJit.Semantics

/-- A term of the calculus, that is a term of DdLP96's Λ_{+∥}, with de Bruijn indices. -/
inductive Term where
  /-- An occurrence of a variable by its de Bruijn index: under `depth` enclosing abstractions,
  index `index` is bound by the `index`-th of them counting outward from zero when
  `index < depth`, and is a free variable otherwise. -/
  | boundVariable (index : Nat)
  /-- The abstraction λx. body; x is index 0 of `body`. -/
  | abstraction (body : Term)
  /-- The application of `function` to `argument`. -/
  | application (function argument : Term)
  /-- The choice left + right. -/
  | choice (left right : Term)
  /-- The parallel left ∥ right. -/
  | parallel (left right : Term)
  deriving DecidableEq, Repr

namespace Term

/-- `shiftFrom cutoff term` raises by one every index of `term` that, counted at the root of
`term`, is at least `cutoff`: an occurrence under `depth` abstractions of `term` is raised when
its index is at least `cutoff + depth`. It places `term` under one more abstraction, inserted
outside the `cutoff` innermost abstractions that enclose `term`. -/
def shiftFrom : Nat → Term → Term
  | cutoff, boundVariable index =>
      if index < cutoff then boundVariable index else boundVariable (index + 1)
  | cutoff, abstraction body => abstraction (shiftFrom (cutoff + 1) body)
  | cutoff, application function argument =>
      application (shiftFrom cutoff function) (shiftFrom cutoff argument)
  | cutoff, choice left right => choice (shiftFrom cutoff left) (shiftFrom cutoff right)
  | cutoff, parallel left right => parallel (shiftFrom cutoff left) (shiftFrom cutoff right)

/-- `shift term` places `term` under one more abstraction: every free index is raised by one. -/
def shift (term : Term) : Term := shiftFrom 0 term

/-- `substitute depth replacement term` replaces the index `depth`, counted at the root of
`term`, by `replacement`, and lowers by one every index above it, as removing the abstraction
that bound index `depth` requires. `replacement` is shifted once for every abstraction of
`term` it is carried under, so no free variable of `replacement` is captured. -/
def substitute : Nat → Term → Term → Term
  | depth, replacement, boundVariable index =>
      if index < depth then boundVariable index
      else if index = depth then replacement
      else boundVariable (index - 1)
  | depth, replacement, abstraction body =>
      abstraction (substitute (depth + 1) (shift replacement) body)
  | depth, replacement, application function argument =>
      application (substitute depth replacement function)
        (substitute depth replacement argument)
  | depth, replacement, choice left right =>
      choice (substitute depth replacement left) (substitute depth replacement right)
  | depth, replacement, parallel left right =>
      parallel (substitute depth replacement left) (substitute depth replacement right)

/-- M[x := N] for the beta redex (λx. M) N, which is
`application (abstraction body) argument`: the capture-avoiding substitution of `argument`
for index 0 of `body`, the contractum of the redex. -/
def instantiate (body argument : Term) : Term := substitute 0 argument body

/-- `OccursFree index term`: the index `index`, counted at the root of `term`, occurs in
`term`; an occurrence under `depth` abstractions of `term` has index `index + depth`. -/
def OccursFree : Nat → Term → Prop
  | index, boundVariable other => other = index
  | index, abstraction body => OccursFree (index + 1) body
  | index, application function argument =>
      OccursFree index function ∨ OccursFree index argument
  | index, choice left right => OccursFree index left ∨ OccursFree index right
  | index, parallel left right => OccursFree index left ∨ OccursFree index right

/-- A closed term: FV(term) = ∅, no index occurs free. A program is a closed term. -/
def Closed (term : Term) : Prop := ∀ index, ¬ OccursFree index term

/-- A pure term, that is a term of Λ: no choice or parallel occurs in it. -/
def Pure : Term → Prop
  | boundVariable _ => True
  | abstraction body => Pure body
  | application function argument => Pure function ∧ Pure argument
  | choice _ _ => False
  | parallel _ _ => False

/-- A beta redex (λx. P) Q. -/
def BetaRedex (term : Term) : Prop :=
  ∃ body argument, term = application (abstraction body) argument

/-- An eta redex λx. P x with x ∉ FV(P): an abstraction of the application of `function` to
index 0, where index 0 does not occur free in `function`. -/
def EtaRedex (term : Term) : Prop :=
  ∃ function, term = abstraction (application function (boundVariable 0)) ∧
    ¬ OccursFree 0 function

/-- `EverySubterm property term`: `property` holds of every subterm of `term`, `term`
itself included. -/
def EverySubterm (property : Term → Prop) : Term → Prop
  | boundVariable index => property (boundVariable index)
  | abstraction body => property (abstraction body) ∧ EverySubterm property body
  | application function argument =>
      property (application function argument) ∧
        EverySubterm property function ∧ EverySubterm property argument
  | choice left right =>
      property (choice left right) ∧ EverySubterm property left ∧ EverySubterm property right
  | parallel left right =>
      property (parallel left right) ∧ EverySubterm property left ∧ EverySubterm property right

/-- A closed βη normal form, that is a term of NF_βη: a closed pure term with no subterm of the
form (λx. P) Q and none of the form λx. P x with x ∉ FV(P). -/
def NormalForm (term : Term) : Prop :=
  Closed term ∧ Pure term ∧
    EverySubterm (fun subterm => ¬ BetaRedex subterm ∧ ¬ EtaRedex subterm) term

end Term

open Term

/-- A one-hole context C. -/
inductive Context where
  /-- The hole. -/
  | hole
  /-- λx. C. -/
  | abstraction (body : Context)
  /-- C applied to `argument`. -/
  | applicationFunction (function : Context) (argument : Term)
  /-- `function` applied to C. -/
  | applicationArgument (function : Term) (argument : Context)
  /-- C + right. -/
  | choiceLeft (left : Context) (right : Term)
  /-- left + C. -/
  | choiceRight (left : Term) (right : Context)
  /-- C ∥ right. -/
  | parallelLeft (left : Context) (right : Term)
  /-- left ∥ C. -/
  | parallelRight (left : Term) (right : Context)

/-- C[term]: `term` placed in the hole as it is, so an abstraction of the context binds the
free indices of `term` that point to it (the filling permits capture). -/
def Context.fill : Context → Term → Term
  | .hole, term => term
  | .abstraction body, term => .abstraction (body.fill term)
  | .applicationFunction function argument, term => .application (function.fill term) argument
  | .applicationArgument function argument, term => .application function (argument.fill term)
  | .choiceLeft left right, term => .choice (left.fill term) right
  | .choiceRight left right, term => .choice left (right.fill term)
  | .parallelLeft left right, term => .parallel (left.fill term) right
  | .parallelRight left right, term => .parallel left (right.fill term)

namespace Term

/-- Instantiating the once-shifted body at the variable its abstraction would bind gives the
body back, at any depth: `substitute depth (boundVariable depth)` undoes `shiftFrom (depth + 1)`.
-/
theorem substituteShiftFrom : ∀ (body : Term) (depth : Nat),
    substitute depth (boundVariable depth) (shiftFrom (depth + 1) body) = body
  | boundVariable index, depth => by
      by_cases below : index < depth + 1
      · by_cases strictlyBelow : index < depth
        · simp [shiftFrom, substitute, below, strictlyBelow]
        · have equal : index = depth := by omega
          subst equal
          simp [shiftFrom, substitute]
      · have notBelow : ¬ index + 1 < depth := by omega
        have notEqual : ¬ index + 1 = depth := by omega
        simp [shiftFrom, substitute, below, notBelow, notEqual]
  | abstraction body, depth => by
      have inner := substituteShiftFrom body (depth + 1)
      simp only [shiftFrom, substitute, shift] at inner ⊢
      simp [Nat.not_lt_zero] at inner ⊢
      exact inner
  | application function argument, depth => by
      simp only [shiftFrom, substitute, substituteShiftFrom function depth,
        substituteShiftFrom argument depth]
  | choice left right, depth => by
      simp only [shiftFrom, substitute, substituteShiftFrom left depth,
        substituteShiftFrom right depth]
  | parallel left right, depth => by
      simp only [shiftFrom, substitute, substituteShiftFrom left depth,
        substituteShiftFrom right depth]

/-- The case of `substituteShiftFrom` that T7 uses. Under the binder of λx. M, the term M is
(λx. M) x by the β rule from right to left, where the inner abstraction's body is M with every free
index but x shifted past the inner binder, `shiftFrom 1 M`; this lemma says that the
contractum of that redex is M again. -/
theorem instantiateShiftFrom (body : Term) :
    instantiate (shiftFrom 1 body) (boundVariable 0) = body :=
  substituteShiftFrom body 0

/-- Substitution at `depth` leaves a term unchanged when no index at or above `depth` occurs
free in it. -/
theorem substituteUnchanged : ∀ (term : Term) (depth : Nat) (replacement : Term),
    (∀ index, depth ≤ index → ¬ OccursFree index term) →
      substitute depth replacement term = term
  | boundVariable index, depth, replacement, absent => by
      have below : index < depth := by
        apply Nat.lt_of_not_le
        intro atOrAbove
        exact absent index atOrAbove rfl
      simp [substitute, below]
  | abstraction body, depth, replacement, absent => by
      have bodyAbsent : ∀ index, depth + 1 ≤ index → ¬ OccursFree index body := by
        intro index atOrAbove occurs
        have shifted : index - 1 + 1 = index := by omega
        apply absent (index - 1) (by omega)
        simp only [OccursFree, shifted]
        exact occurs
      simp only [substitute, substituteUnchanged body (depth + 1) (shift replacement) bodyAbsent]
  | application function argument, depth, replacement, absent => by
      simp only [substitute,
        substituteUnchanged function depth replacement
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inl occurs)),
        substituteUnchanged argument depth replacement
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inr occurs))]
  | choice left right, depth, replacement, absent => by
      simp only [substitute,
        substituteUnchanged left depth replacement
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inl occurs)),
        substituteUnchanged right depth replacement
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inr occurs))]
  | parallel left right, depth, replacement, absent => by
      simp only [substitute,
        substituteUnchanged left depth replacement
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inl occurs)),
        substituteUnchanged right depth replacement
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inr occurs))]

/-- Substituting at `depth` into a term shifted at `depth` gives the term back: the shifted term
has no index `depth`, and the substitution lowers every index above it again. -/
theorem substituteShiftFromCancel : ∀ (term : Term) (depth : Nat) (replacement : Term),
    substitute depth replacement (shiftFrom depth term) = term
  | boundVariable index, depth, replacement => by
      by_cases below : index < depth
      · simp [shiftFrom, substitute, below]
      · have notBelow : ¬ index + 1 < depth := by omega
        have notEqual : ¬ index + 1 = depth := by omega
        simp [shiftFrom, substitute, below, notBelow, notEqual]
  | abstraction body, depth, replacement => by
      simp only [shiftFrom, substitute, substituteShiftFromCancel body (depth + 1)]
  | application function argument, depth, replacement => by
      simp only [shiftFrom, substitute, substituteShiftFromCancel function depth,
        substituteShiftFromCancel argument depth]
  | choice left right, depth, replacement => by
      simp only [shiftFrom, substitute, substituteShiftFromCancel left depth,
        substituteShiftFromCancel right depth]
  | parallel left right, depth, replacement => by
      simp only [shiftFrom, substitute, substituteShiftFromCancel left depth,
        substituteShiftFromCancel right depth]

/-- Substituting index 0 of a shifted term gives the term back: (λx. M) N contracts to M when
x is not free in M. -/
theorem substituteShift (term replacement : Term) :
    substitute 0 replacement (shift term) = term :=
  substituteShiftFromCancel term 0 replacement

/-- Two shifts commute when the second cutoff is at most the first: shifting from
`lowerCutoff` after shifting from `cutoff` is shifting from `cutoff + 1` after shifting from
`lowerCutoff`. -/
theorem shiftFromShiftFrom : ∀ (term : Term) (cutoff lowerCutoff : Nat), lowerCutoff ≤ cutoff →
    shiftFrom lowerCutoff (shiftFrom cutoff term) =
      shiftFrom (cutoff + 1) (shiftFrom lowerCutoff term)
  | boundVariable index, cutoff, lowerCutoff, ordered => by
      by_cases belowLower : index < lowerCutoff
      · have belowCutoff : index < cutoff := by omega
        have belowNext : index < cutoff + 1 := by omega
        simp [shiftFrom, belowLower, belowCutoff, belowNext]
      · by_cases belowCutoff : index < cutoff
        · have belowNext : index + 1 < cutoff + 1 := by omega
          simp [shiftFrom, belowLower, belowCutoff, belowNext]
        · have notLower : ¬ index + 1 < lowerCutoff := by omega
          have notNext : ¬ index + 1 < cutoff + 1 := by omega
          simp [shiftFrom, belowLower, belowCutoff, notLower, notNext]
  | abstraction body, cutoff, lowerCutoff, ordered => by
      simp only [shiftFrom, shiftFromShiftFrom body (cutoff + 1) (lowerCutoff + 1) (by omega)]
  | application function argument, cutoff, lowerCutoff, ordered => by
      simp only [shiftFrom, shiftFromShiftFrom function cutoff lowerCutoff ordered,
        shiftFromShiftFrom argument cutoff lowerCutoff ordered]
  | choice left right, cutoff, lowerCutoff, ordered => by
      simp only [shiftFrom, shiftFromShiftFrom left cutoff lowerCutoff ordered,
        shiftFromShiftFrom right cutoff lowerCutoff ordered]
  | parallel left right, cutoff, lowerCutoff, ordered => by
      simp only [shiftFrom, shiftFromShiftFrom left cutoff lowerCutoff ordered,
        shiftFromShiftFrom right cutoff lowerCutoff ordered]

end Term

end LambdaJit.Semantics
