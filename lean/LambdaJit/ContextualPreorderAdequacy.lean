import LambdaJit.DdLP96Model

/-!
# Adequacy of DdLP96's reading for SOL (theorem 4.1 and corollary 4.2)

This module formalises sections 4 and 5 of the contextual preorder record
(the record below), given a model satisfying the fields of `DdLP96Model`; module
`ContextualPreorderUnconditional` states them in the instance `wadsworthModel`, with no model
argument. Theorems 6.1 and 7.1 for ⊢_{λ-lattice-η} are in modules `LatticeEtaConsistency` and
`LatticeEtaBridge`.

- `DdLP96Model.solvableIffInterpretNotBottom`, the record's theorem 4.1: given a model, M ∈ SOL if
  and only if [[M]]ρ_⊤ ≠ ⊥. Direction ⇒ is `DdLP96Model.interpretNotBottomOfSolvable` of module
  `DdLP96Model`; direction ⇐ is the record's section 4.2, computability by levels of compact
  elements (`DdLP96Model.Computable`, the record's 𝒮ₙ(d)) and the basic lemma 4.3
  (`DdLP96Model.basicLemma`).
- `DdLP96Model.contextualPreorderOfInterpretBelow`, the record's corollary 4.2, and
  `DdLP96Model.contextualEquivalenceOfInterpretEqual`, its form for two terms that read alike.
- `notContextuallyEquivalentFirstSecond`: K ≄_O K*, in the context □ Ω I.

The proof of theorem 4.1 ⇐ differs from the record's section 4.2 in one respect, a choice of
proof, not of statement: the computability predicates quantify over CLOSED arguments only
(`Computable` at level 0 over closed argument lists, at level n + 1 over closed arguments), and
the basic lemma substitutes closed terms for the free variables (`closeAll`). The record's lemma X
is used with the argument `top` = Y (λz. λx. z ∥ x), which is closed and whose applications to closed
terms are all solvable (`solvableApplicationsTop`), where the record uses a fresh variable; module
`ContextualPreorder` proves lemma X for every argument. `top` also closes the free variables in the
proof of theorem 4.1 ⇐. With closed replacements a simultaneous
substitution is a sequence of single substitutions, which the substitution lemmas of module
`BetaEtaConfluence` already cover. The theorem proved is the record's theorem 4.1 as stated.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Closed terms and closing substitutions -/

/-- Shifting from `cutoff` leaves a term unchanged when no index at or above `cutoff` occurs free
in it. -/
theorem shiftFromUnchanged : ∀ (term : Term) (cutoff : Nat),
    (∀ index, cutoff ≤ index → ¬ OccursFree index term) → shiftFrom cutoff term = term
  | .boundVariable index, cutoff, absent => by
      have below : index < cutoff := Nat.lt_of_not_le fun atOrAbove => absent index atOrAbove rfl
      simp [shiftFrom, below]
  | .abstraction body, cutoff, absent => by
      have bodyAbsent : ∀ index, cutoff + 1 ≤ index → ¬ OccursFree index body := by
        intro index atOrAbove occurs
        have shifted : index - 1 + 1 = index := by omega
        apply absent (index - 1) (by omega)
        simp only [OccursFree, shifted]
        exact occurs
      simp only [shiftFrom, shiftFromUnchanged body (cutoff + 1) bodyAbsent]
  | .application function argument, cutoff, absent => by
      simp only [shiftFrom,
        shiftFromUnchanged function cutoff
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inl occurs)),
        shiftFromUnchanged argument cutoff
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inr occurs))]
  | .choice left right, cutoff, absent => by
      simp only [shiftFrom,
        shiftFromUnchanged left cutoff
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inl occurs)),
        shiftFromUnchanged right cutoff
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inr occurs))]
  | .parallel left right, cutoff, absent => by
      simp only [shiftFrom,
        shiftFromUnchanged left cutoff
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inl occurs)),
        shiftFromUnchanged right cutoff
          (fun index atOrAbove occurs => absent index atOrAbove (Or.inr occurs))]

/-- A closed term is its own shift. -/
theorem shiftClosed {term : Term} (closed : Closed term) : shift term = term :=
  shiftFromUnchanged term 0 (fun index _ => closed index)

/-- Substitution leaves a closed term unchanged. -/
theorem substituteClosed {term : Term} (closed : Closed term) (depth : Nat) (replacement : Term) :
    substitute depth replacement term = term :=
  substituteUnchanged term depth replacement (fun index _ => closed index)

/-- The free indices of a substitution instance by a closed term: those of the term below the
substituted index, and those above it lowered by one. -/
theorem occursFreeSubstituteClosed {replacement : Term} (closed : Closed replacement) :
    ∀ (term : Term) (depth index : Nat), OccursFree index (substitute depth replacement term) →
      (index < depth ∧ OccursFree index term) ∨ (depth ≤ index ∧ OccursFree (index + 1) term)
  | .boundVariable position, depth, index, occurs => by
      by_cases below : position < depth
      · simp only [substitute, below, ite_true, OccursFree] at occurs
        subst occurs
        exact .inl ⟨below, rfl⟩
      · by_cases equal : position = depth
        · subst equal
          simp only [substitute, Nat.lt_irrefl, ite_false, ite_true] at occurs
          exact absurd occurs (closed index)
        · simp only [substitute, below, equal, ite_false, OccursFree] at occurs
          refine .inr ⟨by omega, ?_⟩
          show position = index + 1
          omega
  | .abstraction body, depth, index, occurs => by
      simp only [substitute, shiftClosed closed, OccursFree] at occurs
      rcases occursFreeSubstituteClosed closed body (depth + 1) (index + 1) occurs with
        ⟨below, inner⟩ | ⟨above, inner⟩
      · exact .inl ⟨by omega, inner⟩
      · exact .inr ⟨by omega, inner⟩
  | .application function argument, depth, index, occurs => by
      simp only [substitute, OccursFree] at occurs
      rcases occurs with inner | inner
      · rcases occursFreeSubstituteClosed closed function depth index inner with
          ⟨below, found⟩ | ⟨above, found⟩
        · exact .inl ⟨below, .inl found⟩
        · exact .inr ⟨above, .inl found⟩
      · rcases occursFreeSubstituteClosed closed argument depth index inner with
          ⟨below, found⟩ | ⟨above, found⟩
        · exact .inl ⟨below, .inr found⟩
        · exact .inr ⟨above, .inr found⟩
  | .choice left right, depth, index, occurs => by
      simp only [substitute, OccursFree] at occurs
      rcases occurs with inner | inner
      · rcases occursFreeSubstituteClosed closed left depth index inner with
          ⟨below, found⟩ | ⟨above, found⟩
        · exact .inl ⟨below, .inl found⟩
        · exact .inr ⟨above, .inl found⟩
      · rcases occursFreeSubstituteClosed closed right depth index inner with
          ⟨below, found⟩ | ⟨above, found⟩
        · exact .inl ⟨below, .inr found⟩
        · exact .inr ⟨above, .inr found⟩
  | .parallel left right, depth, index, occurs => by
      simp only [substitute, OccursFree] at occurs
      rcases occurs with inner | inner
      · rcases occursFreeSubstituteClosed closed left depth index inner with
          ⟨below, found⟩ | ⟨above, found⟩
        · exact .inl ⟨below, .inl found⟩
        · exact .inr ⟨above, .inl found⟩
      · rcases occursFreeSubstituteClosed closed right depth index inner with
          ⟨below, found⟩ | ⟨above, found⟩
        · exact .inl ⟨below, .inr found⟩
        · exact .inr ⟨above, .inr found⟩

/-- FV(term) ⊆ {0, …, bound − 1}: every free index of `term` is below `bound`. -/
def FreeBelow (bound : Nat) (term : Term) : Prop :=
  ∀ index, OccursFree index term → index < bound

/-- Every term has finitely many free indices. -/
theorem freeBound : ∀ term : Term, ∃ bound, FreeBelow bound term
  | .boundVariable position => ⟨position + 1, fun index occurs => by
      simp only [OccursFree] at occurs
      omega⟩
  | .abstraction body =>
      let ⟨bound, free⟩ := freeBound body
      ⟨bound, fun index occurs => by
        have inner := free (index + 1) occurs
        omega⟩
  | .application function argument =>
      let ⟨functionBound, functionFree⟩ := freeBound function
      let ⟨argumentBound, argumentFree⟩ := freeBound argument
      ⟨functionBound + argumentBound, fun index occurs => by
        rcases occurs with inner | inner
        · have below := functionFree index inner
          omega
        · have below := argumentFree index inner
          omega⟩
  | .choice left right =>
      let ⟨leftBound, leftFree⟩ := freeBound left
      let ⟨rightBound, rightFree⟩ := freeBound right
      ⟨leftBound + rightBound, fun index occurs => by
        rcases occurs with inner | inner
        · have below := leftFree index inner
          omega
        · have below := rightFree index inner
          omega⟩
  | .parallel left right =>
      let ⟨leftBound, leftFree⟩ := freeBound left
      let ⟨rightBound, rightFree⟩ := freeBound right
      ⟨leftBound + rightBound, fun index occurs => by
        rcases occurs with inner | inner
        · have below := leftFree index inner
          omega
        · have below := rightFree index inner
          omega⟩

/-- Every member of the list is closed. -/
def AllClosed (terms : List Term) : Prop := ∀ term ∈ terms, Closed term

/-- The empty list has only closed members. -/
theorem allClosedNil : AllClosed [] := fun _ member => absurd member List.not_mem_nil

/-- A closed term added to a list of closed terms. -/
theorem allClosedCons {first : Term} {rest : List Term} (firstClosed : Closed first)
    (restClosed : AllClosed rest) : AllClosed (first :: rest) := fun term member =>
  (List.mem_cons.mp member).elim (fun equal => equal ▸ firstClosed) (restClosed term)

/-- M[x₀ := N₀][x₁ := N₁]…: the closed terms of the list substituted, in order, for the index
`depth`; with `depth` 0 and a term whose free indices are below the length of the list, the
simultaneous substitution of the list's i-th member for index i. -/
def closeAll : Nat → List Term → Term → Term
  | _, [], term => term
  | depth, replacement :: rest, term => closeAll depth rest (substitute depth replacement term)

theorem closeAllApplication : ∀ (replacements : List Term) (depth : Nat) (function argument : Term),
    closeAll depth replacements (.application function argument) =
      .application (closeAll depth replacements function) (closeAll depth replacements argument)
  | [], _, _, _ => rfl
  | replacement :: rest, depth, function, argument =>
      closeAllApplication rest depth (substitute depth replacement function)
        (substitute depth replacement argument)

theorem closeAllChoice : ∀ (replacements : List Term) (depth : Nat) (left right : Term),
    closeAll depth replacements (.choice left right) =
      .choice (closeAll depth replacements left) (closeAll depth replacements right)
  | [], _, _, _ => rfl
  | replacement :: rest, depth, left, right =>
      closeAllChoice rest depth (substitute depth replacement left)
        (substitute depth replacement right)

theorem closeAllParallel : ∀ (replacements : List Term) (depth : Nat) (left right : Term),
    closeAll depth replacements (.parallel left right) =
      .parallel (closeAll depth replacements left) (closeAll depth replacements right)
  | [], _, _, _ => rfl
  | replacement :: rest, depth, left, right =>
      closeAllParallel rest depth (substitute depth replacement left)
        (substitute depth replacement right)


/-- Closed replacements are carried under an abstraction unchanged. -/
theorem closeAllAbstraction : ∀ {replacements : List Term}, AllClosed replacements →
    ∀ (depth : Nat) (body : Term),
      closeAll depth replacements (.abstraction body) =
        .abstraction (closeAll (depth + 1) replacements body)
  | [], _, _, _ => rfl
  | replacement :: rest, allClosed, depth, body => by
      show closeAll depth rest
        (.abstraction (substitute (depth + 1) (shift replacement) body)) = _
      rw [shiftClosed (allClosed replacement List.mem_cons_self)]
      exact closeAllAbstraction (fun term member => allClosed term (List.mem_cons_of_mem _ member))
        depth _

/-- A closing substitution leaves a closed term unchanged. -/
theorem closeAllClosed : ∀ (replacements : List Term) (depth : Nat) {term : Term},
    Closed term → closeAll depth replacements term = term
  | [], _, _, _ => rfl
  | replacement :: rest, depth, term, closed => by
      show closeAll depth rest (substitute depth replacement term) = term
      rw [substituteClosed closed]
      exact closeAllClosed rest depth closed

/-- A closing substitution maps index i to the list's i-th member. -/
theorem closeAllVariable : ∀ {replacements : List Term}, AllClosed replacements →
    ∀ {index : Nat} {replacement : Term}, replacements[index]? = some replacement →
      closeAll 0 replacements (.boundVariable index) = replacement
  | [], _, _, _, found => by simp at found
  | first :: rest, allClosed, 0, replacement, found => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      show closeAll 0 rest (substitute 0 first (.boundVariable 0)) = first
      simp only [substitute, Nat.lt_irrefl, ite_false, ite_true]
      exact closeAllClosed rest 0 (allClosed first List.mem_cons_self)
  | first :: rest, allClosed, index + 1, replacement, found => by
      simp only [List.getElem?_cons_succ] at found
      show closeAll 0 rest (substitute 0 first (.boundVariable (index + 1))) = replacement
      have notBelow : ¬ index + 1 < 0 := by omega
      have notEqual : ¬ index + 1 = 0 := by omega
      simp only [substitute, notBelow, notEqual, ite_false, Nat.add_sub_cancel]
      exact closeAllVariable (fun term member => allClosed term (List.mem_cons_of_mem _ member)) found

/-- A closing substitution of a term whose free indices are below the length of the list gives a
closed term. -/
theorem closeAllClosesTerm : ∀ {replacements : List Term}, AllClosed replacements →
    ∀ {term : Term}, FreeBelow replacements.length term → Closed (closeAll 0 replacements term)
  | [], _, _, free => fun index occurs => Nat.not_lt_zero _ (free index occurs)
  | first :: rest, allClosed, term, free => by
      apply closeAllClosesTerm (fun term member => allClosed term (List.mem_cons_of_mem _ member))
      intro index occurs
      rcases occursFreeSubstituteClosed (allClosed first List.mem_cons_self) term 0 index occurs with
        ⟨below, _⟩ | ⟨_, inner⟩
      · exact absurd below (Nat.not_lt_zero _)
      · have bound := free (index + 1) inner
        simp only [List.length_cons] at bound
        omega

/-- Two closed terms substituted at index 0 and at index 1 commute:
M[1 := r][0 := N] = M[0 := N][0 := r], both being M with N for index 0 and r for index 1. -/
theorem substituteSwapClosed {first second : Term} (firstClosed : Closed first)
    (secondClosed : Closed second) (term : Term) :
    substitute 0 first (substitute 1 second term) = substitute 0 second (substitute 0 first term) := by
  rw [BetaEtaConfluence.substituteSubstitute term 0 0 first second (Nat.le_refl 0),
    substituteClosed firstClosed]
  have shifted : shiftFrom 0 second = second := shiftClosed secondClosed
  rw [shifted]

/-- The β contractum of a closing substitution under one abstraction is the closing substitution
with the argument added in front: (λx. M[σ]) N contracts to M[x := N, σ]. -/
theorem instantiateCloseAll : ∀ {replacements : List Term}, AllClosed replacements →
    ∀ {argument : Term}, Closed argument → ∀ body : Term,
      instantiate (closeAll 1 replacements body) argument =
        closeAll 0 (argument :: replacements) body
  | [], _, _, _, _ => rfl
  | first :: rest, allClosed, argument, argumentClosed, body => by
      show instantiate (closeAll 1 rest (substitute 1 first body)) argument =
        closeAll 0 rest (substitute 0 first (substitute 0 argument body))
      rw [instantiateCloseAll (fun term member => allClosed term (List.mem_cons_of_mem _ member))
        argumentClosed]
      show closeAll 0 rest (substitute 0 argument (substitute 1 first body)) = _
      rw [substituteSwapClosed argumentClosed (allClosed first List.mem_cons_self)]

/-- A closing substitution instance is solvable only if the term is. -/
theorem solvableOfCloseAll : ∀ (replacements : List Term) (depth : Nat) {term : Term},
    Solvable (closeAll depth replacements term) → Solvable term
  | [], _, _, solvable => solvable
  | _ :: rest, depth, _, solvable =>
      Solvable.ofSubstitute (solvableOfCloseAll rest depth solvable)

/-! ## Expansion ⇛ -/

/-- The record's M ⇛ M′: for every list P⃗ of closed terms, M P⃗ ∈ SOL iff M′ P⃗ ∈ SOL. -/
def Expands (term other : Term) : Prop :=
  ∀ arguments, AllClosed arguments →
    (Solvable (applyAll term arguments) ↔ Solvable (applyAll other arguments))

/-- M ⇛ M′ gives M N ⇛ M′ N for closed N. -/
theorem Expands.application {term other argument : Term} (expands : Expands term other)
    (closed : Closed argument) : Expands (.application term argument) (.application other argument) :=
  fun arguments allClosed => expands (argument :: arguments) (allClosedCons closed allClosed)

/-- (λx. M) N ⇛ M[x := N], by (S3). -/
theorem expandsBeta (body argument : Term) :
    Expands (.application (.abstraction body) argument) (instantiate body argument) :=
  fun arguments _ => solvableBetaSpine body argument arguments

/-- (M₁ + M₂) N ⇛ M₁ N + M₂ N, by (S3) twice. -/
theorem expandsChoiceApplication (left right argument : Term) :
    Expands (.application (.choice left right) argument)
      (.choice (.application left argument) (.application right argument)) :=
  fun arguments _ => (solvableChoiceSpine (argument :: arguments) left right).trans
    (solvableChoiceSpine arguments (.application left argument) (.application right argument)).symm

/-- (M₁ ∥ M₂) N ⇛ M₁ N ∥ M₂ N, by (S3) twice. -/
theorem expandsParallelApplication (left right argument : Term) :
    Expands (.application (.parallel left right) argument)
      (.parallel (.application left argument) (.application right argument)) :=
  fun arguments _ => (solvableParallelSpine (argument :: arguments) left right).trans
    (solvableParallelSpine arguments (.application left argument) (.application right argument)).symm

/-- A stuck spine applied to more arguments is a stuck spine. -/
theorem StuckSpine.applyAll : ∀ (arguments : List Term) {term : Term},
    StuckSpine term → StuckSpine (ContextualPreorder.applyAll term arguments)
  | [], _, stuck => stuck
  | argument :: rest, _, stuck => StuckSpine.applyAll rest (.application argument stuck)

/-- The context `inner` applied to the arguments in order: C P₁ … Pₖ. -/
def applicationContext : Context → List Term → Context
  | inner, [] => inner
  | inner, argument :: rest => applicationContext (.applicationFunction inner argument) rest

/-- Filling C P⃗ is applying C[M] to P⃗. -/
theorem applicationContextFill : ∀ (inner : Context) (arguments : List Term) (term : Term),
    (applicationContext inner arguments).fill term = applyAll (inner.fill term) arguments
  | _, [], _ => rfl
  | inner, argument :: rest, term => applicationContextFill (.applicationFunction inner argument) rest term

/-- ⇛ is transitive. -/
theorem Expands.transitive {term middle other : Term} (first : Expands term middle)
    (second : Expands middle other) : Expands term other :=
  fun arguments closed => (first arguments closed).trans (second arguments closed)

/-! ## `top`, a closed term whose applications to closed terms are all solvable

`top` = Y (λz. λx. z ∥ x) of the proofs file, section 3, with
Y = λf. (λx. f (x x)) (λx. f (x x)). `top` P⃗ ∈ SOL for every list of closed P⃗, by head reduction alone
(`solvableApplicationsTop`), so `top` is in every 𝒮ₙ(d) (`DdLP96Model.computableOfSolvableApplications`)
and serves as the closed argument of (L) and (CA′) and as the closing substitution of theorem 4.1 ⇐.
-/

/-- Y = λf. (λx. f (x x)) (λx. f (x x)). -/
def fixedPointCombinator : Term :=
  .abstraction (.application
    (.abstraction (.application (.boundVariable 1)
      (.application (.boundVariable 0) (.boundVariable 0))))
    (.abstraction (.application (.boundVariable 1)
      (.application (.boundVariable 0) (.boundVariable 0)))))

/-- λx. F (x x), for a closed F: the term that Y F applies to itself. -/
def selfApplicationOf (functional : Term) : Term :=
  .abstraction (.application functional (.application (.boundVariable 0) (.boundVariable 0)))

/-- (λx. F (x x)) (λx. F (x x)), for a closed F: the term Y F reduces to in one step. -/
def selfApplicationFixedPoint (functional : Term) : Term :=
  .application (selfApplicationOf functional) (selfApplicationOf functional)

/-- λx. F (x x) is closed when F is. -/
theorem closedSelfApplicationOf {functional : Term} (closed : Closed functional) :
    Closed (selfApplicationOf functional) := by
  intro index occurs
  simp only [selfApplicationOf, OccursFree] at occurs
  rcases occurs with inside | (equal | equal)
  · exact closed (index + 1) inside
  · omega
  · omega

/-- (λx. F (x x)) (λx. F (x x)) is closed when F is. -/
theorem closedSelfApplicationFixedPoint {functional : Term} (closed : Closed functional) :
    Closed (selfApplicationFixedPoint functional) := by
  intro index occurs
  rcases occurs with inside | inside <;> exact closedSelfApplicationOf closed index inside

/-- Y F ⇛ (λx. F (x x)) (λx. F (x x)), for a closed F: one β step at the head. -/
theorem expandsFixedPointCombinator {functional : Term} (closed : Closed functional) :
    Expands (.application fixedPointCombinator functional) (selfApplicationFixedPoint functional) := by
  have contractum : instantiate (.application
      (.abstraction (.application (.boundVariable 1)
        (.application (.boundVariable 0) (.boundVariable 0))))
      (.abstraction (.application (.boundVariable 1)
        (.application (.boundVariable 0) (.boundVariable 0))))) functional =
      selfApplicationFixedPoint functional := by
    simp [instantiate, substitute, shiftClosed closed, selfApplicationFixedPoint, selfApplicationOf]
  rw [← contractum]
  exact expandsBeta _ _

/-- (λx. F (x x)) (λx. F (x x)) ⇛ F ((λx. F (x x)) (λx. F (x x))), for a closed F. -/
theorem expandsSelfApplicationFixedPoint {functional : Term} (closed : Closed functional) :
    Expands (selfApplicationFixedPoint functional)
      (.application functional (selfApplicationFixedPoint functional)) := by
  have contractum : instantiate
      (.application functional (.application (.boundVariable 0) (.boundVariable 0)))
      (selfApplicationOf functional) =
      .application functional (selfApplicationFixedPoint functional) := by
    simp [instantiate, substitute, substituteClosed closed, selfApplicationFixedPoint]
  rw [← contractum]
  exact expandsBeta _ _

/-- λz. λx. z ∥ x, the functional of `top`. -/
def functionalOfTop : Term :=
  .abstraction (.abstraction (.parallel (.boundVariable 1) (.boundVariable 0)))

/-- `top` = Y (λz. λx. z ∥ x), the proofs file's section 3. -/
def top : Term := .application fixedPointCombinator functionalOfTop

theorem closedFunctionalOfTop : Closed functionalOfTop := by
  intro index occurs
  simp only [functionalOfTop, OccursFree] at occurs
  omega

theorem closedFixedPointCombinator : Closed fixedPointCombinator := by
  intro index occurs
  simp only [fixedPointCombinator, OccursFree] at occurs
  omega

/-- `top` is closed. -/
theorem closedTop : Closed top := by
  intro index occurs
  rcases occurs with inside | inside
  · exact closedFixedPointCombinator index inside
  · exact closedFunctionalOfTop index inside

/-- `top′` ⇛ λx. `top′` ∥ x, where `top′` is the self-application `top` reduces to. -/
theorem expandsUnfoldedTop :
    Expands (selfApplicationFixedPoint functionalOfTop)
      (.abstraction (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0))) := by
  have closed := closedSelfApplicationFixedPoint closedFunctionalOfTop
  have contractum : instantiate (.abstraction (.parallel (.boundVariable 1) (.boundVariable 0)))
      (selfApplicationFixedPoint functionalOfTop) =
      .abstraction (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0)) := by
    simp [instantiate, substitute, shiftClosed closed]
  refine (expandsSelfApplicationFixedPoint closedFunctionalOfTop).transitive ?_
  rw [← contractum]
  exact expandsBeta _ _

/-- `top′` P⃗ ∈ SOL for every list of closed P⃗, where `top′` is the self-application `top` reduces to. With no
argument, `top′` reduces to λx. `top′` ∥ x, a head normal form: (∥s) needs both sides to step, and x does
not. With P₁ first, `top′` P₁ P⃗ reduces to (`top′` ∥ P₁) P⃗, solvable by the induction hypothesis on its
left branch (the record's (S3)). -/
theorem solvableApplicationsUnfoldedTop : ∀ arguments, AllClosed arguments →
    Solvable (applyAll (selfApplicationFixedPoint functionalOfTop) arguments)
  | [], _ => by
      rw [expandsUnfoldedTop [] allClosedNil]
      refine ⟨0, fun result step => ?_⟩
      cases step with
      | abstraction inner =>
          cases inner with
          | parallel _ rightStep => cases rightStep
  | argument :: rest, allClosed => by
      have argumentClosed := allClosed argument List.mem_cons_self
      have restClosed : AllClosed rest :=
        fun term member => allClosed term (List.mem_cons_of_mem _ member)
      rw [expandsUnfoldedTop (argument :: rest) allClosed]
      show Solvable (applyAll (.application (.abstraction
        (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0))) argument) rest)
      rw [solvableBetaSpine]
      have contractum : instantiate
          (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0)) argument =
          .parallel (selfApplicationFixedPoint functionalOfTop) argument := by
        simp [instantiate, substitute,
          substituteClosed (closedSelfApplicationFixedPoint closedFunctionalOfTop)]
      rw [contractum, solvableParallelSpine]
      exact .inl (solvableApplicationsUnfoldedTop rest restClosed)

/-- `top` P⃗ ∈ SOL for every list of closed P⃗. -/
theorem solvableApplicationsTop (arguments : List Term) (closed : AllClosed arguments) :
    Solvable (applyAll top arguments) :=
  (expandsFixedPointCombinator closedFunctionalOfTop arguments closed).mpr
    (solvableApplicationsUnfoldedTop arguments closed)

/-! ## Ξ, another closed term whose applications to closed terms are all solvable

Ξ = Y (λe. Ŝ ∥ (K ∥ e e)) of the proofs file, section 3 (Ŝ ∥ K ∥ e e is read as Ŝ ∥ (K ∥ e e); the
other bracketing has the same proof). Ξ P⃗ ∈ SOL for every list of closed P⃗, by head reduction alone
(`solvableApplicationsXi`): Ξ P₁ P⃗ has the branch K Ξ′ P₁ P⃗, which reduces to Ξ′ P⃗. -/

/-- K = λx. λy. x is closed. -/
theorem closedFirst : Closed first := by
  intro index occurs
  simp only [first, OccursFree] at occurs
  omega

/-- Ŝ = λx. λy. λz. x z (y z). -/
def starling : Term :=
  .abstraction (.abstraction (.abstraction (.application
    (.application (.boundVariable 2) (.boundVariable 0))
    (.application (.boundVariable 1) (.boundVariable 0)))))

/-- λe. Ŝ ∥ (K ∥ e e), the functional of Ξ; K is `first`. -/
def functionalOfXi : Term :=
  .abstraction (.parallel starling
    (.parallel first (.application (.boundVariable 0) (.boundVariable 0))))

/-- Ξ = Y (λe. Ŝ ∥ (K ∥ e e)), the proofs file's section 3. -/
def fixedPointOfXi : Term := .application fixedPointCombinator functionalOfXi

theorem closedStarling : Closed starling := by
  intro index occurs
  simp only [starling, OccursFree] at occurs
  omega

theorem closedFunctionalOfXi : Closed functionalOfXi := by
  intro index occurs
  simp only [functionalOfXi, OccursFree] at occurs
  rcases occurs with inside | (inside | (equal | equal))
  · exact closedStarling (index + 1) inside
  · exact closedFirst (index + 1) inside
  · omega
  · omega

/-- Ξ is closed. -/
theorem closedFixedPointOfXi : Closed fixedPointOfXi := by
  intro index occurs
  rcases occurs with inside | inside
  · exact closedFixedPointCombinator index inside
  · exact closedFunctionalOfXi index inside

/-- Ξ′ ⇛ Ŝ ∥ (K ∥ Ξ′ Ξ′), where Ξ′ is the self-application Ξ reduces to. -/
theorem expandsUnfoldedXi :
    Expands (selfApplicationFixedPoint functionalOfXi)
      (.parallel starling (.parallel first (.application (selfApplicationFixedPoint functionalOfXi)
        (selfApplicationFixedPoint functionalOfXi)))) := by
  have contractum : instantiate (.parallel starling
      (.parallel first (.application (.boundVariable 0) (.boundVariable 0))))
      (selfApplicationFixedPoint functionalOfXi) =
      .parallel starling (.parallel first (.application (selfApplicationFixedPoint functionalOfXi)
        (selfApplicationFixedPoint functionalOfXi))) := by
    simp [instantiate, substitute, substituteClosed closedStarling, substituteClosed closedFirst]
  refine (expandsSelfApplicationFixedPoint closedFunctionalOfXi).transitive ?_
  rw [← contractum]
  exact expandsBeta _ _

/-- Ξ′ P⃗ ∈ SOL for every list of closed P⃗, where Ξ′ is the self-application Ξ reduces to. With no
argument, the branch K of Ξ′'s unfolding is a head normal form. With P₁ first, the branch Ξ′ Ξ′ of
Ξ′ P₁ P⃗ unfolds again, and its branch K Ξ′ P₁ P⃗ reduces to Ξ′ P⃗, solvable by the induction
hypothesis (the record's (S3)). -/
theorem solvableApplicationsUnfoldedXi : ∀ arguments, AllClosed arguments →
    Solvable (applyAll (selfApplicationFixedPoint functionalOfXi) arguments)
  | [], _ => by
      rw [expandsUnfoldedXi [] allClosedNil]
      exact solvableParallel.mpr (.inr (solvableParallel.mpr (.inl
        (solvableOfHeadNormalForm (.abstraction (.abstraction (.stuck (.boundVariable 1))))))))
  | argument :: rest, allClosed => by
      have closed := closedSelfApplicationFixedPoint closedFunctionalOfXi
      have restClosed : AllClosed rest :=
        fun term member => allClosed term (List.mem_cons_of_mem _ member)
      rw [expandsUnfoldedXi (argument :: rest) allClosed, solvableParallelSpine]
      refine .inr ?_
      rw [solvableParallelSpine]
      refine .inr ?_
      -- Ξ′ Ξ′ P₁ P⃗ is Ξ′ applied to Ξ′ :: P₁ :: P⃗.
      show Solvable (applyAll (selfApplicationFixedPoint functionalOfXi)
        (selfApplicationFixedPoint functionalOfXi :: argument :: rest))
      rw [expandsUnfoldedXi _ (allClosedCons closed allClosed), solvableParallelSpine]
      refine .inr ?_
      rw [solvableParallelSpine]
      refine .inl ?_
      -- K Ξ′ P₁ P⃗ reduces in two β steps to Ξ′ P⃗.
      show Solvable (applyAll (.application (.abstraction (.abstraction (.boundVariable 1)))
        (selfApplicationFixedPoint functionalOfXi)) (argument :: rest))
      rw [solvableBetaSpine]
      have firstContractum : instantiate (.abstraction (.boundVariable 1))
          (selfApplicationFixedPoint functionalOfXi) =
          .abstraction (selfApplicationFixedPoint functionalOfXi) := by
        simp [instantiate, substitute, shiftClosed closed]
      rw [firstContractum]
      show Solvable (applyAll (.application (.abstraction (selfApplicationFixedPoint functionalOfXi))
        argument) rest)
      rw [solvableBetaSpine, instantiate, substituteClosed closed]
      exact solvableApplicationsUnfoldedXi rest restClosed

/-- Ξ P⃗ ∈ SOL for every list of closed P⃗. -/
theorem solvableApplicationsXi (arguments : List Term) (closed : AllClosed arguments) :
    Solvable (applyAll fixedPointOfXi arguments) :=
  (expandsFixedPointCombinator closedFunctionalOfXi arguments closed).mpr
    (solvableApplicationsUnfoldedXi arguments closed)

namespace DdLP96Model

variable (model : DdLP96Model)

/-! ## The compact elements 𝔻ₙ -/

/-- d ∈ 𝔻ₙ: d is a fixed point of Pₙ, which by (P4) is the image of Pₙ. -/
def Compact (level : Nat) (value : model.Value) : Prop := model.project level value = value

/-- Pₙ(x) ∈ 𝔻ₙ, by (P4). -/
theorem compactProject (level : Nat) (value : model.Value) :
    model.Compact level (model.project level value) := by
  show model.project level (model.project level value) = model.project level value
  rw [model.projectProject, Nat.min_self]

/-- 𝔻ₙ ⊆ 𝔻_{n+1}, by (P4). -/
theorem compactRaise {level : Nat} {value : model.Value} (compact : model.Compact level value) :
    model.Compact (level + 1) value := by
  show model.project (level + 1) value = value
  rw [← compact, model.projectProject, Nat.min_eq_left (Nat.le_succ level)]

/-- 𝔻ₙ ⊆ 𝔻_{n+k}. -/
theorem compactRaiseBy {level : Nat} {value : model.Value} (compact : model.Compact level value) :
    ∀ extra, model.Compact (level + extra) value
  | 0 => compact
  | extra + 1 => model.compactRaise (compactRaiseBy compact extra)

/-- 𝔻ₙ is closed under ⊓, by (E1). -/
theorem compactMeet {level : Nat} {left right : model.Value} (leftCompact : model.Compact level left)
    (rightCompact : model.Compact level right) : model.Compact level (model.meet left right) := by
  show model.project level (model.meet left right) = model.meet left right
  rw [model.projectMeet, leftCompact, rightCompact]

/-- 𝔻ₙ is closed under ⊔, by (E1). -/
theorem compactJoin {level : Nat} {left right : model.Value} (leftCompact : model.Compact level left)
    (rightCompact : model.Compact level right) : model.Compact level (model.join left right) := by
  show model.project level (model.join left right) = model.join left right
  rw [model.projectJoin, leftCompact, rightCompact]

/-- ⊤ ∈ 𝔻ₙ for every n. -/
theorem compactTop (level : Nat) : model.Compact level model.top := by
  have zero : model.Compact 0 model.top := model.projectTop
  have raised := model.compactRaiseBy zero level
  rw [Nat.zero_add] at raised
  exact raised

/-- ⊥ ∈ 𝔻₀: P₀(⊥) is ⊥ or ⊤ and below ⊥. -/
theorem compactBottomZero : model.Compact 0 model.bottom :=
  model.bottomOfBelowBottom (model.projectBelow 0 model.bottom)

/-- 𝔻₀ = {⊥, ⊤}. -/
theorem compactZero {value : model.Value} (compact : model.Compact 0 value) :
    value = model.bottom ∨ value = model.top := by
  rw [← compact]
  exact model.projectZeroTwoPoint value

/-- (E3): d ∈ 𝔻_{n+1} gives d(z) ∈ 𝔻ₙ, by (P11). -/
theorem compactApply {level : Nat} {function : model.Value}
    (compact : model.Compact (level + 1) function) (argument : model.Value) :
    model.Compact level (model.apply function argument) := by
  have result := model.applyProjectResult level function argument
  rw [compact] at result
  exact result

/-- (E3): d ∈ 𝔻_{n+1} gives d(z) = d(zₙ), by (P12). -/
theorem compactApplyArgument {level : Nat} {function : model.Value}
    (compact : model.Compact (level + 1) function) (argument : model.Value) :
    model.apply function argument = model.apply function (model.project level argument) := by
  have result := model.applyProjectArgument level function argument
  rw [compact] at result
  exact result

/-! ## Computability 𝒮ₙ(d) (the record, section 4.2) -/

/-- The record's 𝒮ₙ(d), with closed arguments: 𝒮₀(⊥) is every term, 𝒮₀(⊤) the terms M with
M P⃗ ∈ SOL for every list P⃗ of closed terms (here: `value = ⊥` or that), and 𝒮_{n+1}(d) the terms
M with M N ∈ 𝒮ₙ(d(a)) for every a ∈ 𝔻ₙ and every closed N ∈ 𝒮ₙ(a). -/
def Computable (model : DdLP96Model) : Nat → model.Value → Term → Prop
  | 0, value, term =>
      value = model.bottom ∨ ∀ arguments, AllClosed arguments → Solvable (applyAll term arguments)
  | level + 1, value, term =>
      ∀ argumentValue argument, model.Compact level argumentValue → Closed argument →
        Computable model level argumentValue argument →
          Computable model level (model.apply value argumentValue) (.application term argument)

/-- The record's (D): d ⊑ d′ in 𝔻ₙ gives 𝒮ₙ(d′) ⊆ 𝒮ₙ(d). -/
theorem computableDown : ∀ (level : Nat) {lower upper : model.Value} {term : Term},
    model.Compact level lower → model.Compact level upper → model.below lower upper →
      model.Computable level upper term → model.Computable level lower term
  | 0, _, _, _, _, _, below, computable => by
      rcases computable with isBottom | solvable
      · rw [isBottom] at below
        exact .inl (model.bottomOfBelowBottom below)
      · exact .inr solvable
  | level + 1, _, _, _, lowerCompact, upperCompact, below, computable => by
      intro argumentValue argument argumentCompact closed argumentComputable
      exact computableDown level (model.compactApply lowerCompact argumentValue)
        (model.compactApply upperCompact argumentValue)
        (model.applyMonotoneFunction below argumentValue)
        (computable argumentValue argument argumentCompact closed argumentComputable)

/-- The record's (H): 𝒮ₙ(d) is closed under ⇛ in both directions. -/
theorem computableExpands : ∀ (level : Nat) {value : model.Value} {term other : Term},
    Expands term other → (model.Computable level value term ↔ model.Computable level value other)
  | 0, _, _, _, expands => by
      constructor
      · rintro (isBottom | solvable)
        · exact .inl isBottom
        · exact .inr fun arguments closed => (expands arguments closed).mp (solvable arguments closed)
      · rintro (isBottom | solvable)
        · exact .inl isBottom
        · exact .inr fun arguments closed => (expands arguments closed).mpr (solvable arguments closed)
  | level + 1, _, _, _, expands => by
      constructor
      · intro computable argumentValue argument compact closed argumentComputable
        exact (computableExpands level (expands.application closed)).mp
          (computable argumentValue argument compact closed argumentComputable)
      · intro computable argumentValue argument compact closed argumentComputable
        exact (computableExpands level (expands.application closed)).mpr
          (computable argumentValue argument compact closed argumentComputable)

/-- The record's (V): x M⃗ is in every 𝒮ₙ(d). -/
theorem computableStuck : ∀ (level : Nat) {value : model.Value} {term : Term},
    StuckSpine term → model.Computable level value term
  | 0, _, _, stuck => .inr fun arguments _ => solvableOfStuckSpine (stuck.applyAll arguments)
  | level + 1, _, _, stuck => fun _ _ _ _ _ => computableStuck level (.application _ stuck)

/-- A term M with M P⃗ ∈ SOL for every list P⃗ of closed terms is in every 𝒮ₙ(d): at level 0 by the
definition, and at level n + 1 because M N has the same property for every closed N. `top` is such a
term (`solvableApplicationsTop`). -/
theorem computableOfSolvableApplications : ∀ (level : Nat) {value : model.Value} {term : Term},
    (∀ arguments, AllClosed arguments → Solvable (applyAll term arguments)) →
      model.Computable level value term
  | 0, _, _, solvable => .inr solvable
  | level + 1, _, _, solvable => fun _ argument _ closed _ =>
      computableOfSolvableApplications level fun arguments allClosed =>
        solvable (argument :: arguments) (allClosedCons closed allClosed)

/-- The record's (L): d ∈ 𝔻ₙ gives 𝒮ₙ(d) = 𝒮_{n+1}(d). At level 0 it uses lemma X with the
closed argument `top`, which is in 𝒮₀(⊤) by `computableOfSolvableApplications`. -/
theorem computableSucc : ∀ (level : Nat) {value : model.Value} {term : Term},
    model.Compact level value →
      (model.Computable level value term ↔ model.Computable (level + 1) value term)
  | 0, value, term, compact => by
      rcases model.compactZero compact with isBottom | isTop
      · subst isBottom
        constructor
        · intro _ argumentValue argument _ _ _
          show model.apply model.bottom argumentValue = model.bottom ∨ _
          exact .inl (model.applyBottom _)
        · intro _
          exact .inl rfl
      · subst isTop
        constructor
        · intro computable argumentValue argument _ closed _
          rcases computable with isBottom | solvable
          · exact absurd isBottom model.topNotBottom
          · show model.apply model.top argumentValue = model.bottom ∨ _
            exact .inr fun arguments closedArguments =>
              solvable (argument :: arguments) (allClosedCons closed closedArguments)
        · intro computable
          refine .inr fun arguments closedArguments => ?_
          cases arguments with
          | nil =>
              have applied := computable model.top ContextualPreorder.top (model.compactTop 0)
                closedTop (model.computableOfSolvableApplications 0 solvableApplicationsTop)
              rcases applied with isBottom | solvable
              · rw [model.applyTop] at isBottom
                exact absurd isBottom model.topNotBottom
              · exact solvableOfSolvableApplication (solvable [] allClosedNil)
          | cons argument rest =>
              have applied := computable model.bottom argument model.compactBottomZero
                (closedArguments argument List.mem_cons_self) (.inl rfl)
              rcases applied with isBottom | solvable
              · rw [model.applyTop] at isBottom
                exact absurd isBottom model.topNotBottom
              · exact solvable rest
                  (fun term member => closedArguments term (List.mem_cons_of_mem _ member))
  | level + 1, value, term, compact => by
      constructor
      · intro computable argumentValue argument argumentCompact closed argumentComputable
        have lowered : model.Compact level (model.project level argumentValue) :=
          model.compactProject level argumentValue
        have argumentDown := model.computableDown (level + 1) (model.compactRaise lowered)
          argumentCompact (model.projectBelow level argumentValue) argumentComputable
        have argumentLevel := (computableSucc level lowered).mpr argumentDown
        have applied := computable _ argument lowered closed argumentLevel
        rw [model.compactApplyArgument compact argumentValue]
        exact (computableSucc level (model.compactApply compact _)).mp applied
      · intro computable argumentValue argument argumentCompact closed argumentComputable
        have applied := computable argumentValue argument (model.compactRaise argumentCompact) closed
          ((computableSucc level argumentCompact).mp argumentComputable)
        exact (computableSucc level (model.compactApply compact argumentValue)).mpr applied

/-- (L) iterated: d ∈ 𝔻ₙ gives 𝒮ₙ(d) = 𝒮_{n+k}(d). -/
theorem computableRaiseBy {level : Nat} {value : model.Value} {term : Term}
    (compact : model.Compact level value) :
    ∀ extra, model.Computable level value term ↔ model.Computable (level + extra) value term
  | 0 => Iff.rfl
  | extra + 1 => (computableRaiseBy compact extra).trans
      (model.computableSucc (level + extra) (model.compactRaiseBy compact extra))

/-- 𝒮(d) does not depend on the level d is taken at. -/
theorem computableAtLevel {level other : Nat} {value : model.Value} {term : Term}
    (compact : model.Compact level value) (otherCompact : model.Compact other value)
    (computable : model.Computable other value term) : model.Computable level value term := by
  have raised := (model.computableRaiseBy otherCompact level).mp computable
  rw [Nat.add_comm] at raised
  exact (model.computableRaiseBy compact other).mpr raised

/-- (D) across levels: d ⊑ d′, d and d′ compact at any levels. -/
theorem computableBelow {level other : Nat} {lower upper : model.Value} {term : Term}
    (lowerCompact : model.Compact level lower) (upperCompact : model.Compact other upper)
    (below : model.below lower upper) (computable : model.Computable other upper term) :
    model.Computable level lower term := by
  have upperRaised := (model.computableRaiseBy upperCompact level).mp computable
  rw [Nat.add_comm] at upperRaised
  have upperTotal := model.compactRaiseBy upperCompact level
  rw [Nat.add_comm] at upperTotal
  have lowered := model.computableDown (level + other) (model.compactRaiseBy lowerCompact other)
    upperTotal below upperRaised
  exact (model.computableRaiseBy lowerCompact other).mpr lowered

/-- The record's (+): 𝒮ₙ(d) is closed under +. -/
theorem computableChoice : ∀ (level : Nat) {value : model.Value} {left right : Term},
    model.Computable level value left → model.Computable level value right →
      model.Computable level value (.choice left right)
  | 0, _, left, right, leftComputable, rightComputable => by
      rcases leftComputable with isBottom | leftSolvable
      · exact .inl isBottom
      · rcases rightComputable with isBottom | rightSolvable
        · exact .inl isBottom
        · exact .inr fun arguments closed => (solvableChoiceSpine arguments left right).mpr
            ⟨leftSolvable arguments closed, rightSolvable arguments closed⟩
  | level + 1, _, left, right, leftComputable, rightComputable => by
      intro argumentValue argument compact closed argumentComputable
      exact (model.computableExpands level (expandsChoiceApplication left right argument)).mpr
        (computableChoice level (leftComputable argumentValue argument compact closed argumentComputable)
          (rightComputable argumentValue argument compact closed argumentComputable))

/-- ⊥ ⊔ ⊥ = ⊥. -/
theorem joinBottom : model.join model.bottom model.bottom = model.bottom :=
  model.bottomOfBelowBottom (model.joinLeast (model.orderReflexive _) (model.orderReflexive _))

/-- The record's (∥): M₁ ∈ 𝒮ₙ(d₁), M₂ ∈ 𝒮ₙ(d₂) give M₁ ∥ M₂ ∈ 𝒮ₙ(d₁ ⊔ d₂). -/
theorem computableParallel : ∀ (level : Nat) {leftValue rightValue : model.Value} {left right : Term},
    model.Compact level leftValue → model.Compact level rightValue →
      model.Computable level leftValue left → model.Computable level rightValue right →
        model.Computable level (model.join leftValue rightValue) (.parallel left right)
  | 0, _, _, left, right, _, _, leftComputable, rightComputable => by
      rcases leftComputable with leftBottom | leftSolvable
      · rcases rightComputable with rightBottom | rightSolvable
        · rw [leftBottom, rightBottom]
          exact .inl model.joinBottom
        · exact .inr fun arguments closed => (solvableParallelSpine arguments left right).mpr
            (.inr (rightSolvable arguments closed))
      · exact .inr fun arguments closed => (solvableParallelSpine arguments left right).mpr
          (.inl (leftSolvable arguments closed))
  | level + 1, _, _, left, right, leftCompact, rightCompact, leftComputable, rightComputable => by
      intro argumentValue argument compact closed argumentComputable
      rw [model.applyJoin]
      exact (model.computableExpands level (expandsParallelApplication left right argument)).mpr
        (computableParallel level (model.compactApply leftCompact argumentValue)
          (model.compactApply rightCompact argumentValue)
          (leftComputable argumentValue argument compact closed argumentComputable)
          (rightComputable argumentValue argument compact closed argumentComputable))

/-- The record's (CA′): d ∈ 𝔻ₙ, d ≠ ⊥ and M ∈ 𝒮ₙ(d) give M ∈ SOL. At level n + 1, d(⊤) ≠ ⊥ by
(P6), `top` ∈ 𝒮ₙ(⊤) by `computableOfSolvableApplications`, and lemma X takes M `top` ∈ SOL back to M. -/
theorem solvableOfComputable : ∀ (level : Nat) {value : model.Value} {term : Term},
    model.Compact level value → value ≠ model.bottom → model.Computable level value term →
      Solvable term
  | 0, _, _, _, notBottom, computable => by
      rcases computable with isBottom | solvable
      · exact absurd isBottom notBottom
      · exact solvable [] allClosedNil
  | level + 1, value, _, compact, notBottom, computable => by
      have appliedNotBottom : model.apply value model.top ≠ model.bottom := by
        intro isBottom
        apply notBottom
        apply model.bottomOfBelowBottom
        apply model.extensional.mpr
        intro argument
        rw [model.applyBottom, ← isBottom]
        exact model.applyMonotoneArgument value (model.topGreatest argument)
      have applied := computable model.top ContextualPreorder.top (model.compactTop level) closedTop
        (model.computableOfSolvableApplications level solvableApplicationsTop)
      exact solvableOfSolvableApplication
        (solvableOfComputable level (model.compactApply compact _) appliedNotBottom applied)

/-! ## The basic lemma 4.3 -/

/-- The hypothesis of the basic lemma on a closing substitution: the i-th replacement is closed
and is in 𝒮(aᵢ), where aᵢ = ρ(i) is compact. -/
def ReplacementsComputable (replacements : List Term) (environment : Nat → model.Value) : Prop :=
  ∀ index replacement, replacements[index]? = some replacement →
    Closed replacement ∧ ∃ level, model.Compact level (environment index) ∧
      model.Computable level (environment index) replacement

/-- The replacements of the hypothesis are closed. -/
theorem ReplacementsComputable.allClosed {replacements : List Term} {environment : Nat → model.Value}
    (computable : model.ReplacementsComputable replacements environment) :
    AllClosed replacements := by
  intro term member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
  exact (computable index term found).1

/-- The hypothesis extended by a closed N ∈ 𝒮(a) for a new index 0. -/
theorem ReplacementsComputable.extend {replacements : List Term} {environment : Nat → model.Value}
    (computable : model.ReplacementsComputable replacements environment) {argument : Term}
    {argumentValue : model.Value} {level : Nat} (closed : Closed argument)
    (compact : model.Compact level argumentValue)
    (argumentComputable : model.Computable level argumentValue argument) :
    model.ReplacementsComputable (argument :: replacements)
      (extendEnvironment argumentValue environment) := by
  intro index replacement found
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨closed, level, compact, argumentComputable⟩
  | succ index =>
      simp only [List.getElem?_cons_succ] at found
      exact computable index replacement found

/-- The record's lemma 4.3, the basic lemma, for closing substitutions: if FV(M) is below the
length of a list of closed replacements Nᵢ ∈ 𝒮(ρ(i)) with ρ(i) compact, and d is compact with
d ⊑ [[M]]ρ, then M[i := Nᵢ] ∈ 𝒮(d). By induction on M, as the record's proof. -/
theorem basicLemma : ∀ (term : Term) {replacements : List Term} {environment : Nat → model.Value},
    FreeBelow replacements.length term → model.ReplacementsComputable replacements environment →
      ∀ {level : Nat} {value : model.Value}, model.Compact level value →
        model.below value (model.interpret term environment) →
          model.Computable level value (closeAll 0 replacements term)
  | .boundVariable index, replacements, environment, free, computable, level, value, compact,
      below => by
      have inRange : index < replacements.length := free index rfl
      obtain ⟨replacement, found⟩ :
          ∃ replacement, replacements[index]? = some replacement :=
        ⟨replacements[index], List.getElem?_eq_getElem inRange⟩
      rw [closeAllVariable computable.allClosed found]
      rw [model.interpretVariable] at below
      obtain ⟨_, otherLevel, otherCompact, otherComputable⟩ := computable index replacement found
      exact model.computableBelow compact otherCompact below otherComputable
  | .choice left right, replacements, environment, free, computable, level, value, compact,
      below => by
      rw [closeAllChoice]
      rw [model.interpretChoice] at below
      exact model.computableChoice level
        (basicLemma left (fun index occurs => free index (.inl occurs)) computable compact
          (model.orderTransitive below (model.meetBelowLeft _ _)))
        (basicLemma right (fun index occurs => free index (.inr occurs)) computable compact
          (model.orderTransitive below (model.meetBelowRight _ _)))
  | .parallel left right, replacements, environment, free, computable, level, value, compact,
      below => by
      rw [closeAllParallel]
      rw [model.interpretParallel] at below
      -- m₁ ⊔ m₂ is the least upper bound of the chain Pₖ m₁ ⊔ Pₖ m₂, so the compact d is below one
      -- member of it.
      obtain ⟨index, chainBelow⟩ := model.compact level value
        (fun index => model.join (model.project index (model.interpret left environment))
          (model.project index (model.interpret right environment)))
        (model.join (model.interpret left environment) (model.interpret right environment))
        compact
        (fun index => model.joinMonotone (model.projectIncreasing _ _) (model.projectIncreasing _ _))
        (fun upper bounds => model.joinLeast
          (model.projectLeast _ upper fun index =>
            model.orderTransitive (model.joinAboveLeft _ _) (bounds index))
          (model.projectLeast _ upper fun index =>
            model.orderTransitive (model.joinAboveRight _ _) (bounds index)))
        below
      have valueCompact := model.compactRaiseBy compact index
      have leftProjected := model.compactRaiseBy
        (model.compactProject index (model.interpret left environment)) level
      have rightProjected := model.compactRaiseBy
        (model.compactProject index (model.interpret right environment)) level
      rw [Nat.add_comm] at leftProjected rightProjected
      have leftPartCompact := model.compactMeet valueCompact leftProjected
      have rightPartCompact := model.compactMeet valueCompact rightProjected
      have leftComputable := basicLemma left (fun index occurs => free index (.inl occurs))
        computable leftPartCompact
        (model.orderTransitive (model.meetBelowRight _ _) (model.projectBelow _ _))
      have rightComputable := basicLemma right (fun index occurs => free index (.inr occurs))
        computable rightPartCompact
        (model.orderTransitive (model.meetBelowRight _ _) (model.projectBelow _ _))
      have joined := model.computableParallel (level + index) leftPartCompact rightPartCompact
        leftComputable rightComputable
      -- d = d ⊓ (Pₖ m₁ ⊔ Pₖ m₂) ⊑ (d ⊓ Pₖ m₁) ⊔ (d ⊓ Pₖ m₂), by distributivity (E1).
      have valueBelow := model.orderTransitive
        (model.meetGreatest (model.orderReflexive value) chainBelow)
        (model.distributive value _ _)
      exact model.computableBelow compact (model.compactJoin leftPartCompact rightPartCompact)
        valueBelow joined
  | .application function argument, replacements, environment, free, computable, level, value,
      compact, below => by
      rw [closeAllApplication]
      rw [model.interpretApplication] at below
      -- x(y) is the least upper bound of the chain x_{n+1}(yₙ) (P7), so the compact d is below one
      -- member of it.
      obtain ⟨index, chainBelow⟩ := model.compact level value
        (fun index => model.apply (model.project (index + 1) (model.interpret function environment))
          (model.project index (model.interpret argument environment)))
        (model.apply (model.interpret function environment) (model.interpret argument environment))
        compact
        (fun index => model.orderTransitive
          (model.applyMonotoneFunction (model.projectIncreasing _ _) _)
          (model.applyMonotoneArgument _ (model.projectIncreasing _ _)))
        (model.applyLeast _ _)
        below
      have functionComputable := basicLemma function (fun index occurs => free index (.inl occurs))
        computable (model.compactProject (index + 1) _) (model.projectBelow _ _)
      have argumentComputable := basicLemma argument (fun index occurs => free index (.inr occurs))
        computable (model.compactProject index _) (model.projectBelow _ _)
      have argumentClosed := closeAllClosesTerm computable.allClosed
        (fun index occurs => free index (.inr occurs))
      have applied := functionComputable _ _ (model.compactProject index _) argumentClosed
        argumentComputable
      exact model.computableBelow compact
        (model.compactApply (model.compactProject (index + 1) _) _) chainBelow applied
  | .abstraction body, replacements, environment, free, computable, level, value, compact,
      below => by
      rw [closeAllAbstraction computable.allClosed]
      apply model.computableAtLevel compact (model.compactRaise compact)
      intro argumentValue argument argumentCompact closed argumentComputable
      have bodyBelow : model.below (model.apply value argumentValue)
          (model.interpret body (extendEnvironment argumentValue environment)) := by
        rw [← model.interpretAbstraction]
        exact model.applyMonotoneFunction below argumentValue
      have bodyFree : FreeBelow (argument :: replacements).length body := by
        intro index occurs
        cases index with
        | zero => simp
        | succ index =>
            have inner := free index occurs
            simp only [List.length_cons]
            omega
      have bodyComputable := basicLemma body bodyFree
        (ReplacementsComputable.extend model computable closed argumentCompact argumentComputable)
        (model.compactApply (model.compactRaise compact) argumentValue) bodyBelow
      rw [← instantiateCloseAll computable.allClosed closed] at bodyComputable
      exact (model.computableExpands level (expandsBeta _ _)).mpr bodyComputable

/-! ## Theorem 4.1, corollary 4.2, theorem 6.1, section 5 -/

/-- The record's theorem 4.1, direction ⇐, given a model satisfying the fields of `DdLP96Model`:
[[M]]ρ_⊤ ≠ ⊥ gives M ∈ SOL. Some Pₙ([[M]]ρ_⊤) is not ⊥ (P3); the basic lemma with `top` for every free
index (`top` ∈ 𝒮(⊤) by `computableOfSolvableApplications`) puts the closed instance of M in
𝒮ₙ(Pₙ([[M]]ρ_⊤)); (CA′) makes it solvable, and so is M. -/
theorem solvableOfInterpretNotBottom {term : Term}
    (notBottom : model.interpret term model.topEnvironment ≠ model.bottom) : Solvable term := by
  obtain ⟨bound, free⟩ := freeBound term
  have someLevel : ∃ level, model.project level (model.interpret term model.topEnvironment) ≠
      model.bottom := by
    refine Classical.byContradiction fun none => notBottom ?_
    apply model.bottomOfBelowBottom
    apply model.projectLeast
    intro level
    have isBottom : model.project level (model.interpret term model.topEnvironment) = model.bottom :=
      Classical.byContradiction fun notEqual => none ⟨level, notEqual⟩
    rw [isBottom]
    exact model.orderReflexive _
  obtain ⟨level, projectedNotBottom⟩ := someLevel
  have replacementsComputable :
      model.ReplacementsComputable (List.replicate bound ContextualPreorder.top) model.topEnvironment := by
    intro index replacement found
    rw [List.getElem?_replicate] at found
    split at found
    · simp only [Option.some.injEq] at found
      subst found
      exact ⟨closedTop, 0, model.compactTop 0,
        model.computableOfSolvableApplications 0 solvableApplicationsTop⟩
    · exact absurd found (by simp)
  have computable := model.basicLemma term (by rw [List.length_replicate]; exact free)
    replacementsComputable (model.compactProject level _) (model.projectBelow _ _)
  exact solvableOfCloseAll _ 0
    (model.solvableOfComputable level (model.compactProject level _) projectedNotBottom computable)

/-- The record's theorem 4.1, given a model satisfying the fields of `DdLP96Model`: M ∈ SOL if and
only if [[M]]ρ_⊤ ≠ ⊥. -/
theorem solvableIffInterpretNotBottom {term : Term} :
    Solvable term ↔ model.interpret term model.topEnvironment ≠ model.bottom :=
  ⟨model.interpretNotBottomOfSolvable, model.solvableOfInterpretNotBottom⟩

/-- The reading is monotone in a hole: [[M]]ρ ⊑ [[N]]ρ for every ρ gives [[C[M]]]ρ ⊑ [[C[N]]]ρ for
every ρ (application, ⊓ and ⊔ are monotone; λ by (P6)). -/
theorem interpretFillBelow {lower upper : Term}
    (below : ∀ environment, model.below (model.interpret lower environment)
      (model.interpret upper environment)) :
    ∀ (context : Context) (environment : Nat → model.Value),
      model.below (model.interpret (context.fill lower) environment)
        (model.interpret (context.fill upper) environment)
  | .hole, environment => below environment
  | .abstraction body, environment => model.extensional.mpr fun value => by
      simp only [Context.fill]
      rw [model.interpretAbstraction, model.interpretAbstraction]
      exact interpretFillBelow below body _
  | .applicationFunction function argument, environment => by
      simp only [Context.fill]
      rw [model.interpretApplication, model.interpretApplication]
      exact model.applyMonotoneFunction (interpretFillBelow below function environment) _
  | .applicationArgument function argument, environment => by
      simp only [Context.fill]
      rw [model.interpretApplication, model.interpretApplication]
      exact model.applyMonotoneArgument _ (interpretFillBelow below argument environment)
  | .choiceLeft left right, environment => by
      simp only [Context.fill]
      rw [model.interpretChoice, model.interpretChoice]
      exact model.meetMonotone (interpretFillBelow below left environment) (model.orderReflexive _)
  | .choiceRight left right, environment => by
      simp only [Context.fill]
      rw [model.interpretChoice, model.interpretChoice]
      exact model.meetMonotone (model.orderReflexive _) (interpretFillBelow below right environment)
  | .parallelLeft left right, environment => by
      simp only [Context.fill]
      rw [model.interpretParallel, model.interpretParallel]
      exact model.joinMonotone (interpretFillBelow below left environment) (model.orderReflexive _)
  | .parallelRight left right, environment => by
      simp only [Context.fill]
      rw [model.interpretParallel, model.interpretParallel]
      exact model.joinMonotone (model.orderReflexive _) (interpretFillBelow below right environment)

/-- The record's corollary 4.2, given a model satisfying the fields of `DdLP96Model`: if
[[M]]ρ ⊑ [[N]]ρ for every environment ρ, then M ⊑_O N. -/
theorem contextualPreorderOfInterpretBelow {lower upper : Term}
    (below : ∀ environment, model.below (model.interpret lower environment)
      (model.interpret upper environment)) : ContextualPreorder lower upper := by
  intro context solvable
  apply model.solvableOfInterpretNotBottom
  intro isBottom
  apply model.interpretNotBottomOfSolvable solvable
  apply model.bottomOfBelowBottom
  rw [← isBottom]
  exact model.interpretFillBelow below context _

/-- Corollary 4.2 for equal readings: M ≃_O N when [[M]]ρ = [[N]]ρ for every ρ. -/
theorem contextualEquivalenceOfInterpretEqual {left right : Term}
    (equal : ∀ environment, model.interpret left environment = model.interpret right environment) :
    ContextualEquivalence left right :=
  ⟨model.contextualPreorderOfInterpretBelow fun environment => by
      rw [equal environment]
      exact model.orderReflexive _,
    model.contextualPreorderOfInterpretBelow fun environment => by
      rw [equal environment]
      exact model.orderReflexive _⟩

end DdLP96Model

/-! ## K and K* -/

/-- λx. x. -/
def identity : Term := .abstraction (.boundVariable 0)

/-- Ω has the one successor Ω. -/
theorem uniqueSuccessorOmega : ∀ result, HeadStep Omega result ↔ result = Omega := by
  intro result
  constructor
  · intro step
    cases step with
    | beta => rfl
    | function _ notOther _ => exact absurd notOther id
  · intro equal
    subst equal
    exact .beta _ _

/-- Ω is not solvable: its one successor is itself, so it has reduction sequences of every length. -/
theorem notSolvableOmega : ¬ Solvable Omega := by
  intro ⟨steps, bounded⟩
  induction steps with
  | zero => exact bounded Omega ((uniqueSuccessorOmega Omega).mpr rfl)
  | succ steps inner =>
      exact inner ((headReductionsAtMostOfUniqueSuccessor uniqueSuccessorOmega steps).mp bounded)

/-- The record's section 6: K ≄_O K*. The context [ ] Ω I sends K* to I, which is solvable, and K
to Ω, which is not. -/
theorem notContextuallyEquivalentFirstSecond : ¬ ContextualEquivalence first second := by
  intro ⟨_, secondBelowFirst⟩
  have secondSolvable : Solvable
      ((Context.applicationFunction (.applicationFunction .hole Omega) identity).fill second) := by
    show Solvable (applyAll (.application (.abstraction (.abstraction (.boundVariable 0))) Omega)
      [identity])
    rw [solvableBetaSpine]
    show Solvable (applyAll (.application (.abstraction (.boundVariable 0)) identity) [])
    rw [solvableBetaSpine]
    exact solvableOfHeadNormalForm (.abstraction (.stuck (.boundVariable 0)))
  have firstSolvable := secondBelowFirst _ secondSolvable
  apply notSolvableOmega
  revert firstSolvable
  show Solvable (applyAll (.application (.abstraction (.abstraction (.boundVariable 1))) Omega)
    [identity]) → Solvable Omega
  rw [solvableBetaSpine]
  show Solvable (applyAll (.application (.abstraction (shift Omega)) identity) []) → Solvable Omega
  rw [solvableBetaSpine, shiftClosed closedOmega]
  show Solvable (instantiate Omega identity) → Solvable Omega
  rw [instantiateOmega]
  exact id

end LambdaJit.ContextualPreorder
