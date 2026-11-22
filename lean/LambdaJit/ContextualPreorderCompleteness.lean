import LambdaJit.ContextualPreorderBridge
import LambdaJit.ContextualPreorderSeparationProof

/-!
# Lemma C of the proofs file's section 20, and the reading of head nodes

Proved here, given a model satisfying the fields of `DdLP96Model`: the proofs file's lemma C
(the proofs file, section 20.3;
`DdLP96Model.interpretBelowOfNotConflicts`: a stratified approximant that does not conflict with
a βη normal form reads below it in every environment), with the readings of Ω, of η expansions and
of head nodes it rests on (`DdLP96Model.interpretOmega`, `interpretEtaExpand`, `interpretPadded`,
`interpretHeadNodeMonotone`), and the shifting lemmas of spines (`shiftTimesApplyAll` and its
companions). The completeness for ⊢_{λ-lattice-η} (`DdLP96Model.completenessLatticeEta`, module
`LatticeEtaSeparation`) uses them with its corollary C1.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Term lemmas for the η expansion of head nodes -/

theorem shiftTimesApplication : ∀ (count : Nat) (function argument : Term),
    shiftTimes count (.application function argument) =
      .application (shiftTimes count function) (shiftTimes count argument)
  | 0, _, _ => rfl
  | count + 1, function, argument => by
      show shift (shiftTimes count (.application function argument)) = _
      rw [shiftTimesApplication count function argument]
      rfl

theorem shiftTimesVariable : ∀ (count index : Nat),
    shiftTimes count (.boundVariable index) = .boundVariable (index + count)
  | 0, _ => rfl
  | count + 1, index => by
      show shift (shiftTimes count (.boundVariable index)) = _
      rw [shiftTimesVariable count index]
      show shiftFrom 0 (.boundVariable (index + count)) = _
      simp [shiftFrom]
      omega

theorem shiftTimesShift : ∀ (count : Nat) (term : Term),
    shiftTimes count (shift term) = shiftTimes (count + 1) term
  | 0, _ => rfl
  | count + 1, term => by
      show shift (shiftTimes count (shift term)) = shift (shiftTimes (count + 1) term)
      rw [shiftTimesShift count term]

theorem shiftTimesApplyAll : ∀ (count : Nat) (head : Term) (arguments : List Term),
    shiftTimes count (applyAll head arguments) =
      applyAll (shiftTimes count head) (arguments.map (shiftTimes count))
  | 0, _, arguments => by simp [shiftTimes]
  | count + 1, head, arguments => by
      show shift (shiftTimes count (applyAll head arguments)) = _
      rw [shiftTimesApplyAll count head arguments]
      show shiftFrom 0 _ = _
      rw [shiftFromApplyAll, List.map_map]
      rfl

theorem abstractAllAdd : ∀ (outer inner : Nat) (body : Term),
    abstractAll (outer + inner) body = abstractAll outer (abstractAll inner body)
  | 0, inner, body => by simp [abstractAll]
  | outer + 1, inner, body => by
      rw [Nat.add_right_comm]
      show Term.abstraction (abstractAll (outer + inner) body) = _
      rw [abstractAllAdd outer inner body]
      rfl

namespace DdLP96Model

variable (model : DdLP96Model)

/-! ## The reading of head nodes -/

/-- Ω reads as ⊥ in every environment: it is closed and not solvable (theorem 4.1). -/
theorem interpretOmega (environment : Nat → model.Value) :
    model.interpret Omega environment = model.bottom := by
  rw [model.interpretClosed closedOmega environment]
  exact Classical.byContradiction fun notBottom =>
    notSolvableOmega (model.solvableOfInterpretNotBottom notBottom)

/-- The reading respects λ: equal bodies in every environment give equal readings under
`count` abstractions. -/
theorem interpretAbstractAllCongruence : ∀ (count : Nat) {left right : Term},
    (∀ environment, model.interpret left environment = model.interpret right environment) →
      ∀ environment, model.interpret (abstractAll count left) environment =
        model.interpret (abstractAll count right) environment
  | 0, _, _, equal => equal
  | count + 1, _, _, equal =>
      model.interpretAbstractionCongruence (interpretAbstractAllCongruence count equal)

/-- The η rule `count` times: M = λx₁ … x_k. M x₁ … x_k, the new binders innermost. -/
theorem interpretEtaExpand : ∀ (extra : Nat) (body : Term) (environment : Nat → model.Value),
    model.interpret (abstractAll extra (applyAll (shiftTimes extra body) (trailingVariables extra)))
      environment = model.interpret body environment
  | 0, _, _ => rfl
  | extra + 1, body, environment => by
      have rewritten : abstractAll (extra + 1)
          (applyAll (shiftTimes (extra + 1) body) (trailingVariables (extra + 1))) =
          .abstraction (abstractAll extra
            (applyAll (shiftTimes extra (.application (shift body) (.boundVariable 0)))
              (trailingVariables extra))) := by
        rw [shiftTimesApplication, shiftTimesShift, shiftTimesVariable, Nat.zero_add]
        rfl
      rw [rewritten, model.interpretAbstractionCongruence
        (interpretEtaExpand extra (.application (shift body) (.boundVariable 0))) environment]
      exact model.interpretEta body environment

/-- Section 14.1's η expansion alignment: a head node reads as its expansion to `extra` more
abstractions, with the head raised and the arguments padded. -/
theorem interpretPadded (abstractions head : Nat) (arguments : List Term) (extra : Nat)
    (environment : Nat → model.Value) :
    model.interpret (headNode abstractions head arguments) environment =
      model.interpret (headNode (abstractions + extra) (head + extra)
        (paddedArguments extra arguments)) environment := by
  unfold headNode paddedArguments
  rw [abstractAllAdd, applyAllAppendAll, ← shiftTimesVariable, ← shiftTimesApplyAll]
  exact model.interpretAbstractAllCongruence abstractions
    (fun environment => (model.interpretEtaExpand extra _ environment).symm) environment

/-- The reading is monotone under abstractions. -/
theorem interpretAbstractAllMonotone : ∀ (count : Nat) {lower upper : Term},
    (∀ environment, model.below (model.interpret lower environment)
      (model.interpret upper environment)) →
      ∀ environment, model.below (model.interpret (abstractAll count lower) environment)
        (model.interpret (abstractAll count upper) environment)
  | 0, _, _, below => below
  | count + 1, _, _, below => fun environment => model.extensional.mpr fun value => by
      show model.below (model.apply (model.interpret (.abstraction (abstractAll count _)) environment) value)
        (model.apply (model.interpret (.abstraction (abstractAll count _)) environment) value)
      rw [model.interpretAbstraction, model.interpretAbstraction]
      exact interpretAbstractAllMonotone count below _

/-- The reading is monotone in the head and the arguments of a spine. -/
theorem interpretApplyAllMonotone : ∀ {lowerHead upperHead : Term} {lowers uppers : List Term},
    (∀ environment, model.below (model.interpret lowerHead environment)
      (model.interpret upperHead environment)) →
    lowers.length = uppers.length →
    (∀ (position : Nat) lower upper, lowers[position]? = some lower → uppers[position]? = some upper →
      ∀ environment, model.below (model.interpret lower environment)
        (model.interpret upper environment)) →
      ∀ environment, model.below (model.interpret (applyAll lowerHead lowers) environment)
        (model.interpret (applyAll upperHead uppers) environment)
  | _, _, [], [], headBelow, _, _ => headBelow
  | _, _, [], _ :: _, _, sameLength, _ => absurd sameLength (by simp)
  | _, _, _ :: _, [], _, sameLength, _ => absurd sameLength (by simp)
  | lowerHead, upperHead, lower :: lowerRest, upper :: upperRest, headBelow, sameLength,
      pointwise => by
      apply interpretApplyAllMonotone (lowerHead := .application lowerHead lower)
        (upperHead := .application upperHead upper)
      · intro environment
        rw [model.interpretApplication, model.interpretApplication]
        exact model.orderTransitive (model.applyMonotoneFunction (headBelow environment) _)
          (model.applyMonotoneArgument _ (pointwise 0 lower upper rfl rfl environment))
      · simpa using sameLength
      · intro position lowerArgument upperArgument lowerFound upperFound
        exact pointwise (position + 1) lowerArgument upperArgument lowerFound upperFound

/-- Lemma 14.4b's step at a head node: the same head under the same abstractions, with arguments
below one another position by position, reads below. -/
theorem interpretHeadNodeMonotone (abstractions head : Nat) {lowers uppers : List Term}
    (sameLength : lowers.length = uppers.length)
    (pointwise : ∀ (position : Nat) lower upper, lowers[position]? = some lower →
      uppers[position]? = some upper →
        ∀ environment, model.below (model.interpret lower environment)
          (model.interpret upper environment)) :
    ∀ environment, model.below (model.interpret (headNode abstractions head lowers) environment)
      (model.interpret (headNode abstractions head uppers) environment) :=
  model.interpretAbstractAllMonotone abstractions
    (model.interpretApplyAllMonotone (fun _ => model.orderReflexive _) sameLength pointwise)

/-! ## Lemma C -/

/-- The proofs file's lemma C (section 20.3), given a model satisfying the fields of
`DdLP96Model`: a stratified approximant A and a β normal form N with A ⋪ N false read
[[A]]ρ ⊑ [[N]]ρ in every environment ρ. By induction on |A| + |N|, as the proofs file: ⋄ reads ⊥;
0 conflicts; a parallel has both sides below; a choice has one side below; at a head node, both
sides η-expanded to the same abstractions have the same head and arguments below one another
(lemma 14.4b). -/
theorem interpretBelowOfNotConflicts : ∀ (bound : Nat) {approximant candidate : Term},
    termSize approximant + termSize candidate < bound →
    Stratified approximant → BetaNormal candidate → ¬ Conflicts approximant candidate →
      ∀ environment, model.below (model.interpret approximant environment)
        (model.interpret candidate environment)
  | 0, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, approximant, candidate, small, stratified, normal, notConflicts => by
      cases stratified with
      | truncated =>
          intro environment
          rw [model.interpretOmega]
          exact model.bottomLeast _
      | @choice left right leftStratified rightStratified =>
          simp only [termSize] at small
          intro environment
          rw [model.interpretChoice]
          rcases Classical.em (Conflicts left candidate) with leftConflicts | leftFine
          · have rightFine : ¬ Conflicts right candidate := fun rightConflicts =>
              notConflicts (.choice leftConflicts rightConflicts)
            exact model.orderTransitive (model.meetBelowRight _ _)
              (interpretBelowOfNotConflicts bound (by omega) rightStratified normal rightFine
                environment)
          · exact model.orderTransitive (model.meetBelowLeft _ _)
              (interpretBelowOfNotConflicts bound (by omega) leftStratified normal leftFine
                environment)
      | @parallel left right leftStratified rightStratified =>
          simp only [termSize] at small
          intro environment
          rw [model.interpretParallel]
          exact model.joinLeast
            (interpretBelowOfNotConflicts bound (by omega) leftStratified normal
              (fun conflicts => notConflicts (.parallelLeft right conflicts)) environment)
            (interpretBelowOfNotConflicts bound (by omega) rightStratified normal
              (fun conflicts => notConflicts (.parallelRight left conflicts)) environment)
      | headNode abstractions head arguments argumentsStratified =>
          cases normal with
          | headNode candidateAbstractions candidateHead candidateArguments candidateNormal =>
              rw [termSizeHeadNode, termSizeHeadNode] at small
              have agree : RootAgree abstractions head arguments.length candidateAbstractions
                  candidateHead candidateArguments.length :=
                Classical.byContradiction fun disagree =>
                  notConflicts (.rootDisagree _ _ _ _ _ _ disagree)
              have maximum : max abstractions candidateAbstractions = abstractions ∨
                  max abstractions candidateAbstractions = candidateAbstractions := by
                rcases Nat.le_total abstractions candidateAbstractions with ordered | ordered
                · exact .inr (Nat.max_eq_right ordered)
                · exact .inl (Nat.max_eq_left ordered)
              have aboveLeft := Nat.le_max_left abstractions candidateAbstractions
              have aboveRight := Nat.le_max_right abstractions candidateAbstractions
              have sameLength :
                  (paddedArguments (max abstractions candidateAbstractions - abstractions)
                    arguments).length =
                  (paddedArguments (max abstractions candidateAbstractions - candidateAbstractions)
                    candidateArguments).length := by
                rw [lengthPaddedArguments, lengthPaddedArguments]
                exact agree.2
              have pointwise : ∀ (position : Nat) lower upper,
                  (paddedArguments (max abstractions candidateAbstractions - abstractions)
                    arguments)[position]? = some lower →
                  (paddedArguments (max abstractions candidateAbstractions - candidateAbstractions)
                    candidateArguments)[position]? = some upper →
                  ∀ environment, model.below (model.interpret lower environment)
                    (model.interpret upper environment) := by
                intro position lower upper lowerFound upperFound
                have lowerSize := termSizePaddedArgument lowerFound
                have upperSize := termSizePaddedArgument upperFound
                apply interpretBelowOfNotConflicts bound
                · rcases lowerSize with lowerSmall | ⟨lowerOne, lowerExtra⟩ <;>
                    rcases upperSize with upperSmall | ⟨upperOne, upperExtra⟩ <;> omega
                · exact stratifiedPaddedArguments argumentsStratified _ lower
                    (List.mem_of_getElem? lowerFound)
                · exact betaNormalPaddedArguments candidateNormal _ upper
                    (List.mem_of_getElem? upperFound)
                · exact fun conflicts =>
                    notConflicts (.argument _ _ _ _ _ _ position agree lowerFound upperFound conflicts)
              intro environment
              rw [model.interpretPadded abstractions head arguments
                  (max abstractions candidateAbstractions - abstractions),
                model.interpretPadded candidateAbstractions candidateHead candidateArguments
                  (max abstractions candidateAbstractions - candidateAbstractions)]
              have sameAbstractions :
                  abstractions + (max abstractions candidateAbstractions - abstractions) =
                    candidateAbstractions +
                      (max abstractions candidateAbstractions - candidateAbstractions) := by
                omega
              rw [sameAbstractions, agree.1]
              exact model.interpretHeadNodeMonotone _ _ sameLength pointwise environment

end DdLP96Model

end LambdaJit.ContextualPreorder
