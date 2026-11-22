import LambdaJit.LatticeEtaXi

/-!
# Theorem A in ⊢_{λ-lattice-η}

The proofs file's theorem A (section 20.2, with
lemma C0 of section 20.3) in ⊢_{λ-lattice-η} (module `LatticeEtaDerivability`, the proofs
file's ⊢_B of section 21):
for a closed T and a compact d ⊑ [[T]], some closed T′ with ∅ ⊢_{λ-lattice-η} T = T′ has a
stratified truncation A with d ⊑ [[A]] (`DdLP96Model.approximationLatticeEta`).

The proof is section 20.2's, each declaration named after its step with the suffix `LatticeEta`.
It differs from the proofs file, which reads the theorem in the derivability with the unit law:

- the proofs file's cases at 0 ((Z), T5 and T6) have no counterpart here;
- the equations used are those of ⊢_{λ-lattice-η}: β, η, (8), (9), T7, T8 and the congruences, which
  module `LatticeEtaDerivability` derives with no unit law.

The declarations that do not mention the derivability (the reading of head nodes, lemma C0's
substitution of ⋄, `bindVariable`, the free indices of redexes) are those of module
`ContextualPreorderApproximation`.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Lemma C0 and app(A) in ⊢_{λ-lattice-η} -/

section Stratification

variable (model : DdLP96Model)

/-- Lemma C0 at an abstraction in ⊢_{λ-lattice-η}: λx. B, B stratified and truncating a term X, is a
stratified approximant of a term equal to λx. X, by T7 and T8 pushing the λ down to the head nodes,
with the reading of λx. B. -/
theorem stratifiedAbstractionLatticeEta {approximant : Term} (stratified : Stratified approximant) :
    ∀ {term : Term}, Truncates approximant term →
      ∃ newApproximant newTerm, Stratified newApproximant ∧ Truncates newApproximant newTerm ∧
        DerivableLatticeEta (fun _ _ => False) (.abstraction term) newTerm ∧
        FreeIncluded newTerm (.abstraction term) ∧
        ∀ environment, model.interpret newApproximant environment =
          model.interpret (.abstraction approximant) environment := by
  induction stratified with
  | truncated =>
      intro term _
      refine ⟨Omega, .abstraction term, .truncated, .truncated _, .reflexive _,
        fun _ occurs => occurs, fun environment => ?_⟩
      exact model.equalOfApply fun value => by
        rw [model.interpretAbstraction, model.interpretOmega, model.interpretOmega,
          model.applyBottom]
  | choice _ _ leftInner rightInner =>
      intro term truncates
      cases truncates with
      | choice leftTruncates rightTruncates =>
          obtain ⟨leftApproximant, leftTerm, leftStratified, leftTruncated, leftDerivation,
            leftIncluded, leftValue⟩ := leftInner leftTruncates
          obtain ⟨rightApproximant, rightTerm, rightStratified, rightTruncated, rightDerivation,
            rightIncluded, rightValue⟩ := rightInner rightTruncates
          refine ⟨.choice leftApproximant rightApproximant, .choice leftTerm rightTerm,
            .choice leftStratified rightStratified, .choice leftTruncated rightTruncated,
            .transitive (DerivableLatticeEta.abstractionChoice _ _)
              (DerivableLatticeEta.congruenceChoice leftDerivation rightDerivation), ?_, ?_⟩
          · intro index occurs
            rcases occurs with found | found
            · exact .inl (leftIncluded index found)
            · exact .inr (rightIncluded index found)
          · intro environment
            rw [model.interpretChoice, leftValue, rightValue]
            exact model.equalOfApply fun value => by
              rw [model.applyMeet, model.interpretAbstraction, model.interpretAbstraction,
                model.interpretAbstraction, model.interpretChoice]
  | parallel _ _ leftInner rightInner =>
      intro term truncates
      cases truncates with
      | parallel leftTruncates rightTruncates =>
          obtain ⟨leftApproximant, leftTerm, leftStratified, leftTruncated, leftDerivation,
            leftIncluded, leftValue⟩ := leftInner leftTruncates
          obtain ⟨rightApproximant, rightTerm, rightStratified, rightTruncated, rightDerivation,
            rightIncluded, rightValue⟩ := rightInner rightTruncates
          refine ⟨.parallel leftApproximant rightApproximant, .parallel leftTerm rightTerm,
            .parallel leftStratified rightStratified, .parallel leftTruncated rightTruncated,
            .transitive (DerivableLatticeEta.abstractionParallel _ _)
              (.transitive (DerivableLatticeEta.congruenceParallelLeft _ leftDerivation)
                (DerivableLatticeEta.congruenceParallelRight _ rightDerivation)), ?_, ?_⟩
          · intro index occurs
            rcases occurs with found | found
            · exact .inl (leftIncluded index found)
            · exact .inr (rightIncluded index found)
          · intro environment
            rw [model.interpretParallel, leftValue, rightValue]
            exact model.equalOfApply fun value => by
              rw [model.applyJoin, model.interpretAbstraction, model.interpretAbstraction,
                model.interpretAbstraction, model.interpretParallel]
  | headNode abstractions head arguments argumentsStratified _ =>
      intro term truncates
      exact ⟨headNode (abstractions + 1) head arguments, .abstraction term,
        .headNode _ _ _ argumentsStratified, .abstraction truncates, .reflexive _,
        fun _ occurs => occurs, fun _ => rfl⟩

end Stratification

section Application

variable (model : DdLP96Model)

/-- The proofs file's app(A) of (L) in ⊢_{λ-lattice-η}: an approximant of M applied to N gives a
stratified approximant of a term equal to M N, which reads as the approximant applied to ⊥. -/
theorem stratifiedApplicationLatticeEta {approximant : Term} (stratified : Stratified approximant) :
    ∀ {term : Term}, Truncates approximant term → ∀ argument : Term,
      ∃ newApproximant newTerm, Stratified newApproximant ∧ Truncates newApproximant newTerm ∧
        DerivableLatticeEta (fun _ _ => False) (.application term argument) newTerm ∧
        FreeIncluded newTerm (.application term argument) ∧
        ∀ environment, model.interpret newApproximant environment =
          model.apply (model.interpret approximant environment) model.bottom := by
  induction stratified with
  | truncated =>
      intro term _ argument
      exact ⟨Omega, .application term argument, .truncated, .truncated _, .reflexive _,
        fun _ occurs => occurs, fun environment => by
          rw [model.interpretOmega, model.applyBottom]⟩
  | choice _ _ leftInner rightInner =>
      intro term truncates argument
      cases truncates with
      | choice leftTruncates rightTruncates =>
          obtain ⟨leftApproximant, leftTerm, leftStratified, leftTruncated, leftDerivation,
            leftIncluded, leftValue⟩ := leftInner leftTruncates argument
          obtain ⟨rightApproximant, rightTerm, rightStratified, rightTruncated, rightDerivation,
            rightIncluded, rightValue⟩ := rightInner rightTruncates argument
          refine ⟨.choice leftApproximant rightApproximant, .choice leftTerm rightTerm,
            .choice leftStratified rightStratified, .choice leftTruncated rightTruncated,
            .transitive (.choiceFunctionDistributive _ _ _)
              (DerivableLatticeEta.congruenceChoice leftDerivation rightDerivation), ?_, ?_⟩
          · intro index occurs
            rcases occurs with found | found
            · rcases leftIncluded index found with inner | inner
              · exact .inl (.inl inner)
              · exact .inr inner
            · rcases rightIncluded index found with inner | inner
              · exact .inl (.inr inner)
              · exact .inr inner
          · intro environment
            rw [model.interpretChoice, model.interpretChoice, leftValue, rightValue,
              model.applyMeet]
  | parallel _ _ leftInner rightInner =>
      intro term truncates argument
      cases truncates with
      | parallel leftTruncates rightTruncates =>
          obtain ⟨leftApproximant, leftTerm, leftStratified, leftTruncated, leftDerivation,
            leftIncluded, leftValue⟩ := leftInner leftTruncates argument
          obtain ⟨rightApproximant, rightTerm, rightStratified, rightTruncated, rightDerivation,
            rightIncluded, rightValue⟩ := rightInner rightTruncates argument
          refine ⟨.parallel leftApproximant rightApproximant, .parallel leftTerm rightTerm,
            .parallel leftStratified rightStratified, .parallel leftTruncated rightTruncated,
            .transitive (.parallelFunctionDistributive _ _ _)
              (.transitive (DerivableLatticeEta.congruenceParallelLeft _ leftDerivation)
                (DerivableLatticeEta.congruenceParallelRight _ rightDerivation)), ?_, ?_⟩
          · intro index occurs
            rcases occurs with found | found
            · rcases leftIncluded index found with inner | inner
              · exact .inl (.inl inner)
              · exact .inr inner
            · rcases rightIncluded index found with inner | inner
              · exact .inl (.inr inner)
              · exact .inr inner
          · intro environment
            rw [model.interpretParallel, model.interpretParallel, leftValue, rightValue,
              model.applyJoin]
  | headNode abstractions head arguments argumentsStratified _ =>
      intro term truncates argument
      obtain ⟨truncatedArguments, rfl, argumentsTruncate⟩ := truncatesHeadNode truncates
      cases abstractions with
      | zero =>
          refine ⟨headNode 0 head (arguments ++ [Omega]),
            .application (headNode 0 head truncatedArguments) argument, ?_, ?_, .reflexive _,
            fun _ occurs => occurs, ?_⟩
          · refine .headNode 0 head _ fun member inList => ?_
            rcases List.mem_append.mp inList with inArguments | isOmega
            · exact argumentsStratified member inArguments
            · rw [List.mem_singleton.mp isOmega]
              exact .truncated
          · show Truncates (applyAll (.boundVariable head) (arguments ++ [Omega]))
              (.application (applyAll (.boundVariable head) truncatedArguments) argument)
            rw [applyAllAppend]
            exact .application (truncatesApplyAllOf (.boundVariable head) argumentsTruncate)
              (.truncated _)
          · intro environment
            show model.interpret (applyAll (.boundVariable head) (arguments ++ [Omega])) _ = _
            rw [applyAllAppend, model.interpretApplication, model.interpretOmega]
            rfl
      | succ abstractions =>
          have bodyStratified : Stratified (headNode abstractions head arguments) :=
            .headNode _ _ _ argumentsStratified
          have bodyTruncates : Truncates (headNode abstractions head arguments)
              (headNode abstractions head truncatedArguments) :=
            truncatesAbstractAllOf (truncatesApplyAllOf (.boundVariable head) argumentsTruncate) _
          obtain ⟨newApproximant, newStratified, newTruncates, newValue⟩ :=
            stratifiedSubstituteOmega model bodyStratified bodyTruncates 0 argument
          refine ⟨newApproximant, instantiate (headNode abstractions head truncatedArguments) argument,
            newStratified, newTruncates, .beta _ _, ?_, ?_⟩
          · intro index occurs
            rcases occursFreeSubstitute _ 0 argument index occurs with
              ⟨impossible, _⟩ | ⟨_, found⟩ | found
            · omega
            · exact .inl found
            · exact .inr found
          · intro environment
            rw [newValue]
            show _ = model.apply (model.interpret
              (.abstraction (headNode abstractions head arguments)) environment) model.bottom
            rw [model.interpretAbstraction, ← model.interpretOmega environment]
            exact model.interpretInstantiate _ _ _

/-- The step from B ∈ 𝒜(M x) to λx. B ∈ 𝒜(M) in ⊢_{λ-lattice-η}: η gives
M = λx. M x, the congruence under λ carries M x = T, and lemma C0 pushes the λ down. -/
theorem freshAbstractionLatticeEta {function approximant term : Term} {index : Nat}
    (functionFree : FreeBelow index function) (stratified : Stratified approximant)
    (truncates : Truncates approximant term)
    (derivation : DerivableLatticeEta (fun _ _ => False)
      (.application function (.boundVariable index)) term)
    (included : FreeIncluded term (.application function (.boundVariable index))) :
    ∃ newApproximant newTerm, Stratified newApproximant ∧ Truncates newApproximant newTerm ∧
      DerivableLatticeEta (fun _ _ => False) function newTerm ∧
      FreeIncluded newTerm function ∧
      ∀ environment, model.apply (model.interpret newApproximant environment) (environment index) =
        model.interpret approximant environment := by
  have boundStratified : Stratified (bindVariable index approximant) :=
    (stratified.shiftFrom 0).substituteVariable _ _
  obtain ⟨newApproximant, newTerm, newStratified, newTruncates, newDerivation, newIncluded,
    newValue⟩ :=
    stratifiedAbstractionLatticeEta model boundStratified (truncates.bindVariable index)
  refine ⟨newApproximant, newTerm, newStratified, newTruncates, ?_,
    newIncluded.transitive (freeIncludedBindVariable functionFree included), ?_⟩
  · have expanded : DerivableLatticeEta (fun _ _ => False) function
        (.abstraction (bindVariable index (.application function (.boundVariable index)))) := by
      rw [bindVariableApplication functionFree]
      exact .symmetric (.eta function)
    exact .transitive expanded (.transitive (.congruenceAbstraction
      (LatticeEta.derivableLatticeEtaSubstitute
        (LatticeEta.derivableLatticeEtaShiftFrom derivation 0) (index + 1) (.boundVariable 0)))
      newDerivation)
  · intro environment
    have approximantFree : FreeBelow (index + 1) approximant := by
      intro other occurs
      rcases included other (truncates.freeIncluded other occurs) with inFunction | isIndex
      · have := functionFree other inFunction
        omega
      · simp only [OccursFree] at isIndex
        omega
    rw [newValue, model.interpretAbstraction]
    exact model.interpretBindVariable approximantFree environment

end Application

/-! ## Approximants and computability in ⊢_{λ-lattice-η} (the proofs file, 20.2) -/

/-- A ∈ 𝒜(M) in ⊢_{λ-lattice-η}: A is a stratified truncation of some T′ with
∅ ⊢_{λ-lattice-η} M = T′ and FV(T′) ⊆ FV(M). -/
def ApproximantLatticeEta (term approximant : Term) : Prop :=
  ∃ reduct, DerivableLatticeEta (fun _ _ => False) term reduct ∧
    FreeIncluded reduct term ∧ Truncates approximant reduct ∧ Stratified approximant

/-- Approximants of a list of terms, position by position. -/
def ApproximantAllLatticeEta : List Term → List Term → Prop
  | [], [] => True
  | first :: rest, approximantFirst :: approximantRest =>
      ApproximantLatticeEta first approximantFirst ∧ ApproximantAllLatticeEta rest approximantRest
  | _, _ => False

theorem ApproximantAllLatticeEta.append : ∀ {first approximantsFirst : List Term},
    ApproximantAllLatticeEta first approximantsFirst → ∀ {last approximantLast : Term},
      ApproximantLatticeEta last approximantLast →
        ApproximantAllLatticeEta (first ++ [last]) (approximantsFirst ++ [approximantLast])
  | [], [], _, _, _, lastApproximant => ⟨lastApproximant, trivial⟩
  | _ :: _, _ :: _, firstApproximants, _, _, lastApproximant =>
      ⟨firstApproximants.1, ApproximantAllLatticeEta.append firstApproximants.2 lastApproximant⟩
  | [], _ :: _, firstApproximants, _, _, _ => firstApproximants.elim
  | _ :: _, [], firstApproximants, _, _, _ => firstApproximants.elim

/-- The approximants of the arguments give an approximant of x M⃗, the head node x A⃗. -/
theorem approximantSpineLatticeEta (head : Nat) : ∀ {arguments approximants : List Term},
    ApproximantAllLatticeEta arguments approximants →
      ApproximantLatticeEta (applyAll (.boundVariable head) arguments)
        (applyAll (.boundVariable head) approximants) := by
  suffices general : ∀ (arguments approximants : List Term) (spine reductSpine approximantSpine : Term),
      DerivableLatticeEta (fun _ _ => False) spine reductSpine →
      FreeIncluded reductSpine spine →
      Truncates approximantSpine reductSpine → ApproximantAllLatticeEta arguments approximants →
      ∃ reduct, DerivableLatticeEta (fun _ _ => False) (applyAll spine arguments) reduct ∧
        FreeIncluded reduct (applyAll spine arguments) ∧
        Truncates (applyAll approximantSpine approximants) reduct by
    intro arguments approximants approximantsHold
    obtain ⟨reduct, derivation, included, truncates⟩ := general arguments approximants
      (.boundVariable head) (.boundVariable head) (.boundVariable head) (.reflexive _)
      (fun _ occurs => occurs) (.boundVariable head) approximantsHold
    refine ⟨reduct, derivation, included, truncates,
      .headNode 0 head approximants ?_⟩
    clear derivation included truncates
    induction arguments generalizing approximants with
    | nil =>
        cases approximants with
        | nil => exact fun _ member => absurd member List.not_mem_nil
        | cons _ _ => exact approximantsHold.elim
    | cons first rest inner =>
        cases approximants with
        | nil => exact approximantsHold.elim
        | cons approximantFirst approximantRest =>
            intro approximant member
            rcases List.mem_cons.mp member with equal | inRest
            · subst equal
              obtain ⟨_, _, _, _, stratified⟩ := approximantsHold.1
              exact stratified
            · exact inner approximantsHold.2 approximant inRest
  intro arguments
  induction arguments with
  | nil =>
      intro approximants spine reductSpine approximantSpine derivation included truncates holds
      cases approximants with
      | nil => exact ⟨reductSpine, derivation, included, truncates⟩
      | cons _ _ => exact holds.elim
  | cons first rest inner =>
      intro approximants spine reductSpine approximantSpine derivation included truncates holds
      cases approximants with
      | nil => exact holds.elim
      | cons approximantFirst approximantRest =>
          obtain ⟨firstReduct, firstDerivation, firstIncluded, firstTruncates, _⟩ := holds.1
          exact inner approximantRest (.application spine first)
            (.application reductSpine firstReduct) (.application approximantSpine approximantFirst)
            (.transitive (.congruenceFunction first derivation)
              (.congruenceArgument _ firstDerivation))
            (fun index occurs => occurs.elim (fun found => .inl (included index found))
              (fun found => .inr (firstIncluded index found)))
            (.application truncates firstTruncates) holds.2

namespace DdLP96Model

variable (model : DdLP96Model)

/-- Approx(d) in ⊢_{λ-lattice-η}: some approximant of M reads above d in ρ₀. -/
def ApproximableLatticeEta (value : model.Value) (term : Term) : Prop :=
  ∃ approximant, ApproximantLatticeEta term approximant ∧
    model.below value (model.interpret approximant model.richEnvironment)

/-- 𝒞ₙ(d) in ⊢_{λ-lattice-η}: 𝒞₀(d) = Approx(d), and 𝒞_{n+1}(d) the terms M with M N ∈ 𝒞ₙ(d(a))
for every a ∈ 𝔻ₙ and every N ∈ 𝒞ₙ(a). -/
def ApproximatingLatticeEta (model : DdLP96Model) : Nat → model.Value → Term → Prop
  | 0, value, term => model.ApproximableLatticeEta value term
  | level + 1, value, term =>
      ∀ argumentValue argument, model.Compact level argumentValue →
        ApproximatingLatticeEta model level argumentValue argument →
          ApproximatingLatticeEta model level (model.apply value argumentValue)
            (.application term argument)

/-- Approx(⊥) is every term: ⋄ is an approximant of it. -/
theorem approximableLatticeEtaBottom (term : Term) :
    model.ApproximableLatticeEta model.bottom term :=
  ⟨Omega, ⟨term, .reflexive _, fun _ occurs => occurs, .truncated _, .truncated⟩,
    model.bottomLeast _⟩

/-- The proofs file's (D). -/
theorem approximatingLatticeEtaDown : ∀ (level : Nat) {lower upper : model.Value} {term : Term},
    model.Compact level lower → model.Compact level upper → model.below lower upper →
      model.ApproximatingLatticeEta level upper term → model.ApproximatingLatticeEta level lower term
  | 0, _, _, _, _, _, below, ⟨approximant, holds, approximantAbove⟩ =>
      ⟨approximant, holds, model.orderTransitive below approximantAbove⟩
  | level + 1, _, _, _, lowerCompact, upperCompact, below, approximating => by
      intro argumentValue argument argumentCompact argumentApproximating
      exact approximatingLatticeEtaDown level (model.compactApply lowerCompact argumentValue)
        (model.compactApply upperCompact argumentValue)
        (model.applyMonotoneFunction below argumentValue)
        (approximating argumentValue argument argumentCompact argumentApproximating)

/-- The proofs file's (Eq): ∅ ⊢_{λ-lattice-η} M = M′ and FV(M′) ⊆ FV(M) carry 𝒞ₙ(d) from M′ to M. -/
theorem approximatingLatticeEtaOfDerivable : ∀ (level : Nat) {value : model.Value}
    {term other : Term},
    DerivableLatticeEta (fun _ _ => False) term other → FreeIncluded other term →
      model.ApproximatingLatticeEta level value other → model.ApproximatingLatticeEta level value term
  | 0, _, _, _, derivation, included, ⟨approximant, ⟨reduct, reductDerivation,
      reductIncluded, truncates, stratified⟩, above⟩ =>
      ⟨approximant, ⟨reduct, .transitive derivation reductDerivation,
        reductIncluded.transitive included, truncates, stratified⟩, above⟩
  | level + 1, _, _, _, derivation, included, approximating => by
      intro argumentValue argument argumentCompact argumentApproximating
      exact approximatingLatticeEtaOfDerivable level (.congruenceFunction argument derivation)
        (fun index occurs => occurs.elim (fun found => .inl (included index found)) .inr)
        (approximating argumentValue argument argumentCompact argumentApproximating)

/-- The proofs file's (+). -/
theorem approximatingLatticeEtaChoice : ∀ (level : Nat) {value : model.Value} {left right : Term},
    model.ApproximatingLatticeEta level value left → model.ApproximatingLatticeEta level value right →
      model.ApproximatingLatticeEta level value (.choice left right)
  | 0, _, _, _, ⟨leftApproximant, ⟨leftReduct, leftDerivation, leftIncluded,
      leftTruncates, leftStratified⟩, leftAbove⟩, ⟨rightApproximant, ⟨rightReduct,
      rightDerivation, rightIncluded, rightTruncates, rightStratified⟩, rightAbove⟩ =>
      ⟨.choice leftApproximant rightApproximant,
        ⟨.choice leftReduct rightReduct,
          DerivableLatticeEta.congruenceChoice leftDerivation rightDerivation,
          fun index occurs => occurs.elim (fun found => .inl (leftIncluded index found))
            (fun found => .inr (rightIncluded index found)),
          .choice leftTruncates rightTruncates, .choice leftStratified rightStratified⟩,
        by rw [model.interpretChoice]; exact model.meetGreatest leftAbove rightAbove⟩
  | level + 1, _, left, right, leftApproximating, rightApproximating => by
      intro argumentValue argument argumentCompact argumentApproximating
      exact model.approximatingLatticeEtaOfDerivable level
        (.choiceFunctionDistributive left right argument)
        (fun index occurs => occurs.elim (fun found => found.elim (fun inner => .inl (.inl inner)) .inr)
          (fun found => found.elim (fun inner => .inl (.inr inner)) .inr))
        (approximatingLatticeEtaChoice level
          (leftApproximating argumentValue argument argumentCompact argumentApproximating)
          (rightApproximating argumentValue argument argumentCompact argumentApproximating))

/-- The proofs file's (∥). -/
theorem approximatingLatticeEtaParallel : ∀ (level : Nat) {leftValue rightValue : model.Value}
    {left right : Term}, model.Compact level leftValue → model.Compact level rightValue →
      model.ApproximatingLatticeEta level leftValue left →
      model.ApproximatingLatticeEta level rightValue right →
        model.ApproximatingLatticeEta level (model.join leftValue rightValue) (.parallel left right)
  | 0, _, _, _, _, _, _, ⟨leftApproximant, ⟨leftReduct, leftDerivation, leftIncluded,
      leftTruncates, leftStratified⟩, leftAbove⟩, ⟨rightApproximant, ⟨rightReduct,
      rightDerivation, rightIncluded, rightTruncates, rightStratified⟩, rightAbove⟩ =>
      ⟨.parallel leftApproximant rightApproximant,
        ⟨.parallel leftReduct rightReduct,
          .transitive (DerivableLatticeEta.congruenceParallelLeft _ leftDerivation)
            (DerivableLatticeEta.congruenceParallelRight _ rightDerivation),
          fun index occurs => occurs.elim (fun found => .inl (leftIncluded index found))
            (fun found => .inr (rightIncluded index found)),
          .parallel leftTruncates rightTruncates, .parallel leftStratified rightStratified⟩,
        by rw [model.interpretParallel]; exact model.joinMonotone leftAbove rightAbove⟩
  | level + 1, _, _, left, right, leftCompact, rightCompact, leftApproximating,
      rightApproximating => by
      intro argumentValue argument argumentCompact argumentApproximating
      rw [model.applyJoin]
      exact model.approximatingLatticeEtaOfDerivable level
        (.parallelFunctionDistributive left right argument)
        (fun index occurs => occurs.elim (fun found => found.elim (fun inner => .inl (.inl inner)) .inr)
          (fun found => found.elim (fun inner => .inl (.inr inner)) .inr))
        (approximatingLatticeEtaParallel level (model.compactApply leftCompact argumentValue)
          (model.compactApply rightCompact argumentValue)
          (leftApproximating argumentValue argument argumentCompact argumentApproximating)
          (rightApproximating argumentValue argument argumentCompact argumentApproximating))

/-- The proofs file's (V) and (CA) in ⊢_{λ-lattice-η}, by simultaneous induction on the level: a
spine x M⃗ whose arguments have approximants A⃗ with d ⊑ [[x A⃗]]ρ₀ is in 𝒞ₙ(d); and
𝒞ₙ(d) ⊆ Approx(d). -/
theorem variableAndApproximableLatticeEta : ∀ level : Nat,
    (∀ (value : model.Value) (head : Nat) (arguments approximants : List Term),
      model.Compact level value → ApproximantAllLatticeEta arguments approximants →
      model.below value (model.interpret (applyAll (.boundVariable head) approximants)
        model.richEnvironment) →
      model.ApproximatingLatticeEta level value (applyAll (.boundVariable head) arguments)) ∧
    (∀ (value : model.Value) (term : Term), model.Compact level value →
      model.ApproximatingLatticeEta level value term → model.ApproximableLatticeEta value term)
  | 0 => ⟨fun _ head _ _ _ holds above => ⟨_, approximantSpineLatticeEta head holds, above⟩,
      fun _ _ _ approximating => approximating⟩
  | level + 1 => by
      obtain ⟨variableLower, approximableLower⟩ := variableAndApproximableLatticeEta level
      refine ⟨?_, ?_⟩
      · intro value head arguments approximants compact holds above argumentValue argument
          argumentCompact argumentApproximating
        obtain ⟨argumentApproximant, argumentHolds, argumentAbove⟩ :=
          approximableLower argumentValue argument argumentCompact argumentApproximating
        have extended := variableLower (model.apply value argumentValue) head
          (arguments ++ [argument]) (approximants ++ [argumentApproximant])
          (model.compactApply compact argumentValue) (holds.append argumentHolds) (by
            rw [applyAllAppend, model.interpretApplication]
            exact model.orderTransitive (model.applyMonotoneFunction above argumentValue)
              (model.applyMonotoneArgument _ argumentAbove))
        rw [applyAllAppend] at extended
        exact extended
      · intro value term compact approximating
        -- one fresh variable for each a ∈ 𝔻ₙ, and the parallel of the abstractions
        have collected : ∀ values : List model.Value, (∀ member ∈ values, model.Compact level member) →
            ∃ approximant reduct, Stratified approximant ∧ Truncates approximant reduct ∧
              DerivableLatticeEta (fun _ _ => False) term reduct ∧
              FreeIncluded reduct term ∧
              ∀ member ∈ values, model.below (model.apply value member)
                (model.apply (model.interpret approximant model.richEnvironment) member) := by
          intro values
          induction values with
          | nil =>
              intro _
              exact ⟨Omega, term, .truncated, .truncated _, .reflexive _,
                fun _ occurs => occurs, fun _ member => absurd member List.not_mem_nil⟩
          | cons first rest inner =>
              intro allCompact
              have firstCompact := allCompact first List.mem_cons_self
              obtain ⟨restApproximant, restReduct, restStratified, restTruncates, restDerivation,
                restIncluded, restAbove⟩ :=
                inner (fun member inRest => allCompact member (List.mem_cons_of_mem _ inRest))
              obtain ⟨index, termFreeBelow, indexValue⟩ := model.freshIndex firstCompact term
              have variableApproximating :
                  model.ApproximatingLatticeEta level first (.boundVariable index) :=
                variableLower first index [] [] firstCompact trivial (by
                  show model.below first (model.interpret (.boundVariable index) _)
                  rw [model.interpretVariable, indexValue]
                  exact model.orderReflexive _)
              obtain ⟨bodyApproximant, ⟨bodyReduct, bodyDerivation, bodyIncluded,
                bodyTruncates, bodyStratified⟩, bodyAbove⟩ :=
                approximableLower _ (.application term (.boundVariable index))
                  (model.compactApply compact first)
                  (approximating first (.boundVariable index) firstCompact variableApproximating)
              obtain ⟨firstApproximant, firstReduct, firstStratified, firstTruncates,
                firstDerivation, firstIncluded, firstValue⟩ :=
                freshAbstractionLatticeEta model termFreeBelow bodyStratified bodyTruncates
                  bodyDerivation bodyIncluded
              refine ⟨.parallel firstApproximant restApproximant, .parallel firstReduct restReduct,
                .parallel firstStratified restStratified, .parallel firstTruncates restTruncates,
                .transitive (.symmetric (DerivableLatticeEta.parallelIdempotent term))
                  (.transitive (DerivableLatticeEta.congruenceParallelLeft _ firstDerivation)
                    (DerivableLatticeEta.congruenceParallelRight _ restDerivation)),
                fun index occurs => occurs.elim (firstIncluded index) (restIncluded index), ?_⟩
              intro member inValues
              rw [model.interpretParallel, model.applyJoin]
              rcases List.mem_cons.mp inValues with equal | inRest
              · subst equal
                have firstApplied := firstValue model.richEnvironment
                rw [indexValue] at firstApplied
                rw [← firstApplied] at bodyAbove
                exact model.orderTransitive bodyAbove (model.joinAboveLeft _ _)
              · exact model.orderTransitive (restAbove member inRest) (model.joinAboveRight _ _)
        obtain ⟨approximant, reduct, stratified, truncates, derivation, included, above⟩ :=
          collected (model.compactList level)
            (fun member inList => (model.memCompactList level member).mp inList)
        refine ⟨approximant, ⟨reduct, derivation, included, truncates, stratified⟩, ?_⟩
        apply model.extensional.mpr
        intro argument
        rw [model.compactApplyArgument compact argument]
        exact model.orderTransitive
          (above _ ((model.memCompactList level _).mpr (model.compactProject level argument)))
          (model.applyMonotoneArgument _ (model.projectBelow level argument))

/-- The proofs file's (L) in ⊢_{λ-lattice-η}: d ∈ 𝔻ₙ gives 𝒞ₙ(d) = 𝒞_{n+1}(d). At level 0 it uses
app(A) for ⊆ and a fresh variable, (E4), for ⊇. -/
theorem approximatingLatticeEtaSucc : ∀ (level : Nat) {value : model.Value} {term : Term},
    model.Compact level value →
      (model.ApproximatingLatticeEta level value term ↔
        model.ApproximatingLatticeEta (level + 1) value term)
  | 0, value, term, compact => by
      rcases model.compactZero compact with isBottom | isTop
      · subst isBottom
        constructor
        · intro _ argumentValue argument _ _
          show model.ApproximableLatticeEta (model.apply model.bottom argumentValue) _
          rw [model.applyBottom]
          exact model.approximableLatticeEtaBottom _
        · intro _
          exact model.approximableLatticeEtaBottom term
      · subst isTop
        constructor
        · intro approximable argumentValue argument _ _
          show model.ApproximableLatticeEta (model.apply model.top argumentValue) _
          rw [model.applyTop]
          obtain ⟨approximant, ⟨reduct, derivation, included, truncates, stratified⟩,
            above⟩ := approximable
          obtain ⟨newApproximant, newReduct, newStratified, newTruncates, newDerivation,
            newIncluded, newValue⟩ :=
            stratifiedApplicationLatticeEta model stratified truncates argument
          refine ⟨newApproximant, ⟨newReduct, .transitive (.congruenceFunction argument derivation)
            newDerivation, ?_, newTruncates, newStratified⟩, ?_⟩
          · exact newIncluded.transitive
              (fun index occurs => occurs.elim (fun found => .inl (included index found)) .inr)
          · rw [newValue, model.topOfTopBelow above, model.applyTop]
            exact model.orderReflexive _
        · intro approximating
          show model.ApproximableLatticeEta model.top term
          obtain ⟨index, termFreeBelow, indexValue⟩ :=
            model.freshIndex model.compactBottomZero term
          have applied := approximating model.bottom (.boundVariable index) model.compactBottomZero
            (model.approximableLatticeEtaBottom _)
          obtain ⟨bodyApproximant, ⟨bodyReduct, bodyDerivation, bodyIncluded,
            bodyTruncates, bodyStratified⟩, bodyAbove⟩ := applied
          rw [model.applyTop] at bodyAbove
          obtain ⟨newApproximant, newReduct, newStratified, newTruncates, newDerivation,
            newIncluded, newValue⟩ :=
            freshAbstractionLatticeEta model termFreeBelow bodyStratified bodyTruncates
              bodyDerivation bodyIncluded
          refine ⟨newApproximant, ⟨newReduct, newDerivation, newIncluded, newTruncates,
            newStratified⟩, ?_⟩
          have appliedTop := newValue model.richEnvironment
          rw [indexValue, model.topOfTopBelow bodyAbove] at appliedTop
          rw [model.topOfApplyBottom _ appliedTop]
          exact model.orderReflexive _
  | level + 1, value, term, compact => by
      constructor
      · intro approximating argumentValue argument argumentCompact argumentApproximating
        have lowered : model.Compact level (model.project level argumentValue) :=
          model.compactProject level argumentValue
        have argumentDown := model.approximatingLatticeEtaDown (level + 1)
          (model.compactRaise lowered) argumentCompact (model.projectBelow level argumentValue)
          argumentApproximating
        have argumentLevel := (approximatingLatticeEtaSucc level lowered).mpr argumentDown
        have applied := approximating _ argument lowered argumentLevel
        rw [model.compactApplyArgument compact argumentValue]
        exact (approximatingLatticeEtaSucc level (model.compactApply compact _)).mp applied
      · intro approximating argumentValue argument argumentCompact argumentApproximating
        have applied := approximating argumentValue argument (model.compactRaise argumentCompact)
          ((approximatingLatticeEtaSucc level argumentCompact).mp argumentApproximating)
        exact (approximatingLatticeEtaSucc level (model.compactApply compact argumentValue)).mpr
          applied

/-- (L) iterated. -/
theorem approximatingLatticeEtaRaiseBy {level : Nat} {value : model.Value} {term : Term}
    (compact : model.Compact level value) :
    ∀ extra, model.ApproximatingLatticeEta level value term ↔
      model.ApproximatingLatticeEta (level + extra) value term
  | 0 => Iff.rfl
  | extra + 1 => (approximatingLatticeEtaRaiseBy compact extra).trans
      (model.approximatingLatticeEtaSucc (level + extra) (model.compactRaiseBy compact extra))

/-- 𝒞(d) does not depend on the level d is taken at. -/
theorem approximatingLatticeEtaAtLevel {level other : Nat} {value : model.Value} {term : Term}
    (compact : model.Compact level value) (otherCompact : model.Compact other value)
    (approximating : model.ApproximatingLatticeEta other value term) :
    model.ApproximatingLatticeEta level value term := by
  have raised := (model.approximatingLatticeEtaRaiseBy otherCompact level).mp approximating
  rw [Nat.add_comm] at raised
  exact (model.approximatingLatticeEtaRaiseBy compact other).mpr raised

/-- (D) across levels. -/
theorem approximatingLatticeEtaBelow {level other : Nat} {lower upper : model.Value} {term : Term}
    (lowerCompact : model.Compact level lower) (upperCompact : model.Compact other upper)
    (below : model.below lower upper)
    (approximating : model.ApproximatingLatticeEta other upper term) :
    model.ApproximatingLatticeEta level lower term := by
  have upperRaised := (model.approximatingLatticeEtaRaiseBy upperCompact level).mp
    approximating
  rw [Nat.add_comm] at upperRaised
  have upperTotal := model.compactRaiseBy upperCompact level
  rw [Nat.add_comm] at upperTotal
  have lowered := model.approximatingLatticeEtaDown (level + other)
    (model.compactRaiseBy lowerCompact other) upperTotal below upperRaised
  exact (model.approximatingLatticeEtaRaiseBy lowerCompact other).mpr lowered

end DdLP96Model

/-! ## The substitution of the basic lemma as a β redex, in ⊢_{λ-lattice-η} -/

/-- One β step at the head of a redex. -/
theorem redexStepLatticeEta {hypotheses : Term → Term → Prop} (first : Term) (rest : List Term)
    (term : Term) :
    DerivableLatticeEta hypotheses (redex (first :: rest) term)
      (redex rest (substitute rest.length (shiftTimes rest.length first) term)) := by
  show DerivableLatticeEta hypotheses
    (applyAll (.application (.abstraction (abstractAll rest.length term)) first) rest)
    (applyAll (abstractAll rest.length (substitute rest.length (shiftTimes rest.length first) term))
      rest)
  have contracted : instantiate (abstractAll rest.length term) first =
      abstractAll rest.length (substitute rest.length (shiftTimes rest.length first) term) := by
    unfold instantiate
    rw [substituteAbstractAll, Nat.zero_add]
  rw [← contracted]
  exact LatticeEta.congruenceApplyAll rest (.beta _ _)

theorem redexApplicationLatticeEta {hypotheses : Term → Term → Prop} : ∀ (arguments : List Term)
    (function argument : Term),
    DerivableLatticeEta hypotheses (redex arguments (.application function argument))
      (.application (redex arguments function) (redex arguments argument))
  | [], _, _ => .reflexive _
  | first :: rest, function, argument =>
      .transitive (redexStepLatticeEta first rest _)
        (.transitive (redexApplicationLatticeEta rest _ _)
          (.transitive (.congruenceFunction _ (.symmetric (redexStepLatticeEta first rest function)))
            (.congruenceArgument _ (.symmetric (redexStepLatticeEta first rest argument)))))

theorem redexChoiceLatticeEta {hypotheses : Term → Term → Prop} : ∀ (arguments : List Term)
    (left right : Term),
    DerivableLatticeEta hypotheses (redex arguments (.choice left right))
      (.choice (redex arguments left) (redex arguments right))
  | [], _, _ => .reflexive _
  | first :: rest, left, right =>
      .transitive (redexStepLatticeEta first rest _)
        (.transitive (redexChoiceLatticeEta rest _ _)
          (DerivableLatticeEta.congruenceChoice (.symmetric (redexStepLatticeEta first rest left))
            (.symmetric (redexStepLatticeEta first rest right))))

theorem redexParallelLatticeEta {hypotheses : Term → Term → Prop} : ∀ (arguments : List Term)
    (left right : Term),
    DerivableLatticeEta hypotheses (redex arguments (.parallel left right))
      (.parallel (redex arguments left) (redex arguments right))
  | [], _, _ => .reflexive _
  | first :: rest, left, right =>
      .transitive (redexStepLatticeEta first rest _)
        (.transitive (redexParallelLatticeEta rest _ _)
          (.transitive (DerivableLatticeEta.congruenceParallelLeft _
              (.symmetric (redexStepLatticeEta first rest left)))
            (DerivableLatticeEta.congruenceParallelRight _
              (.symmetric (redexStepLatticeEta first rest right)))))

theorem redexShiftedLatticeEta {hypotheses : Term → Term → Prop} :
    ∀ (arguments : List Term) (term : Term),
      DerivableLatticeEta hypotheses (redex arguments (shiftTimes arguments.length term)) term
  | [], _ => .reflexive _
  | first :: rest, term => by
      have step := redexStepLatticeEta (hypotheses := hypotheses) first rest
        (shiftTimes (first :: rest).length term)
      simp only [List.length_cons] at step
      rw [substituteShiftTimes] at step
      exact .transitive step (redexShiftedLatticeEta rest term)

/-- A redex over a variable is the argument the variable stands for. -/
theorem redexVariableLatticeEta {hypotheses : Term → Term → Prop} : ∀ (arguments : List Term)
    {index : Nat} {argument : Term}, arguments[arguments.length - 1 - index]? = some argument →
      index < arguments.length →
        DerivableLatticeEta hypotheses (redex arguments (.boundVariable index)) argument
  | [], _, _, _, below => absurd below (Nat.not_lt_zero _)
  | first :: rest, index, argument, found, below => by
      refine .transitive (redexStepLatticeEta first rest _) ?_
      simp only [List.length_cons] at found below
      by_cases atLast : index = rest.length
      · subst atLast
        simp only [substitute, Nat.lt_irrefl, ite_false, ite_true]
        rw [show rest.length + 1 - 1 - rest.length = 0 by omega] at found
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact redexShiftedLatticeEta rest first
      · have strictly : index < rest.length := by omega
        simp only [substitute, strictly, ite_true]
        rw [show rest.length + 1 - 1 - index = rest.length - 1 - index + 1 by omega,
          List.getElem?_cons_succ] at found
        exact redexVariableLatticeEta rest found strictly

namespace DdLP96Model

variable (model : DdLP96Model)

/-- The proofs file's lemma A4 in ⊢_{λ-lattice-η}, with the substitution written as a β redex: if
FV(M) is bound by the k abstractions, the argument for index i is in 𝒞(ρ(i)) with ρ(i) compact, and
d is compact with d ⊑ [[M]]ρ, then (λx⃗. M) N⃗ ∈ 𝒞(d). By induction on M. -/
theorem approximatingLatticeEtaBasic : ∀ (term : Term) {arguments : List Term}
    {environment : Nat → model.Value},
    FreeBelow arguments.length term →
    (∀ (position : Nat) argument, arguments[position]? = some argument →
      ∃ level, model.Compact level (environment (arguments.length - 1 - position)) ∧
        model.ApproximatingLatticeEta level (environment (arguments.length - 1 - position))
          argument) →
    ∀ {level : Nat} {value : model.Value}, model.Compact level value →
      model.below value (model.interpret term environment) →
      model.ApproximatingLatticeEta level value (redex arguments term)
  | .boundVariable index, arguments, environment, free, holds, level, value, compact, below => by
      have inRange : index < arguments.length := free index rfl
      obtain ⟨argument, found⟩ : ∃ argument, arguments[arguments.length - 1 - index]? = some argument :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨otherLevel, otherCompact, otherApproximating⟩ := holds _ argument found
      rw [show arguments.length - 1 - (arguments.length - 1 - index) = index by omega]
        at otherCompact otherApproximating
      rw [model.interpretVariable] at below
      exact model.approximatingLatticeEtaOfDerivable level (redexVariableLatticeEta arguments found inRange)
        (fun other occurs => occursFreeApplyAllArgument (List.mem_of_getElem? found) occurs)
        (model.approximatingLatticeEtaBelow compact otherCompact below otherApproximating)
  | .choice left right, arguments, environment, free, holds, level, value, compact, below => by
      rw [model.interpretChoice] at below
      have leftFree : FreeBelow arguments.length left := fun index occurs => free index (.inl occurs)
      have rightFree : FreeBelow arguments.length right := fun index occurs => free index (.inr occurs)
      exact model.approximatingLatticeEtaOfDerivable level (redexChoiceLatticeEta arguments left right)
        (fun index occurs => occurs.elim (redexFreeIncluded leftFree _ index)
          (redexFreeIncluded rightFree _ index))
        (model.approximatingLatticeEtaChoice level
          (approximatingLatticeEtaBasic left leftFree holds compact
            (model.orderTransitive below (model.meetBelowLeft _ _)))
          (approximatingLatticeEtaBasic right rightFree holds compact
            (model.orderTransitive below (model.meetBelowRight _ _))))
  | .parallel left right, arguments, environment, free, holds, level, value, compact, below => by
      rw [model.interpretParallel] at below
      have leftFree : FreeBelow arguments.length left := fun index occurs => free index (.inl occurs)
      have rightFree : FreeBelow arguments.length right := fun index occurs => free index (.inr occurs)
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
      have joined := model.approximatingLatticeEtaParallel (level + index) leftPartCompact
        rightPartCompact
        (approximatingLatticeEtaBasic left leftFree holds leftPartCompact
          (model.orderTransitive (model.meetBelowRight _ _) (model.projectBelow _ _)))
        (approximatingLatticeEtaBasic right rightFree holds rightPartCompact
          (model.orderTransitive (model.meetBelowRight _ _) (model.projectBelow _ _)))
      have valueBelow := model.orderTransitive
        (model.meetGreatest (model.orderReflexive value) chainBelow)
        (model.distributive value _ _)
      exact model.approximatingLatticeEtaBelow compact
        (model.compactJoin leftPartCompact rightPartCompact)
        valueBelow (model.approximatingLatticeEtaOfDerivable (level + index)
          (redexParallelLatticeEta arguments left right)
          (fun index occurs => occurs.elim (redexFreeIncluded leftFree _ index)
            (redexFreeIncluded rightFree _ index)) joined)
  | .application function argument, arguments, environment, free, holds, level, value, compact,
      below => by
      rw [model.interpretApplication] at below
      have functionFree : FreeBelow arguments.length function :=
        fun index occurs => free index (.inl occurs)
      have argumentFree : FreeBelow arguments.length argument :=
        fun index occurs => free index (.inr occurs)
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
      have functionApproximating := approximatingLatticeEtaBasic function functionFree
        holds (model.compactProject (index + 1) _) (model.projectBelow _ _)
      have argumentApproximating := approximatingLatticeEtaBasic argument argumentFree
        holds (model.compactProject index _) (model.projectBelow _ _)
      have applied := functionApproximating _ _ (model.compactProject index _)
        argumentApproximating
      exact model.approximatingLatticeEtaBelow compact
        (model.compactApply (model.compactProject (index + 1) _) _) chainBelow
        (model.approximatingLatticeEtaOfDerivable index
          (redexApplicationLatticeEta arguments function argument)
          (fun index occurs => occurs.elim (redexFreeIncluded functionFree _ index)
            (redexFreeIncluded argumentFree _ index)) applied)
  | .abstraction body, arguments, environment, free, holds, level, value, compact, below => by
      apply model.approximatingLatticeEtaAtLevel compact (model.compactRaise compact)
      intro argumentValue argument argumentCompact argumentApproximating
      have rewritten : Term.application (redex arguments (.abstraction body)) argument =
          redex (arguments ++ [argument]) body := by
        unfold redex
        rw [abstractAllAbstraction, applyAllAppend, List.length_append, List.length_singleton]
      rw [rewritten]
      apply approximatingLatticeEtaBasic body (environment := extendEnvironment argumentValue environment)
      · intro index occurs
        cases index with
        | zero => simp
        | succ index =>
            have := free index occurs
            simp only [List.length_append, List.length_singleton]
            omega
      · intro position extendedArgument found
        simp only [List.length_append, List.length_singleton]
        by_cases inside : position < arguments.length
        · rw [List.getElem?_append_left inside] at found
          obtain ⟨otherLevel, otherCompact, otherApproximating⟩ := holds position extendedArgument found
          refine ⟨otherLevel, ?_, ?_⟩
          · rw [show arguments.length + 1 - 1 - position = (arguments.length - 1 - position) + 1 by
              omega]
            exact otherCompact
          · rw [show arguments.length + 1 - 1 - position = (arguments.length - 1 - position) + 1 by
              omega]
            exact otherApproximating
        · rw [List.getElem?_append_right (by omega)] at found
          have atEnd : position - arguments.length = 0 := by
            rcases Nat.lt_or_ge (position - arguments.length) 1 with small | large
            · omega
            · rw [List.getElem?_eq_none (by simp; omega)] at found
              exact absurd found (by simp)
          rw [atEnd, List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          refine ⟨level, ?_, ?_⟩
          · rw [show arguments.length + 1 - 1 - position = 0 by omega]
            exact argumentCompact
          · rw [show arguments.length + 1 - 1 - position = 0 by omega]
            exact argumentApproximating
      · exact model.compactApply (model.compactRaise compact) argumentValue
      · rw [← model.interpretAbstraction]
        exact model.applyMonotoneFunction below argumentValue

/-- The proofs file's theorem A in ⊢_{λ-lattice-η} for a closed T, in the form its proof gives, with
lemma C0: for a compact d ⊑ [[T]], some closed T′ with ∅ ⊢_{λ-lattice-η} T = T′ has a stratified
truncation A with d ⊑ [[A]]. -/
def ApproximationLatticeEtaHypothesis : Prop :=
  ∀ term, Closed term → ∀ level value, model.Compact level value →
    model.below value (model.interpret term model.topEnvironment) →
      ∃ reduct approximant, DerivableLatticeEta (fun _ _ => False) term reduct ∧ Closed reduct ∧
        Truncates approximant reduct ∧ Stratified approximant ∧
        model.below value (model.interpret approximant model.topEnvironment)

/-- The proofs file's theorem A in ⊢_{λ-lattice-η}, given a model satisfying the fields of
`DdLP96Model`: the basic lemma puts T in 𝒞(d), and (CA) gives the approximant. -/
theorem approximationLatticeEta : model.ApproximationLatticeEtaHypothesis := by
  intro term closed level value compact below
  have base := model.approximatingLatticeEtaBasic term (arguments := [])
    (environment := model.richEnvironment)
    (fun index occurs => absurd occurs (closed index))
    (fun _ _ found => by simp at found) compact
    (by rw [model.interpretClosed closed model.richEnvironment]; exact below)
  obtain ⟨approximant, ⟨reduct, derivation, included, truncates, stratified⟩, above⟩ :=
    (model.variableAndApproximableLatticeEta level).2 value term compact base
  have reductClosed : Closed reduct := fun index occurs => closed index (included index occurs)
  have approximantClosed : Closed approximant :=
    fun index occurs => reductClosed index (truncates.freeIncluded index occurs)
  refine ⟨reduct, approximant, derivation, reductClosed, truncates, stratified, ?_⟩
  rw [← model.interpretClosed approximantClosed model.richEnvironment]
  exact above

end DdLP96Model

end LambdaJit.ContextualPreorder
