import LambdaJit.ContextualPreorderSeparation

/-!
# The proofs file's theorem S, first half: the combinators and layers of the separation

The parts of the first half of theorem S of the proofs file, section 20.4, that do not mention a derivability relation: the combinators of
the separation, the layers of a conflict, and the head nodes' injectivity, truncation and padded
arguments. A closed T′, a stratified truncation A of T′ and a closed βη normal form N with A ⋪ N
have closed arguments X⃗ with N X⃗ = K and T′ X⃗ refining every closed term; the derivations of
these two equations, in ⊢_{λ-lattice-η} and with Ξ where the proofs file has 0, and the selectors,
Kill and the table they use are module `LatticeEtaSeparation`. No model is used.

The definitions follow the proofs file's layers (20.4.1 to 20.4.3), with these formulation choices:

- Tags. The proofs file numbers every name of every layer and tags the name v by the projection
  τ_v. Here the binders along a path of layers are numbered by their depth, the level, and a binder
  is tagged by the projection of its level. Two binders compared at one layer are both in scope
  there, on one path, so they have different levels whenever they are different binders.
- Width. Every layer applies the same number W of permutators, W at least every abstraction count;
  the proofs file takes the largest abstraction count of the layer, p̄. The next layer of an (R2)
  leaf starts at the depth of the leaf's own alignment, max(n, n′), so its binders do not meet the
  extra binders of the wider alignment.
- Σ is assembled along the conflict derivation inside a layer: a choice node puts the two sides'
  Σ in parallel, a parallel node keeps the chosen side's, and every leaf contributes Φ₀ ∥ Φⱼ.
  By T2 and T3 the extra copies of Φ₀ change nothing.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Closing substitutions, continued -/

/-- A closing substitution by a concatenation is the two substitutions in order. -/
theorem closeAllAppend : ∀ (first second : List Term) (depth : Nat) (term : Term),
    closeAll depth (first ++ second) term = closeAll depth second (closeAll depth first term)
  | [], _, _, _ => rfl
  | replacement :: rest, second, depth, term =>
      closeAllAppend rest second depth (substitute depth replacement term)

/-- Substitution of a closed term at `depth` is carried under abstractions. -/
theorem substituteAbstractAllClosed {replacement : Term} (closed : Closed replacement) :
    ∀ (count depth : Nat) (body : Term),
      substitute depth replacement (abstractAll count body) =
        abstractAll count (substitute (depth + count) replacement body)
  | 0, _, _ => rfl
  | count + 1, depth, body => by
      show Term.abstraction (substitute (depth + 1) (shift replacement) (abstractAll count body)) = _
      rw [shiftClosed closed, substituteAbstractAllClosed closed count (depth + 1) body,
        Nat.add_right_comm, Nat.add_assoc]
      rfl

/-- Closed replacements are carried under abstractions. -/
theorem closeAllAbstractAll : ∀ {replacements : List Term}, AllClosed replacements →
    ∀ (count depth : Nat) (body : Term),
      closeAll depth replacements (abstractAll count body) =
        abstractAll count (closeAll (depth + count) replacements body)
  | [], _, _, _, _ => rfl
  | replacement :: rest, allClosed, count, depth, body => by
      show closeAll depth rest (substitute depth replacement (abstractAll count body)) = _
      rw [substituteAbstractAllClosed (allClosed replacement List.mem_cons_self)]
      exact closeAllAbstractAll (fun term member => allClosed term (List.mem_cons_of_mem _ member))
        count depth _

/-- A closing substitution of a spine substitutes its head and its arguments. -/
theorem closeAllApplyAll : ∀ (replacements : List Term) (depth : Nat) (head : Term)
    (arguments : List Term),
    closeAll depth replacements (applyAll head arguments) =
      applyAll (closeAll depth replacements head) (arguments.map (closeAll depth replacements))
  | replacements, depth, _, [] => rfl
  | replacements, depth, head, argument :: rest => by
      show closeAll depth replacements (applyAll (.application head argument) rest) = _
      rw [closeAllApplyAll replacements depth (.application head argument) rest,
        closeAllApplication]
      rfl

/-- The key commutation of closed substitutions: substituting index |ρ| and then ρ is substituting
ρ and then index 0. -/
theorem closeAllSubstituteLength : ∀ {replacements : List Term}, AllClosed replacements →
    ∀ {replacement : Term}, Closed replacement → ∀ term : Term,
      closeAll 0 replacements (substitute replacements.length replacement term) =
        substitute 0 replacement (closeAll 0 replacements term)
  | [], _, _, _, _ => rfl
  | first :: rest, allClosed, replacement, closed, term => by
      have firstClosed := allClosed first List.mem_cons_self
      have restClosed : AllClosed rest :=
        fun term member => allClosed term (List.mem_cons_of_mem _ member)
      show closeAll 0 rest (substitute 0 first (substitute (rest.length + 1) replacement term)) =
        substitute 0 replacement (closeAll 0 rest (substitute 0 first term))
      have swapped : substitute 0 first (substitute (rest.length + 1) replacement term) =
          substitute rest.length replacement (substitute 0 first term) := by
        rw [BetaEtaConfluence.substituteSubstitute term 0 rest.length first replacement
          (Nat.zero_le _), substituteClosed firstClosed]
        have shifted : shiftFrom 0 replacement = replacement := shiftClosed closed
        rw [shifted]
      rw [swapped]
      exact closeAllSubstituteLength restClosed closed _

/-- Substituting the outer indices first, then the inner ones, is substituting all of them. -/
theorem closeAllCommute : ∀ {inner : List Term}, AllClosed inner →
    ∀ {outer : List Term}, AllClosed outer → ∀ term : Term,
      closeAll 0 inner (closeAll inner.length outer term) = closeAll 0 (inner ++ outer) term
  | inner, innerClosed, [], _, term => by simp [closeAll]
  | inner, innerClosed, first :: rest, outerClosed, term => by
      have firstClosed := outerClosed first List.mem_cons_self
      have restClosed : AllClosed rest :=
        fun term member => outerClosed term (List.mem_cons_of_mem _ member)
      show closeAll 0 inner (closeAll inner.length rest (substitute inner.length first term)) = _
      rw [closeAllCommute innerClosed restClosed, closeAllAppend, closeAllAppend,
        closeAllSubstituteLength innerClosed firstClosed]
      rfl

/-- Vacuous substitutions drop: substituting the indices that a shifted term does not use. -/
theorem closeAllShiftTimes : ∀ (inner : List Term) (outer : List Term) (term : Term),
    closeAll 0 (inner ++ outer) (shiftTimes inner.length term) = closeAll 0 outer term
  | [], _, _ => rfl
  | first :: rest, outer, term => by
      show closeAll 0 (rest ++ outer) (substitute 0 first (shift (shiftTimes rest.length term))) = _
      rw [substituteShift]
      exact closeAllShiftTimes rest outer term

/-- The free indices of a spine. -/
theorem freeBelowApplyAll {bound : Nat} : ∀ {head : Term} {arguments : List Term},
    FreeBelow bound (applyAll head arguments) →
      FreeBelow bound head ∧ ∀ argument ∈ arguments, FreeBelow bound argument
  | _, [], free => ⟨free, fun _ member => absurd member List.not_mem_nil⟩
  | head, argument :: rest, free => by
      obtain ⟨applicationFree, restFree⟩ :=
        freeBelowApplyAll (head := .application head argument) free
      refine ⟨fun index occurs => applicationFree index (.inl occurs), fun term member => ?_⟩
      rcases List.mem_cons.mp member with equal | inRest
      · subst equal
        exact fun index occurs => applicationFree index (.inr occurs)
      · exact restFree term inRest

/-- An index free under abstractions is the index raised by their number in the body. -/
theorem occursFreeAbstractAll : ∀ (count index : Nat) (body : Term),
    OccursFree index (abstractAll count body) ↔ OccursFree (index + count) body
  | 0, _, _ => Iff.rfl
  | count + 1, index, body => by
      show OccursFree (index + 1) (abstractAll count body) ↔ _
      rw [occursFreeAbstractAll count (index + 1) body, Nat.add_right_comm, Nat.add_assoc]

/-- The free indices under abstractions. -/
theorem freeBelowAbstractAll {bound count : Nat} {body : Term}
    (free : FreeBelow bound (abstractAll count body)) : FreeBelow (bound + count) body := by
  intro index occurs
  by_cases below : index < count
  · omega
  · have lowered := free (index - count)
      ((occursFreeAbstractAll count (index - count) body).mpr (by
        rw [Nat.sub_add_cancel (by omega)]
        exact occurs))
    omega

/-- The free indices of a spine, from those of its head and arguments. -/
theorem freeBelowOfApplyAll {bound : Nat} : ∀ {head : Term} {arguments : List Term},
    FreeBelow bound head → (∀ argument ∈ arguments, FreeBelow bound argument) →
      FreeBelow bound (applyAll head arguments)
  | _, [], headFree, _ => headFree
  | head, argument :: _, headFree, argumentsFree =>
      freeBelowOfApplyAll (head := .application head argument)
        (fun index occurs => occurs.elim (headFree index)
          (argumentsFree argument List.mem_cons_self index))
        (fun term member => argumentsFree term (List.mem_cons_of_mem _ member))

/-- The free indices under abstractions, from those of the body. -/
theorem freeBelowOfAbstractAll {bound count : Nat} {body : Term}
    (free : FreeBelow (bound + count) body) : FreeBelow bound (abstractAll count body) := by
  intro index occurs
  have inner := free (index + count) ((occursFreeAbstractAll count index body).mp occurs)
  omega

/-- A variable's free index. -/
theorem freeBelowVariable {bound index : Nat} (below : index < bound) :
    FreeBelow bound (.boundVariable index) := by
  intro other occurs
  simp only [OccursFree] at occurs
  omega

/-- Shifting raises the free indices. -/
theorem freeBelowShiftFrom : ∀ (term : Term) (cutoff : Nat) {bound : Nat},
    FreeBelow bound term → FreeBelow (bound + 1) (shiftFrom cutoff term)
  | .boundVariable position, cutoff, bound, free => by
      have below := free position rfl
      unfold shiftFrom
      split
      · exact freeBelowVariable (by omega)
      · exact freeBelowVariable (by omega)
  | .abstraction body, cutoff, bound, free => by
      have bodyFree : FreeBelow (bound + 1) body := fun index occurs => by
        cases index with
        | zero => omega
        | succ index =>
            have below := free index occurs
            omega
      have shifted := freeBelowShiftFrom body (cutoff + 1) bodyFree
      intro index occurs
      have below := shifted (index + 1) occurs
      omega
  | .application function argument, cutoff, bound, free => by
      intro index occurs
      rcases occurs with inner | inner
      · exact freeBelowShiftFrom function cutoff (fun index occurs => free index (.inl occurs))
          index inner
      · exact freeBelowShiftFrom argument cutoff (fun index occurs => free index (.inr occurs))
          index inner
  | .choice left right, cutoff, bound, free => by
      intro index occurs
      rcases occurs with inner | inner
      · exact freeBelowShiftFrom left cutoff (fun index occurs => free index (.inl occurs)) index inner
      · exact freeBelowShiftFrom right cutoff (fun index occurs => free index (.inr occurs)) index
          inner
  | .parallel left right, cutoff, bound, free => by
      intro index occurs
      rcases occurs with inner | inner
      · exact freeBelowShiftFrom left cutoff (fun index occurs => free index (.inl occurs)) index inner
      · exact freeBelowShiftFrom right cutoff (fun index occurs => free index (.inr occurs)) index
          inner

theorem freeBelowShiftTimes : ∀ (count : Nat) {term : Term} {bound : Nat},
    FreeBelow bound term → FreeBelow (bound + count) (shiftTimes count term)
  | 0, _, _, free => free
  | count + 1, term, bound, free => by
      rw [← Nat.add_assoc]
      exact freeBelowShiftFrom _ 0 (freeBelowShiftTimes count free)

/-- A closed term has no free index. -/
theorem freeBelowOfClosed {term : Term} (closed : Closed term) (bound : Nat) :
    FreeBelow bound term := fun index occurs => absurd occurs (closed index)

/-- A term with no free index is closed. -/
theorem closedOfFreeBelowZero {term : Term} (free : FreeBelow 0 term) : Closed term :=
  fun index occurs => Nat.not_lt_zero _ (free index occurs)

/-- The reverse of a list of closed terms. -/
theorem AllClosed.reverse {terms : List Term} (closed : AllClosed terms) : AllClosed terms.reverse :=
  fun term member => closed term (List.mem_reverse.mp member)

/-- The concatenation of lists of closed terms. -/
theorem AllClosed.append {first second : List Term} (firstClosed : AllClosed first)
    (secondClosed : AllClosed second) : AllClosed (first ++ second) := fun term member =>
  (List.mem_append.mp member).elim (firstClosed term) (secondClosed term)

/-! ## Derivations along spines -/

/-! ## The combinators of the separation (the proofs file, 20.4.1 and 20.4.2) -/

/-- λs₀ … s_{count−1}. s_index: the projection on argument `index` of `count`. The tag τ_ℓ of the
binder of level ℓ is `projection tagCount ℓ`. -/
def projection (count index : Nat) : Term := abstractAll count (.boundVariable (count - 1 - index))

/-- The tagged permutator P_ℓ = λu₁ … u_r. λw. w τ_ℓ u₁ … u_r. -/
def permutator (argumentBound tagCount level : Nat) : Term :=
  abstractAll (argumentBound + 1) (applyAll (.boundVariable 0)
    (projection tagCount level :: (trailingVariables argumentBound).map shift))

/-- Φ₀ = λv₀ … v_r. λe₁ … e_c. K. -/
def constantComponent (argumentBound trailingCount : Nat) : Term :=
  abstractAll (argumentBound + 1 + trailingCount) first

/-- The (R2) component λv₀ … v_r. v_{position+1} 𝒢, where `next` is the next layer's 𝒢. -/
def argumentComponent (argumentBound position : Nat) (next : List Term) : Term :=
  abstractAll (argumentBound + 1) (applyAll (.boundVariable (argumentBound - 1 - position)) next)

theorem closedProjection {count : Nat} (positive : 0 < count) (index : Nat) :
    Closed (projection count index) :=
  closedOfFreeBelowZero (freeBelowOfAbstractAll (freeBelowVariable (by omega)))

/-- The members of `trailingVariables count` are the variables below `count`. -/
theorem memTrailingVariables : ∀ {count : Nat} {term : Term}, term ∈ trailingVariables count →
    ∃ index, index < count ∧ term = .boundVariable index
  | 0, _, member => absurd member List.not_mem_nil
  | count + 1, _, member => by
      rcases List.mem_cons.mp member with equal | rest
      · exact ⟨count, by omega, equal⟩
      · obtain ⟨index, below, equal⟩ := memTrailingVariables rest
        exact ⟨index, by omega, equal⟩

theorem closedPermutator (argumentBound : Nat) {tagCount : Nat} (positive : 0 < tagCount)
    (level : Nat) : Closed (permutator argumentBound tagCount level) := by
  apply closedOfFreeBelowZero
  apply freeBelowOfAbstractAll
  apply freeBelowOfApplyAll (freeBelowVariable (by omega))
  intro term member
  rcases List.mem_cons.mp member with equal | rest
  · subst equal
    exact freeBelowOfClosed (closedProjection positive level) _
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp rest
    obtain ⟨index, below, rfl⟩ := memTrailingVariables originalMember
    exact freeBelowVariable (by simp; omega)

theorem closedConstantComponent (argumentBound trailingCount : Nat) :
    Closed (constantComponent argumentBound trailingCount) :=
  closedOfFreeBelowZero (freeBelowOfAbstractAll (freeBelowOfClosed closedFirst _))

theorem closedArgumentComponent (argumentBound position : Nat) {next : List Term}
    (nextClosed : AllClosed next) : Closed (argumentComponent argumentBound position next) :=
  closedOfFreeBelowZero (freeBelowOfAbstractAll (freeBelowOfApplyAll
    (freeBelowVariable (by omega))
    (fun term member => freeBelowOfClosed (nextClosed term member) _)))

/-! ## The combinators at work -/

/-- Variables beyond a closing substitution are lowered past it. -/
theorem closeAllVariableAbove : ∀ (replacements : List Term) (index : Nat),
    closeAll 0 replacements (.boundVariable (replacements.length + index)) = .boundVariable index
  | [], index => by simp [closeAll]
  | first :: rest, index => by
      show closeAll 0 rest (substitute 0 first (.boundVariable (rest.length + 1 + index))) = _
      have notBelow : ¬ rest.length + 1 + index < 0 := by omega
      have notEqual : ¬ rest.length + 1 + index = 0 := by omega
      simp only [substitute, notBelow, notEqual, ite_false]
      have lowered : rest.length + 1 + index - 1 = rest.length + index := by omega
      rw [lowered]
      exact closeAllVariableAbove rest index

/-- A closing substitution leaves a list of closed terms unchanged. -/
theorem mapCloseAllClosed (replacements : List Term) (depth : Nat) :
    ∀ {terms : List Term}, AllClosed terms → terms.map (closeAll depth replacements) = terms
  | [], _ => rfl
  | first :: rest, allClosed => by
      rw [List.map_cons, closeAllClosed replacements depth (allClosed first List.mem_cons_self),
        mapCloseAllClosed replacements depth
          (fun term member => allClosed term (List.mem_cons_of_mem _ member))]

/-- The variables of `trailingVariables` taken by the reversed list: λu₁ … u_k. (u₁, …, u_k). -/
theorem closeAllTrailing : ∀ (terms : List Term), AllClosed terms →
    (trailingVariables terms.length).map (closeAll 0 terms.reverse) = terms
  | [], _ => rfl
  | first :: rest, allClosed => by
      have firstClosed := allClosed first List.mem_cons_self
      have restClosed : AllClosed rest :=
        fun term member => allClosed term (List.mem_cons_of_mem _ member)
      rw [List.reverse_cons, List.length_cons]
      show (Term.boundVariable rest.length :: trailingVariables rest.length).map
        (closeAll 0 (rest.reverse ++ [first])) = first :: rest
      have composed : closeAll 0 (rest.reverse ++ [first]) =
          closeAll 0 [first] ∘ closeAll 0 rest.reverse :=
        funext fun term => closeAllAppend _ _ _ _
      rw [composed, List.map_cons, ← List.map_map, closeAllTrailing rest restClosed,
        mapCloseAllClosed [first] 0 restClosed]
      have above := closeAllVariableAbove rest.reverse 0
      rw [List.length_reverse, Nat.add_zero] at above
      simp only [Function.comp, above]
      simp [closeAll, substitute]

/-- The selected argument of a reversed list. -/
theorem getElemReverse {terms : List Term} {index : Nat} {selected : Term}
    (found : terms[index]? = some selected) :
    terms.reverse[terms.length - 1 - index]? = some selected := by
  have below : index < terms.length := by
    rcases Nat.lt_or_ge index terms.length with below | above
    · exact below
    · rw [List.getElem?_eq_none above] at found
      exact absurd found (by simp)
  rw [List.getElem?_reverse (by omega)]
  have same : terms.length - 1 - (terms.length - 1 - index) = index := by omega
  rw [same]
  exact found

/-! ## Layers -/

/-- The constants of one separation: r, the number of arguments a permutator takes before w,
V, the number of tags, and W, the number of permutators applied at every layer. -/
structure SeparationConstants where
  /-- r. -/
  argumentBound : Nat
  /-- V. -/
  tagCount : Nat
  /-- W. -/
  width : Nat

variable (constants : SeparationConstants)

/-- σ for a layer at `depth`: the permutator of level depth − 1 − i for index i, the binder of
index i being the binder of level depth − 1 − i. -/
def pathSubstitution (depth : Nat) : List Term :=
  (List.range depth).reverse.map (permutator constants.argumentBound constants.tagCount)

/-- P_{depth}, …, P_{depth+count−1}: the permutators of `count` binders from level `depth` on. -/
def layerPermutators (depth count : Nat) : List Term :=
  (List.range count).map fun offset =>
    permutator constants.argumentBound constants.tagCount (depth + offset)

theorem lengthLayerPermutators (depth count : Nat) :
    (layerPermutators constants depth count).length = count := by
  simp [layerPermutators]

theorem lengthPathSubstitution (depth : Nat) : (pathSubstitution constants depth).length = depth := by
  simp [pathSubstitution]

theorem pathSubstitutionAdd (depth count : Nat) :
    pathSubstitution constants (depth + count) =
      (layerPermutators constants depth count).reverse ++ pathSubstitution constants depth := by
  simp [pathSubstitution, layerPermutators, List.range_add, List.reverse_append, List.map_reverse,
    List.map_map, Function.comp_def]

theorem layerPermutatorsSplit (depth : Nat) {count total : Nat} (atMost : count ≤ total) :
    layerPermutators constants depth total =
      layerPermutators constants depth count ++
        layerPermutators constants (depth + count) (total - count) := by
  have split : total = count + (total - count) := by omega
  conv => lhs; rw [split]
  simp [layerPermutators, List.range_add, Function.comp_def, Nat.add_assoc]

theorem pathSubstitutionLookup {depth index : Nat} (below : index < depth) :
    (pathSubstitution constants depth)[index]? =
      some (permutator constants.argumentBound constants.tagCount (depth - 1 - index)) := by
  simp only [pathSubstitution, List.getElem?_map]
  rw [List.getElem?_reverse (by simpa using below), List.length_range,
    List.getElem?_range (by omega)]
  rfl

theorem layerPermutatorsLookup {depth count index : Nat} (below : index < count) :
    (layerPermutators constants depth count)[index]? =
      some (permutator constants.argumentBound constants.tagCount (depth + index)) := by
  simp [layerPermutators, List.getElem?_range below]

theorem allClosedPathSubstitution (positive : 0 < constants.tagCount) (depth : Nat) :
    AllClosed (pathSubstitution constants depth) := by
  intro term member
  obtain ⟨level, _, rfl⟩ := List.mem_map.mp member
  exact closedPermutator _ positive _

theorem allClosedLayerPermutators (positive : 0 < constants.tagCount) (depth count : Nat) :
    AllClosed (layerPermutators constants depth count) := by
  intro term member
  obtain ⟨level, _, rfl⟩ := List.mem_map.mp member
  exact closedPermutator _ positive _

/-- The head of a head node in scope, and its arguments' free indices. -/
theorem freeBelowHeadNode {bound abstractions head : Nat} {arguments : List Term}
    (free : FreeBelow bound (headNode abstractions head arguments)) :
    head < bound + abstractions ∧
      ∀ argument ∈ arguments, FreeBelow (bound + abstractions) argument := by
  have bodyFree := freeBelowAbstractAll free
  obtain ⟨headFree, argumentsFree⟩ := freeBelowApplyAll bodyFree
  exact ⟨headFree head rfl, argumentsFree⟩

/-- The padded arguments of a head node under the layer's substitution: its arguments under the
substitution of its own abstractions, then the permutators of the extra binders. -/
def paddedSubstituted (depth abstractions : Nat) (arguments : List Term) : List Term :=
  arguments.map (closeAll 0 (pathSubstitution constants (depth + abstractions))) ++
    layerPermutators constants (depth + abstractions) (constants.width - abstractions)

/-! ## Head nodes: injectivity, truncation, padded arguments -/

/-- The head of an application spine. -/
def spineHead : Term → Term
  | .application function _ => spineHead function
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction body
  | .choice left right => .choice left right
  | .parallel left right => .parallel left right

/-- The arguments of an application spine. -/
def spineArguments : Term → List Term
  | .application function argument => spineArguments function ++ [argument]
  | _ => []

theorem spineApplyAll : ∀ (arguments : List Term) (head : Term),
    spineHead (applyAll head arguments) = spineHead head ∧
      spineArguments (applyAll head arguments) = spineArguments head ++ arguments
  | [], _ => ⟨rfl, by simp [applyAll]⟩
  | argument :: rest, head => by
      obtain ⟨headEqual, argumentsEqual⟩ := spineApplyAll rest (.application head argument)
      refine ⟨headEqual, ?_⟩
      show spineArguments (applyAll (.application head argument) rest) = _
      rw [argumentsEqual]
      simp [spineArguments]

/-- Two head nodes are equal only when their abstractions, heads and arguments are. -/
theorem headNodeInjective : ∀ {abstractions otherAbstractions head otherHead : Nat}
    {arguments otherArguments : List Term},
    headNode abstractions head arguments = headNode otherAbstractions otherHead otherArguments →
      abstractions = otherAbstractions ∧ head = otherHead ∧ arguments = otherArguments
  | 0, 0, head, otherHead, arguments, otherArguments, equal => by
      have spines := congrArg spineHead equal
      have argumentsEqual := congrArg spineArguments equal
      simp only [headNode, abstractAll] at spines argumentsEqual
      rw [(spineApplyAll arguments _).1, (spineApplyAll otherArguments _).1] at spines
      rw [(spineApplyAll arguments _).2, (spineApplyAll otherArguments _).2] at argumentsEqual
      simp only [spineHead, Term.boundVariable.injEq] at spines
      simp only [spineArguments, List.nil_append] at argumentsEqual
      exact ⟨rfl, spines, argumentsEqual⟩
  | 0, otherAbstractions + 1, head, otherHead, arguments, otherArguments, equal => by
      have spines := congrArg spineHead equal
      simp only [headNode, abstractAll] at spines
      rw [(spineApplyAll arguments _).1] at spines
      simp [spineHead] at spines
  | abstractions + 1, 0, head, otherHead, arguments, otherArguments, equal => by
      have spines := congrArg spineHead equal
      simp only [headNode, abstractAll] at spines
      rw [(spineApplyAll otherArguments _).1] at spines
      simp [spineHead] at spines
  | abstractions + 1, otherAbstractions + 1, head, otherHead, arguments, otherArguments, equal => by
      simp only [headNode, abstractAll, Term.abstraction.injEq] at equal
      obtain ⟨abstractionsEqual, headEqual, argumentsEqual⟩ :=
        headNodeInjective (abstractions := abstractions) (otherAbstractions := otherAbstractions)
          equal
      exact ⟨by rw [abstractionsEqual], headEqual, argumentsEqual⟩

/-- Pointwise truncation of two lists. -/
def TruncatesAll : List Term → List Term → Prop
  | [], [] => True
  | first :: rest, otherFirst :: otherRest => Truncates first otherFirst ∧ TruncatesAll rest otherRest
  | _, _ => False

theorem TruncatesAll.length : ∀ {approximants terms : List Term},
    TruncatesAll approximants terms → approximants.length = terms.length
  | [], [], _ => rfl
  | _ :: rest, _ :: otherRest, truncates => by
      simp [TruncatesAll.length (approximants := rest) (terms := otherRest) truncates.2]
  | [], _ :: _, truncates => truncates.elim
  | _ :: _, [], truncates => truncates.elim

theorem TruncatesAll.lookup : ∀ {approximants terms : List Term},
    TruncatesAll approximants terms → ∀ {index : Nat} {approximant : Term},
      approximants[index]? = some approximant →
        ∃ term, terms[index]? = some term ∧ Truncates approximant term
  | [], [], _, _, _, found => by simp at found
  | first :: rest, otherFirst :: otherRest, truncates, 0, approximant, found => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨otherFirst, rfl, truncates.1⟩
  | first :: rest, otherFirst :: otherRest, truncates, index + 1, approximant, found => by
      simp only [List.getElem?_cons_succ] at found ⊢
      exact TruncatesAll.lookup truncates.2 found
  | [], _ :: _, truncates, _, _, _ => truncates.elim
  | _ :: _, [], truncates, _, _, _ => truncates.elim

/-- Ω is not a stuck spine applied to an argument: its function is an abstraction. -/
theorem stuckSpineNotSelfApplication : ¬ StuckSpine selfApplication := by
  intro stuck
  cases stuck

/-- Truncation of a spine with a stuck head truncates the head and each argument. -/
theorem truncatesApplyAll : ∀ (arguments : List Term) {head truncated : Term}, StuckSpine head →
    Truncates (applyAll head arguments) truncated →
      ∃ truncatedHead truncatedArguments,
        truncated = applyAll truncatedHead truncatedArguments ∧ Truncates head truncatedHead ∧
          TruncatesAll arguments truncatedArguments
  | [], _, truncated, _, truncates => ⟨truncated, [], rfl, truncates, trivial⟩
  | argument :: rest, head, truncated, stuck, truncates => by
      obtain ⟨applicationTruncated, restTruncated, equal, applicationTruncates, restTruncates⟩ :=
        truncatesApplyAll rest (.application argument stuck) truncates
      cases applicationTruncates with
      | truncated => exact absurd stuck stuckSpineNotSelfApplication
      | application headTruncates argumentTruncates =>
          exact ⟨_, _ :: restTruncated, equal, headTruncates, argumentTruncates, restTruncates⟩

/-- Truncation under abstractions. -/
theorem truncatesAbstractAll : ∀ (count : Nat) {body truncated : Term},
    Truncates (abstractAll count body) truncated →
      ∃ truncatedBody, truncated = abstractAll count truncatedBody ∧ Truncates body truncatedBody
  | 0, _, truncated, truncates => ⟨truncated, rfl, truncates⟩
  | count + 1, _, _, truncates => by
      cases truncates with
      | abstraction inner =>
          obtain ⟨truncatedBody, equal, bodyTruncates⟩ := truncatesAbstractAll count inner
          exact ⟨truncatedBody, by rw [equal]; rfl, bodyTruncates⟩

/-- A truncation of a head node is the same head node over truncations of its arguments: the
truncated subterms are inside the arguments (the proofs file, 20.4.3, 2: "格结构在 T′ 里是字面的"). -/
theorem truncatesHeadNode {abstractions head : Nat} {arguments : List Term} {truncated : Term}
    (truncates : Truncates (headNode abstractions head arguments) truncated) :
    ∃ truncatedArguments, truncated = headNode abstractions head truncatedArguments ∧
      TruncatesAll arguments truncatedArguments := by
  obtain ⟨truncatedBody, equal, bodyTruncates⟩ := truncatesAbstractAll abstractions truncates
  obtain ⟨truncatedHead, truncatedArguments, bodyEqual, headTruncates, argumentsTruncate⟩ :=
    truncatesApplyAll arguments (.boundVariable head) bodyTruncates
  cases headTruncates with
  | boundVariable =>
      exact ⟨truncatedArguments, by rw [equal, bodyEqual]; rfl, argumentsTruncate⟩

/-- Truncation is preserved by shifting. -/
theorem Truncates.shiftFrom {approximant term : Term} (truncates : Truncates approximant term) :
    ∀ cutoff, Truncates (Term.shiftFrom cutoff approximant) (Term.shiftFrom cutoff term) := by
  induction truncates with
  | truncated term =>
      intro cutoff
      rw [shiftFromUnchanged Omega cutoff (fun index _ => closedOmega index)]
      exact .truncated _
  | boundVariable index =>
      intro cutoff
      unfold Term.shiftFrom
      split <;> exact .boundVariable _
  | abstraction _ inner => intro cutoff; exact .abstraction (inner (cutoff + 1))
  | application _ _ functionInner argumentInner =>
      intro cutoff; exact .application (functionInner cutoff) (argumentInner cutoff)
  | choice _ _ leftInner rightInner =>
      intro cutoff; exact .choice (leftInner cutoff) (rightInner cutoff)
  | parallel _ _ leftInner rightInner =>
      intro cutoff; exact .parallel (leftInner cutoff) (rightInner cutoff)

theorem Truncates.shiftTimes {approximant term : Term} (truncates : Truncates approximant term) :
    ∀ count, Truncates (ContextualPreorder.shiftTimes count approximant)
      (ContextualPreorder.shiftTimes count term)
  | 0 => truncates
  | count + 1 => (Truncates.shiftTimes truncates count).shiftFrom 0

/-- The members of `trailingVariables`, by position. -/
theorem trailingVariablesLookup : ∀ {count index : Nat} {term : Term},
    (trailingVariables count)[index]? = some term →
      index < count ∧ term = .boundVariable (count - 1 - index)
  | 0, _, _, found => by simp [trailingVariables] at found
  | count + 1, 0, term, found => by
      simp only [trailingVariables, List.getElem?_cons_zero, Option.some.injEq] at found
      exact ⟨by omega, by rw [← found]; simp⟩
  | count + 1, index + 1, term, found => by
      simp only [trailingVariables, List.getElem?_cons_succ] at found
      obtain ⟨below, equal⟩ := trailingVariablesLookup found
      exact ⟨by omega, by rw [equal]; congr 1; omega⟩

/-- A padded argument is a shifted argument or a new variable. -/
theorem paddedArgumentsLookup {extra : Nat} {arguments : List Term} {index : Nat} {padded : Term}
    (found : (paddedArguments extra arguments)[index]? = some padded) :
    (∃ argument, arguments[index]? = some argument ∧ padded = shiftTimes extra argument) ∨
      (arguments.length ≤ index ∧ index - arguments.length < extra ∧
        padded = .boundVariable (extra - 1 - (index - arguments.length))) := by
  unfold paddedArguments at found
  by_cases below : index < arguments.length
  · rw [List.getElem?_append_left (by simpa using below), List.getElem?_map] at found
    rcases lookup : arguments[index]? with _ | argument
    · rw [lookup] at found
      simp at found
    · rw [lookup] at found
      simp only [Option.map_some, Option.some.injEq] at found
      exact .inl ⟨argument, rfl, found.symm⟩
  · rw [List.getElem?_append_right (by simp; omega), List.length_map] at found
    obtain ⟨variableBelow, equal⟩ := trailingVariablesLookup found
    exact .inr ⟨by omega, variableBelow, equal⟩

/-- The padded arguments of a truncation are truncations of the padded arguments. -/
theorem truncatesPadded {arguments truncatedArguments : List Term}
    (truncates : TruncatesAll arguments truncatedArguments) (extra : Nat) {index : Nat}
    {padded : Term} (found : (paddedArguments extra arguments)[index]? = some padded) :
    ∃ truncatedPadded, (paddedArguments extra truncatedArguments)[index]? = some truncatedPadded ∧
      Truncates padded truncatedPadded := by
  rcases paddedArgumentsLookup found with ⟨argument, argumentFound, rfl⟩ | ⟨atLeast, variableBelow, rfl⟩
  · obtain ⟨truncatedArgument, truncatedFound, argumentTruncates⟩ := truncates.lookup argumentFound
    refine ⟨shiftTimes extra truncatedArgument, ?_, argumentTruncates.shiftTimes extra⟩
    unfold paddedArguments
    have below : index < truncatedArguments.length := by
      rcases Nat.lt_or_ge index truncatedArguments.length with below | above
      · exact below
      · rw [List.getElem?_eq_none above] at truncatedFound
        exact absurd truncatedFound (by simp)
    rw [List.getElem?_append_left (by simpa using below), List.getElem?_map, truncatedFound]
    rfl
  · refine ⟨_, ?_, .boundVariable _⟩
    unfold paddedArguments
    rw [List.getElem?_append_right (by simp; rw [← truncates.length]; omega), List.length_map,
      ← truncates.length]
    clear found
    generalize index - arguments.length = position at variableBelow ⊢
    induction extra generalizing position with
    | zero => omega
    | succ extra inner =>
        cases position with
        | zero => simp [trailingVariables]
        | succ position =>
            simp only [trailingVariables, List.getElem?_cons_succ]
            rw [inner position (by omega)]
            congr 2
            omega

/-- The proofs file's padded arguments under the layer's substitution: the arguments padded by the
alignment max(n, n′) = n + extra, under the substitution at depth D + n + extra, are the padded
arguments the permutator of the head receives. -/
theorem paddedSubstitutedLookup (positive : 0 < constants.tagCount) {depth abstractions extra : Nat}
    (extraAtMost : abstractions + extra ≤ constants.width) {arguments : List Term}
    (argumentsFree : ∀ argument ∈ arguments, FreeBelow (depth + abstractions) argument)
    {index : Nat} {padded : Term} (found : (paddedArguments extra arguments)[index]? = some padded) :
    (paddedSubstituted constants depth abstractions arguments)[index]? =
        some (closeAll 0 (pathSubstitution constants (depth + abstractions + extra)) padded) ∧
      FreeBelow (depth + abstractions + extra) padded := by
  rcases paddedArgumentsLookup found with ⟨argument, argumentFound, rfl⟩ | ⟨atLeast, variableBelow, rfl⟩
  · have argumentFree := argumentsFree argument (List.mem_of_getElem? argumentFound)
    refine ⟨?_, freeBelowShiftTimes extra argumentFree⟩
    have below : index < arguments.length := by
      rcases Nat.lt_or_ge index arguments.length with below | above
      · exact below
      · rw [List.getElem?_eq_none above] at argumentFound
        exact absurd argumentFound (by simp)
    unfold paddedSubstituted
    rw [List.getElem?_append_left (by simpa using below), List.getElem?_map, argumentFound,
      pathSubstitutionAdd constants (depth + abstractions) extra]
    have dropped := closeAllShiftTimes (layerPermutators constants (depth + abstractions) extra).reverse
      (pathSubstitution constants (depth + abstractions)) argument
    rw [List.length_reverse, lengthLayerPermutators] at dropped
    rw [dropped]
    rfl
  · refine ⟨?_, freeBelowVariable (by omega)⟩
    unfold paddedSubstituted
    rw [List.getElem?_append_right (by simp; omega), List.length_map,
      layerPermutatorsLookup constants (by omega),
      closeAllVariable (allClosedPathSubstitution constants positive _)
        (pathSubstitutionLookup constants (by omega))]
    congr 2
    omega

/-! ## The layer lemma -/

theorem termSizePositive : ∀ term : Term, 0 < termSize term
  | .boundVariable _ => by simp [termSize]
  | .abstraction _ => by simp [termSize]
  | .application function _ => by
      have := termSizePositive function
      simp only [termSize]
      omega
  | .choice _ _ => by simp [termSize]
  | .parallel _ _ => by simp [termSize]

theorem lengthAtMostArgumentsSize : ∀ arguments : List Term,
    arguments.length ≤ argumentsSize arguments
  | [] => Nat.le_refl 0
  | first :: rest => by
      have := termSizePositive first
      have := lengthAtMostArgumentsSize rest
      simp only [List.length_cons, argumentsSize]
      omega

theorem closedParallel {left right : Term} (leftClosed : Closed left) (rightClosed : Closed right) :
    Closed (.parallel left right) :=
  fun index occurs => occurs.elim (leftClosed index) (rightClosed index)

theorem lengthPaddedSubstituted (depth abstractions : Nat) (arguments : List Term) :
    (paddedSubstituted constants depth abstractions arguments).length =
      arguments.length + (constants.width - abstractions) := by
  simp [paddedSubstituted, lengthLayerPermutators]

theorem allClosedPaddedSubstituted (positive : 0 < constants.tagCount) {depth abstractions : Nat}
    {arguments : List Term}
    (argumentsFree : ∀ argument ∈ arguments, FreeBelow (depth + abstractions) argument) :
    AllClosed (paddedSubstituted constants depth abstractions arguments) := by
  apply AllClosed.append
  · intro term member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact closeAllClosesTerm (allClosedPathSubstitution constants positive _) (by
      rw [lengthPathSubstitution]
      exact argumentsFree original originalMember)
  · exact allClosedLayerPermutators constants positive _ _

/-- A head node is an abstraction or a spine whose head is its variable. -/
theorem headNodeCases (abstractions head : Nat) (arguments : List Term) :
    (∃ body, headNode abstractions head arguments = .abstraction body) ∨
      spineHead (headNode abstractions head arguments) = .boundVariable head := by
  cases abstractions with
  | zero =>
      right
      simp only [headNode, abstractAll]
      rw [(spineApplyAll arguments _).1]
      rfl
  | succ abstractions => exact .inl ⟨_, rfl⟩

/-- A term that is not an abstraction and whose spine does not start at a variable is no head
node. -/
theorem notHeadNode {term : Term} (notAbstraction : ∀ body, term ≠ .abstraction body)
    (notVariable : ∀ index, spineHead term ≠ .boundVariable index) {abstractions head : Nat}
    {arguments : List Term} : term ≠ headNode abstractions head arguments := by
  intro equal
  rcases headNodeCases abstractions head arguments with ⟨body, isAbstraction⟩ | spine
  · exact notAbstraction body (equal.trans isAbstraction)
  · rw [← equal] at spine
    exact notVariable head spine

theorem omegaNotHeadNode {abstractions head : Nat} {arguments : List Term} :
    Omega ≠ headNode abstractions head arguments :=
  notHeadNode (fun body equal => by unfold Omega at equal; cases equal)
    (fun index equal => by
      simp only [Omega, spineHead, selfApplication] at equal
      cases equal)

theorem parallelNotHeadNode {left right : Term} {abstractions head : Nat} {arguments : List Term} :
    Term.parallel left right ≠ headNode abstractions head arguments :=
  notHeadNode (fun _ equal => by cases equal) (fun _ equal => by cases equal)

theorem choiceNotHeadNode {left right : Term} {abstractions head : Nat} {arguments : List Term} :
    Term.choice left right ≠ headNode abstractions head arguments :=
  notHeadNode (fun _ equal => by cases equal) (fun _ equal => by cases equal)

theorem Stratified.parallelParts {left right : Term} (stratified : Stratified (.parallel left right)) :
    Stratified left ∧ Stratified right := by
  generalize equal : Term.parallel left right = term at stratified
  cases stratified with
  | parallel leftStratified rightStratified =>
      cases equal
      exact ⟨leftStratified, rightStratified⟩
  | headNode _ _ _ _ => exact absurd equal parallelNotHeadNode
  | truncated => exact absurd equal.symm (by unfold Omega; intro equal; cases equal)
  | choice _ _ => cases equal

theorem Stratified.choiceParts {left right : Term} (stratified : Stratified (.choice left right)) :
    Stratified left ∧ Stratified right := by
  generalize equal : Term.choice left right = term at stratified
  cases stratified with
  | choice leftStratified rightStratified =>
      cases equal
      exact ⟨leftStratified, rightStratified⟩
  | headNode _ _ _ _ => exact absurd equal choiceNotHeadNode
  | truncated => exact absurd equal.symm (by unfold Omega; intro equal; cases equal)
  | parallel _ _ => cases equal

theorem Stratified.headNodeArguments {abstractions head : Nat} {arguments : List Term}
    (stratified : Stratified (ContextualPreorder.headNode abstractions head arguments)) :
    ∀ argument ∈ arguments, Stratified argument := by
  generalize equal : ContextualPreorder.headNode abstractions head arguments = term at stratified
  cases stratified with
  | headNode _ _ _ argumentsStratified =>
      obtain ⟨_, _, rfl⟩ := headNodeInjective equal
      exact argumentsStratified
  | truncated => exact absurd equal.symm omegaNotHeadNode
  | choice _ _ => exact absurd equal.symm choiceNotHeadNode
  | parallel _ _ => exact absurd equal.symm parallelNotHeadNode

/-- W·(s′ + 1) ≤ W·s from s′ < s: the room the tags leave shrinks by at least W per layer. -/
theorem tagRoomStep {width smaller larger : Nat} (less : smaller < larger) :
    width * smaller + width ≤ width * larger := by
  have := Nat.mul_le_mul_left width (show smaller + 1 ≤ larger by omega)
  rw [Nat.mul_succ] at this
  exact this

end LambdaJit.ContextualPreorder
