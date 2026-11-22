import LambdaJit.LatticeEtaApproximation

/-!
# Theorem S with Ξ, and the completeness for NF◇_{λ-lattice-η}

The proofs file's section 21: in
⊢_{λ-lattice-η} (module `LatticeEtaDerivability`, the proofs file's ⊢_B), for a closed T and a closed βη normal form N,
{N + T = T} ⊬_{λ-lattice-η} K = K* gives [[T]] ⊑ [[N]] in DdLP96's reading
(`DdLP96Model.completenessLatticeEta`); module `LatticeEtaBridge` reads it through corollary 4.2 as
T ⊑_O N. By contraposition: if [[T]] ⋢ [[N]], theorem A in ⊢_{λ-lattice-η} (module
`LatticeEtaApproximation`) gives a stratified approximant A of a T′, ∅ ⊢_{λ-lattice-η} T = T′,
that conflicts with N (lemma C); theorem S with Ξ A⃗ (`separationLatticeEta`) gives closed X⃗ with
N X⃗ = K and T′ X⃗ refining every closed term (lemma (F)); then N + T = T gives
K + T′ X⃗ = T′ X⃗, and K = K* (`LatticeEta.inconsistentOfChoiceRefines`).

The separation is the proofs file's theorem S (section 20.4), each declaration named after its step
with the suffix `LatticeEta`, or `Xi` where a combinator changed. It differs from the proofs file,
which separates with 0 in the derivability with the unit law:

- Kill = λv₀ … v_r. Ξ and the table U[ℓ ↦ Ξ] (`killXi`, `tableXi`) where the proofs file has
  λv⃗. 0 and U[ℓ ↦ 0];
- assertion 2 of each layer says that P̃σ 𝒢 e⃗ refines every closed term
  (`LatticeEta.RefinesClosedTerms`) instead of P̃σ 𝒢 e⃗ = 0: the property is kept by application to
  anything (where the proofs file uses T5), by a parallel with anything (T3) and by a choice of two
  such terms (where the proofs file uses T4 and 0 + 0 = 0);
- the conflict has no rule (Z) (module `ContextualPreorderSeparation`).

The declarations that do not mention the derivability, Kill or the table are those of module
`ContextualPreorderSeparationProof`.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Derivations along spines, in ⊢_{λ-lattice-η} -/

/-- Several β steps at once: λx₁ … xₙ. B applied to closed a₁, …, aₙ and then to P⃗ is
B[x⃗ := a⃗] P⃗, the closing substitution taking the innermost binder first. -/
theorem betaAllLatticeEta {hypotheses : Term → Term → Prop} : ∀ (arguments : List Term), AllClosed arguments →
    ∀ (body : Term) (rest : List Term),
      DerivableLatticeEta hypotheses (applyAll (abstractAll arguments.length body) (arguments ++ rest))
        (applyAll (closeAll 0 arguments.reverse body) rest)
  | [], _, body, rest => .reflexive _
  | first :: others, allClosed, body, rest => by
      have firstClosed := allClosed first List.mem_cons_self
      have othersClosed : AllClosed others :=
        fun term member => allClosed term (List.mem_cons_of_mem _ member)
      rw [List.reverse_cons, List.length_cons, List.cons_append]
      show DerivableLatticeEta hypotheses
        (applyAll (.application (.abstraction (abstractAll others.length body)) first) (others ++ rest))
        (applyAll (closeAll 0 (others.reverse ++ [first]) body) rest)
      have contracted : instantiate (abstractAll others.length body) first =
          abstractAll others.length (substitute others.length first body) := by
        unfold instantiate
        rw [substituteAbstractAllClosed firstClosed, Nat.zero_add]
      have step : DerivableLatticeEta hypotheses
          (.application (.abstraction (abstractAll others.length body)) first)
          (abstractAll others.length (substitute others.length first body)) :=
        contracted ▸ .beta _ _
      have inner := betaAllLatticeEta (hypotheses := hypotheses) others othersClosed
        (substitute others.length first body) rest
      have reordered : closeAll 0 others.reverse (substitute others.length first body) =
          closeAll 0 (others.reverse ++ [first]) body := by
        rw [closeAllAppend]
        have lengthEqual : others.length = others.reverse.length := List.length_reverse.symm
        rw [lengthEqual, closeAllSubstituteLength othersClosed.reverse firstClosed]
        rfl
      rw [← reordered]
      exact .transitive (LatticeEta.congruenceApplyAll (others ++ rest) step) inner


/-- The congruence in one argument of a spine. -/
theorem congruenceApplyAllArgumentLatticeEta {hypotheses : Term → Term → Prop} (head : Term)
    (before : List Term) {argument other : Term} (after : List Term)
    (equal : DerivableLatticeEta hypotheses argument other) :
    DerivableLatticeEta hypotheses (applyAll head (before ++ argument :: after))
      (applyAll head (before ++ other :: after)) := by
  rw [applyAllAppendAll, applyAllAppendAll]
  exact LatticeEta.congruenceApplyAll after (.congruenceArgument _ equal)

/-! ## The combinators of the separation with Ξ (section 21) -/

/-- The table U[ℓ ↦ Ξ]: `tagCount` terms, Ξ at position `level` and K elsewhere. -/
def tableXi (tagCount level : Nat) : List Term :=
  (List.range tagCount).map fun position => if position = level then fixedPointOfXi else first

/-- Kill = λv₀ … v_r. Ξ. -/
def killXi (argumentBound : Nat) : Term := abstractAll (argumentBound + 1) fixedPointOfXi

/-- The (R1) component λv₀ … v_r. λe₁ … e_c. v₀ U[ℓ ↦ Ξ]. -/
def headComponentXi (argumentBound trailingCount tagCount level : Nat) : Term :=
  abstractAll (argumentBound + 1 + trailingCount)
    (applyAll (.boundVariable (argumentBound + trailingCount)) (tableXi tagCount level))


theorem allClosedTableXi (tagCount level : Nat) : AllClosed (tableXi tagCount level) := by
  intro term member
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp member
  split
  · exact closedFixedPointOfXi
  · exact closedFirst

theorem closedKillXi (argumentBound : Nat) : Closed (killXi argumentBound) :=
  closedOfFreeBelowZero (freeBelowOfAbstractAll (freeBelowOfClosed closedFixedPointOfXi _))


theorem closedHeadComponentXi (argumentBound trailingCount tagCount level : Nat) :
    Closed (headComponentXi argumentBound trailingCount tagCount level) :=
  closedOfFreeBelowZero (freeBelowOfAbstractAll (freeBelowOfApplyAll
    (freeBelowVariable (by omega))
    (fun term member => freeBelowOfClosed (allClosedTableXi tagCount level term member) _)))


/-- (C0) A projection selects its argument. -/
theorem projectionApplyLatticeEta {hypotheses : Term → Term → Prop} {arguments : List Term}
    (allClosed : AllClosed arguments) {index : Nat} {selected : Term}
    (found : arguments[index]? = some selected) (rest : List Term) :
    DerivableLatticeEta hypotheses (applyAll (projection arguments.length index) (arguments ++ rest))
      (applyAll selected rest) := by
  have reduced := betaAllLatticeEta (hypotheses := hypotheses) arguments allClosed
    (.boundVariable (arguments.length - 1 - index)) rest
  rw [closeAllVariable allClosed.reverse (getElemReverse found)] at reduced
  exact reduced

/-- The tag τ_ℓ′ applied to U[ℓ ↦ Ξ] gives Ξ when ℓ′ = ℓ and K otherwise. -/
theorem tagApplyXi {hypotheses : Term → Term → Prop} {tagCount tagLevel : Nat}
    (below : tagLevel < tagCount) (level : Nat) :
    DerivableLatticeEta hypotheses (applyAll (projection tagCount tagLevel) (tableXi tagCount level))
      (if tagLevel = level then fixedPointOfXi else first) := by
  have found : (tableXi tagCount level)[tagLevel]? =
      some (if tagLevel = level then fixedPointOfXi else first) := by
    simp [tableXi, List.getElem?_range below]
  have reduced := projectionApplyLatticeEta (hypotheses := hypotheses) (allClosedTableXi tagCount level) found []
  simp only [tableXi, List.length_map, List.length_range, List.append_nil] at reduced
  exact reduced

/-- (C1) The permutator P_ℓ takes r arguments u⃗ and then w, and puts w at the head:
P_ℓ u⃗ w R⃗ = w τ_ℓ u⃗ R⃗. -/
theorem permutatorApplyLatticeEta {hypotheses : Term → Term → Prop} (argumentBound tagCount level : Nat)
    (positive : 0 < tagCount) {arguments : List Term} (argumentsClosed : AllClosed arguments)
    (length : arguments.length = argumentBound) {selected : Term} (selectedClosed : Closed selected)
    (rest : List Term) :
    DerivableLatticeEta hypotheses
      (applyAll (permutator argumentBound tagCount level) (arguments ++ selected :: rest))
      (applyAll selected (projection tagCount level :: arguments ++ rest)) := by
  have allClosed : AllClosed (arguments ++ [selected]) :=
    argumentsClosed.append (allClosedCons selectedClosed allClosedNil)
  have reduced := betaAllLatticeEta (hypotheses := hypotheses) (arguments ++ [selected]) allClosed
    (applyAll (.boundVariable 0)
      (projection tagCount level :: (trailingVariables argumentBound).map shift)) rest
  have lengthEqual : (arguments ++ [selected]).length = argumentBound + 1 := by simp [length]
  rw [lengthEqual, List.append_assoc, List.singleton_append] at reduced
  unfold permutator
  refine .transitive reduced ?_
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, closeAllApplyAll,
    List.map_cons, closeAllClosed _ _ (closedProjection positive level), List.map_map]
  have headSelected : closeAll 0 (selected :: arguments.reverse) (.boundVariable 0) = selected :=
    closeAllVariable (allClosedCons selectedClosed argumentsClosed.reverse) (by simp)
  have trailingSelected : (trailingVariables argumentBound).map
      (closeAll 0 (selected :: arguments.reverse) ∘ shift) = arguments := by
    have dropped : closeAll 0 (selected :: arguments.reverse) ∘ shift =
        closeAll 0 arguments.reverse :=
      funext fun term => closeAllShiftTimes [selected] arguments.reverse term
    rw [dropped, ← length]
    exact closeAllTrailing arguments argumentsClosed
  rw [headSelected, trailingSelected, ← applyAllAppendAll]
  exact .reflexive _

/-- (C2) Kill takes r + 1 arguments and gives Ξ applied to the rest, which refines every closed
term (lemma (F)). -/
theorem killApplyXi (argumentBound : Nat) {arguments : List Term}
    (allClosed : AllClosed arguments) (length : arguments.length = argumentBound + 1)
    (rest : List Term) :
    LatticeEta.RefinesClosedTerms (applyAll (killXi argumentBound) (arguments ++ rest)) := by
  have reduced := betaAllLatticeEta (hypotheses := fun _ _ => False) arguments allClosed
    fixedPointOfXi rest
  rw [length, closeAllClosed _ _ closedFixedPointOfXi] at reduced
  exact (LatticeEta.refinesClosedTermsApplyAll rest).ofDerivable reduced

/-- (C3) Φ₀ takes r + 1 + c arguments and gives K. -/
theorem constantComponentApplyLatticeEta {hypotheses : Term → Term → Prop} (argumentBound trailingCount : Nat)
    {arguments : List Term} (allClosed : AllClosed arguments)
    (length : arguments.length = argumentBound + 1 + trailingCount) :
    DerivableLatticeEta hypotheses (applyAll (constantComponent argumentBound trailingCount) arguments)
      first := by
  have reduced := betaAllLatticeEta (hypotheses := hypotheses) arguments allClosed first []
  rw [length, List.append_nil, closeAllClosed _ _ closedFirst] at reduced
  exact reduced

/-- (C4) The (R1) component applied to the tag τ_ℓ′, r further arguments and c trailing ones gives
τ_ℓ′ U[ℓ ↦ Ξ]. -/
theorem headComponentApplyXi {hypotheses : Term → Term → Prop}
    (argumentBound trailingCount tagCount level : Nat) {tag : Term} (tagClosed : Closed tag)
    {others : List Term} (othersClosed : AllClosed others)
    (length : others.length = argumentBound + trailingCount) :
    DerivableLatticeEta hypotheses
      (applyAll (headComponentXi argumentBound trailingCount tagCount level) (tag :: others))
      (applyAll tag (tableXi tagCount level)) := by
  have allClosed := allClosedCons tagClosed othersClosed
  have reduced := betaAllLatticeEta (hypotheses := hypotheses) (tag :: others) allClosed
    (applyAll (.boundVariable (argumentBound + trailingCount)) (tableXi tagCount level)) []
  have lengthEqual : (tag :: others).length = argumentBound + 1 + trailingCount := by
    simp [length]; omega
  rw [lengthEqual, List.append_nil, closeAllApplyAll,
    mapCloseAllClosed _ _ (allClosedTableXi tagCount level)] at reduced
  have found : (tag :: others).reverse[argumentBound + trailingCount]? = some tag := by
    have := getElemReverse (terms := tag :: others) (index := 0) (selected := tag) rfl
    simp only [List.length_cons] at this
    rw [show others.length + 1 - 1 - 0 = argumentBound + trailingCount by omega] at this
    exact this
  rw [closeAllVariable allClosed.reverse found] at reduced
  exact reduced

/-- (C5) The (R2) component applied to v₀ … v_r selects v_{position+1} and applies it to the next
layer's arguments and the rest. -/
theorem argumentComponentApplyLatticeEta {hypotheses : Term → Term → Prop} (argumentBound position : Nat)
    (positionBelow : position < argumentBound) {next : List Term} (nextClosed : AllClosed next)
    {arguments : List Term} (allClosed : AllClosed arguments)
    (length : arguments.length = argumentBound + 1) {selected : Term}
    (found : arguments[position + 1]? = some selected) (rest : List Term) :
    DerivableLatticeEta hypotheses (applyAll (argumentComponent argumentBound position next) (arguments ++ rest))
      (applyAll selected (next ++ rest)) := by
  have reduced := betaAllLatticeEta (hypotheses := hypotheses) arguments allClosed
    (applyAll (.boundVariable (argumentBound - 1 - position)) next) rest
  have reversedFound : arguments.reverse[argumentBound - 1 - position]? = some selected := by
    have := getElemReverse found
    rw [show arguments.length - 1 - (position + 1) = argumentBound - 1 - position by omega] at this
    exact this
  rw [length, closeAllApplyAll, mapCloseAllClosed _ _ nextClosed,
    closeAllVariable allClosed.reverse reversedFound, ← applyAllAppendAll] at reduced
  exact reduced

variable (constants : SeparationConstants)

/-- Q₁, …, Q_{r+1}: Σ at position r − b (from 0), Kill elsewhere. -/
def selectorsXi (count : Nat) (sigma : Term) : List Term :=
  List.replicate (constants.argumentBound - count) (killXi constants.argumentBound) ++
    sigma :: List.replicate count (killXi constants.argumentBound)

theorem allClosedReplicateKillXi (count : Nat) :
    AllClosed (List.replicate count (killXi constants.argumentBound)) := by
  intro term member
  rw [(List.mem_replicate.mp member).2]
  exact closedKillXi _

theorem allClosedSelectorsXi (count : Nat) {sigma : Term} (sigmaClosed : Closed sigma) :
    AllClosed (selectorsXi constants count sigma) :=
  (allClosedReplicateKillXi constants _).append
    (allClosedCons sigmaClosed (allClosedReplicateKillXi constants _))

theorem lengthSelectorsXi {count : Nat} (atMost : count ≤ constants.argumentBound) (sigma : Term) :
    (selectorsXi constants count sigma).length = constants.argumentBound + 1 := by
  simp [selectorsXi]
  omega

/-- The selector the leaf with α padded arguments picks, α ≠ b: Kill. -/
theorem selectorsOtherXi {count other : Nat} (countAtMost : count ≤ constants.argumentBound)
    (otherAtMost : other ≤ constants.argumentBound) (different : other ≠ count) (sigma : Term) :
    (selectorsXi constants count sigma)[constants.argumentBound - other]? =
      some (killXi constants.argumentBound) := by
  unfold selectorsXi
  by_cases before : constants.argumentBound - other < constants.argumentBound - count
  · rw [List.getElem?_append_left (by simpa using before)]
    simp [before]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    have position : constants.argumentBound - other - (constants.argumentBound - count) =
        (constants.argumentBound - other - (constants.argumentBound - count) - 1) + 1 := by omega
    rw [position, List.getElem?_cons_succ]
    simp [List.getElem?_replicate]
    omega

/-- The parts of the selectorsXi around Σ. -/
theorem selectorsSelectedXi {count : Nat} (sigma : Term) :
    (selectorsXi constants count sigma)[constants.argumentBound - count]? = some sigma ∧
    (selectorsXi constants count sigma).take (constants.argumentBound - count) =
      List.replicate (constants.argumentBound - count) (killXi constants.argumentBound) ∧
    (selectorsXi constants count sigma).drop (constants.argumentBound - count + 1) =
      List.replicate count (killXi constants.argumentBound) := by
  unfold selectorsXi
  refine ⟨?_, ?_, ?_⟩
  · rw [List.getElem?_append_right (by simp)]
    simp
  · simp
  · rw [List.drop_append]
    simp [Nat.add_sub_cancel_left]

/-- The head node lemma (the proofs file, 20.4.3, the first step of 1 and of 2): a head node
λx₁ … xₙ. y A⃗ under σ, applied to the W permutators of the layer, the r + 1 selectorsXi Q⃗ and the
rest, becomes P_y applied to its padded arguments; P_y takes r of them and puts the selector at
position r − α at the head, α = m + W − n. -/
theorem headNodeApplyLatticeEta {hypotheses : Term → Term → Prop} (positive : 0 < constants.tagCount)
    {depth abstractions head : Nat} {arguments : List Term}
    (abstractionsAtMost : abstractions ≤ constants.width)
    (headBelow : head < depth + abstractions)
    (argumentsFree : ∀ argument ∈ arguments, FreeBelow (depth + abstractions) argument)
    (countAtMost : arguments.length + (constants.width - abstractions) ≤ constants.argumentBound)
    {selectorList : List Term} (selectorsClosed : AllClosed selectorList)
    (selectorsLength : selectorList.length = constants.argumentBound + 1) {selected : Term}
    (found : selectorList[constants.argumentBound -
      (arguments.length + (constants.width - abstractions))]? = some selected)
    (rest : List Term) :
    DerivableLatticeEta hypotheses
      (applyAll (closeAll 0 (pathSubstitution constants depth) (headNode abstractions head arguments))
        (layerPermutators constants depth constants.width ++ selectorList ++ rest))
      (applyAll selected
        (projection constants.tagCount (depth + abstractions - 1 - head) ::
          (paddedSubstituted constants depth abstractions arguments ++
            selectorList.take (constants.argumentBound -
              (arguments.length + (constants.width - abstractions)))) ++
          (selectorList.drop (constants.argumentBound -
            (arguments.length + (constants.width - abstractions)) + 1) ++ rest))) := by
  have pathClosed := allClosedPathSubstitution constants positive depth
  have innerClosed := allClosedLayerPermutators constants positive depth abstractions
  have outerClosed := allClosedPathSubstitution constants positive (depth + abstractions)
  unfold headNode
  rw [closeAllAbstractAll pathClosed, Nat.zero_add,
    layerPermutatorsSplit constants depth abstractionsAtMost, List.append_assoc, List.append_assoc]
  have reduced := betaAllLatticeEta (hypotheses := hypotheses) (layerPermutators constants depth abstractions)
    innerClosed (closeAll abstractions (pathSubstitution constants depth)
      (applyAll (.boundVariable head) arguments))
    (layerPermutators constants (depth + abstractions) (constants.width - abstractions) ++
      (selectorList ++ rest))
  rw [lengthLayerPermutators] at reduced
  refine .transitive reduced ?_
  have commuted := closeAllCommute innerClosed.reverse pathClosed
    (applyAll (.boundVariable head) arguments)
  rw [List.length_reverse, lengthLayerPermutators, ← pathSubstitutionAdd] at commuted
  rw [commuted, closeAllApplyAll,
    closeAllVariable outerClosed (pathSubstitutionLookup constants headBelow), ← applyAllAppendAll]
  have selectedBelow : constants.argumentBound -
      (arguments.length + (constants.width - abstractions)) < selectorList.length := by omega
  have selectedEqual : selectorList[constants.argumentBound -
      (arguments.length + (constants.width - abstractions))] = selected := by
    rw [List.getElem?_eq_getElem selectedBelow] at found
    exact Option.some.inj found
  have rearranged :
      arguments.map (closeAll 0 (pathSubstitution constants (depth + abstractions))) ++
        (layerPermutators constants (depth + abstractions) (constants.width - abstractions) ++
          (selectorList ++ rest)) =
      (paddedSubstituted constants depth abstractions arguments ++
          selectorList.take (constants.argumentBound -
            (arguments.length + (constants.width - abstractions)))) ++
        selected :: (selectorList.drop (constants.argumentBound -
          (arguments.length + (constants.width - abstractions)) + 1) ++ rest) := by
    conv => lhs; rw [← List.take_append_drop (constants.argumentBound -
      (arguments.length + (constants.width - abstractions))) selectorList]
    rw [List.drop_eq_getElem_cons selectedBelow, selectedEqual]
    simp [paddedSubstituted]
  rw [rearranged]
  have argumentsClosed : AllClosed
      (arguments.map (closeAll 0 (pathSubstitution constants (depth + abstractions)))) := by
    intro term member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact closeAllClosesTerm outerClosed (by
      rw [lengthPathSubstitution]
      exact argumentsFree original originalMember)
  have selectedClosed : Closed selected :=
    selectorsClosed selected (List.mem_of_getElem? found)
  apply permutatorApplyLatticeEta constants.argumentBound constants.tagCount _ positive
  · exact (argumentsClosed.append (allClosedLayerPermutators constants positive _ _)).append
      (fun term member => selectorsClosed term (List.mem_of_mem_take member))
  · simp [paddedSubstituted, lengthLayerPermutators]
    omega
  · exact selectedClosed

/-! ## Head nodes: injectivity, truncation, padded arguments -/

/-- The arguments the components of Σ receive at a layer whose candidate is λx₁ … xₙ. y B⃗: the
tag of y, the r further arguments its permutator took (its b padded arguments, then r − b Kills),
then the b Kills after Σ and the trailing arguments. -/
def candidateArgumentsXi (depth abstractions head : Nat) (arguments trailing : List Term) :
    List Term :=
  projection constants.tagCount (depth + abstractions - 1 - head) ::
    (paddedSubstituted constants depth abstractions arguments ++
      List.replicate (constants.argumentBound - (arguments.length + (constants.width - abstractions)))
        (killXi constants.argumentBound)) ++
    (List.replicate (arguments.length + (constants.width - abstractions))
      (killXi constants.argumentBound) ++ trailing)

/-- The head node lemma for the candidate, whose selector at r − b is Σ. -/
theorem candidateApplyXi {hypotheses : Term → Term → Prop} (positive : 0 < constants.tagCount)
    {depth abstractions head : Nat} {arguments : List Term}
    (abstractionsAtMost : abstractions ≤ constants.width)
    (headBelow : head < depth + abstractions)
    (argumentsFree : ∀ argument ∈ arguments, FreeBelow (depth + abstractions) argument)
    (countAtMost : arguments.length + (constants.width - abstractions) ≤ constants.argumentBound)
    {sigma : Term} (sigmaClosed : Closed sigma) (trailing : List Term) :
    DerivableLatticeEta hypotheses
      (applyAll (closeAll 0 (pathSubstitution constants depth) (headNode abstractions head arguments))
        (layerPermutators constants depth constants.width ++
          selectorsXi constants (arguments.length + (constants.width - abstractions)) sigma ++
          trailing))
      (applyAll sigma (candidateArgumentsXi constants depth abstractions head arguments trailing)) := by
  obtain ⟨found, taken, dropped⟩ :=
    selectorsSelectedXi constants (count := arguments.length + (constants.width - abstractions)) sigma
  have applied := headNodeApplyLatticeEta constants (hypotheses := hypotheses) positive abstractionsAtMost
    headBelow argumentsFree countAtMost (allClosedSelectorsXi constants _ sigmaClosed)
    (lengthSelectorsXi constants countAtMost sigma) found trailing
  rw [taken, dropped] at applied
  exact applied

theorem lengthCandidateArgumentsXi {depth abstractions head : Nat} {arguments : List Term}
    (countAtMost : arguments.length + (constants.width - abstractions) ≤ constants.argumentBound)
    (trailing : List Term) :
    (candidateArgumentsXi constants depth abstractions head arguments trailing).length =
      constants.argumentBound + 1 +
        (arguments.length + (constants.width - abstractions) + trailing.length) := by
  simp [candidateArgumentsXi, lengthPaddedSubstituted]
  omega

theorem allClosedCandidateArgumentsXi (positive : 0 < constants.tagCount)
    {depth abstractions head : Nat} {arguments : List Term}
    (argumentsFree : ∀ argument ∈ arguments, FreeBelow (depth + abstractions) argument)
    {trailing : List Term} (trailingClosed : AllClosed trailing) :
    AllClosed (candidateArgumentsXi constants depth abstractions head arguments trailing) :=
  allClosedCons (closedProjection positive _)
    (((allClosedPaddedSubstituted constants positive argumentsFree).append
      (allClosedReplicateKillXi constants _)).append
      ((allClosedReplicateKillXi constants _).append trailingClosed))

/-- Σ in the selectorsXi may be replaced by a term equal to it. -/
theorem selectorsCongruenceXi {hypotheses : Term → Term → Prop} (head : Term) (before : List Term)
    (count : Nat) {sigma other : Term} (equal : DerivableLatticeEta hypotheses sigma other)
    (trailing : List Term) :
    DerivableLatticeEta hypotheses (applyAll head (before ++ selectorsXi constants count sigma ++ trailing))
      (applyAll head (before ++ selectorsXi constants count other ++ trailing)) := by
  have rearranged : ∀ term : Term, before ++ selectorsXi constants count term ++ trailing =
      (before ++ List.replicate (constants.argumentBound - count) (killXi constants.argumentBound)) ++
        term :: (List.replicate count (killXi constants.argumentBound) ++ trailing) := by
    intro term
    simp [selectorsXi]
  rw [rearranged, rearranged]
  exact congruenceApplyAllArgumentLatticeEta head _ _ equal

/-- A layer's Σ in ⊢_{λ-lattice-η} (section 21's assertion): for a layer (P, M)
at depth D, P a stratified truncation of P̃, M = λx₁ … xₙ. y B⃗ β normal, both with their free
indices bound by the path, there is a closed Σ such that the components of Σ give K on the
candidate's arguments (assertion 1), and P̃ under σ applied to the layer's permutators, the
selectors with Σ ∥ X at the candidate's position, and t trailing arguments refines every closed
term, for every closed X (assertion 2, with Ξ A⃗ where the proofs file has 0). -/
theorem layerSeparationXi (positive : 0 < constants.tagCount)
    (argumentRoom : constants.width + constants.width ≤ constants.argumentBound)
    {approximant candidate : Term} (conflicts : Conflicts approximant candidate) :
    ∀ {abstractions head : Nat} {arguments : List Term},
      candidate = headNode abstractions head arguments →
      (∀ argument ∈ arguments, BetaNormal argument) →
      ∀ {truncated : Term} {depth : Nat} (trailingCount : Nat),
        Truncates approximant truncated → Stratified approximant →
        FreeBelow depth truncated → FreeBelow depth candidate →
        termSize approximant + termSize candidate ≤ constants.width →
        depth + constants.width * (termSize approximant + termSize candidate) ≤ constants.tagCount →
        ∃ sigma, Closed sigma ∧
          (∀ trailing, AllClosed trailing → trailing.length = trailingCount →
            DerivableLatticeEta (fun _ _ => False)
              (applyAll sigma
                (candidateArgumentsXi constants depth abstractions head arguments trailing))
              first) ∧
          (∀ other, Closed other → ∀ trailing, AllClosed trailing →
            trailing.length = trailingCount →
            LatticeEta.RefinesClosedTerms
              (applyAll (closeAll 0 (pathSubstitution constants depth) truncated)
                (layerPermutators constants depth constants.width ++
                  selectorsXi constants (arguments.length + (constants.width - abstractions))
                    (.parallel sigma other) ++ trailing))) := by
  induction conflicts with
  | parallelLeft right _ inner =>
      intro abstractions head arguments candidateEqual argumentsNormal truncated depth
        trailingCount truncates stratified truncatedFree candidateFree
        sizeAtMost tagRoom
      cases truncates with
      | parallel leftTruncates rightTruncates =>
      simp only [termSize] at sizeAtMost tagRoom
      obtain ⟨sigma, sigmaClosed, candidateSide, approximantSide⟩ :=
        inner candidateEqual argumentsNormal trailingCount leftTruncates stratified.parallelParts.1
          (fun index occurs => truncatedFree index (.inl occurs)) candidateFree (by omega)
          (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) tagRoom)
      refine ⟨sigma, sigmaClosed, candidateSide, ?_⟩
      intro other otherClosed trailing trailingClosed trailingLength
      rw [closeAllParallel]
      exact ((approximantSide other otherClosed trailing trailingClosed trailingLength).parallelLeft
        _).ofDerivable (LatticeEta.parallelApplyAll _ _ _)
  | parallelRight left _ inner =>
      intro abstractions head arguments candidateEqual argumentsNormal truncated depth
        trailingCount truncates stratified truncatedFree candidateFree
        sizeAtMost tagRoom
      cases truncates with
      | parallel leftTruncates rightTruncates =>
      simp only [termSize] at sizeAtMost tagRoom
      obtain ⟨sigma, sigmaClosed, candidateSide, approximantSide⟩ :=
        inner candidateEqual argumentsNormal trailingCount rightTruncates stratified.parallelParts.2
          (fun index occurs => truncatedFree index (.inr occurs)) candidateFree (by omega)
          (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) tagRoom)
      refine ⟨sigma, sigmaClosed, candidateSide, ?_⟩
      intro other otherClosed trailing trailingClosed trailingLength
      rw [closeAllParallel]
      exact ((approximantSide other otherClosed trailing trailingClosed trailingLength).parallelRight
        _).ofDerivable (LatticeEta.parallelApplyAll _ _ _)
  | choice _ _ leftInner rightInner =>
      intro abstractions head arguments candidateEqual argumentsNormal truncated depth
        trailingCount truncates stratified truncatedFree candidateFree
        sizeAtMost tagRoom
      cases truncates with
      | choice leftTruncates rightTruncates =>
      simp only [termSize] at sizeAtMost tagRoom
      obtain ⟨leftSigma, leftClosed, leftCandidate, leftApproximant⟩ :=
        leftInner candidateEqual argumentsNormal trailingCount leftTruncates
          stratified.choiceParts.1
          (fun index occurs => truncatedFree index (.inl occurs)) candidateFree (by omega)
          (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) tagRoom)
      obtain ⟨rightSigma, rightClosed, rightCandidate, rightApproximant⟩ :=
        rightInner candidateEqual argumentsNormal trailingCount rightTruncates
          stratified.choiceParts.2
          (fun index occurs => truncatedFree index (.inr occurs)) candidateFree (by omega)
          (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) tagRoom)
      refine ⟨.parallel leftSigma rightSigma, closedParallel leftClosed rightClosed, ?_, ?_⟩
      · intro trailing trailingClosed trailingLength
        exact .transitive (LatticeEta.parallelApplyAll _ _ _)
          (.transitive (.congruenceParallelLeft _ (leftCandidate trailing trailingClosed trailingLength))
            (.transitive (.congruenceParallelRight _
              (rightCandidate trailing trailingClosed trailingLength))
              (.parallelIdempotent _)))
      · intro other otherClosed trailing trailingClosed trailingLength
        have leftZero := leftApproximant (.parallel rightSigma other)
          (closedParallel rightClosed otherClosed) trailing trailingClosed trailingLength
        have rightZero := rightApproximant (.parallel leftSigma other)
          (closedParallel leftClosed otherClosed) trailing trailingClosed trailingLength
        rw [closeAllChoice]
        exact (LatticeEta.RefinesClosedTerms.choice
            (leftZero.ofDerivable (selectorsCongruenceXi constants _ _ _
              (DerivableLatticeEta.parallelAssociative leftSigma rightSigma other) trailing))
            (rightZero.ofDerivable (selectorsCongruenceXi constants _ _ _
              (.transitive (DerivableLatticeEta.congruenceParallelLeft other
                  (.parallelCommutative leftSigma rightSigma))
                (DerivableLatticeEta.parallelAssociative rightSigma leftSigma other)) trailing))).ofDerivable
          (LatticeEta.choiceApplyAll _ _ _)
  | rootDisagree approximantAbstractions approximantHead approximantArguments
      normalAbstractions normalHead normalArguments disagree =>
      intro abstractions head arguments candidateEqual _ truncated depth trailingCount
        truncates _ truncatedFree candidateFree sizeAtMost tagRoom
      obtain ⟨rfl, rfl, rfl⟩ := headNodeInjective candidateEqual
      obtain ⟨truncatedArguments, rfl, argumentsTruncate⟩ := truncatesHeadNode truncates
      have sameLength := argumentsTruncate.length
      obtain ⟨approximantHeadBelow, truncatedArgumentsFree⟩ := freeBelowHeadNode truncatedFree
      obtain ⟨candidateHeadBelow, candidateArgumentsFree⟩ := freeBelowHeadNode candidateFree
      rw [termSizeHeadNode, termSizeHeadNode] at sizeAtMost tagRoom
      have := lengthAtMostArgumentsSize approximantArguments
      have := lengthAtMostArgumentsSize normalArguments
      have widthAtMost : constants.width ≤ constants.width * (1 + argumentsSize approximantArguments +
          approximantAbstractions + (1 + argumentsSize normalArguments + normalAbstractions)) :=
        Nat.le_mul_of_pos_right constants.width (by omega)
      have countAtMost : normalArguments.length + (constants.width - normalAbstractions) ≤
          constants.argumentBound := by omega
      have approximantCountAtMost : truncatedArguments.length +
          (constants.width - approximantAbstractions) ≤ constants.argumentBound := by omega
      have candidateLevelBelow : depth + normalAbstractions - 1 - normalHead <
          constants.tagCount := by omega
      have approximantLevelBelow : depth + approximantAbstractions - 1 - approximantHead <
          constants.tagCount := by omega
      have constantK : ∀ trailing, AllClosed trailing → trailing.length = trailingCount →
          DerivableLatticeEta (fun _ _ => False)
            (applyAll (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
              (candidateArgumentsXi constants depth normalAbstractions normalHead normalArguments
                trailing)) first := by
        intro trailing trailingClosed trailingLength
        exact constantComponentApplyLatticeEta constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount)
          (allClosedCandidateArgumentsXi constants positive candidateArgumentsFree trailingClosed)
          (by rw [lengthCandidateArgumentsXi constants countAtMost, trailingLength])
      by_cases equalCounts : truncatedArguments.length + (constants.width - approximantAbstractions) =
          normalArguments.length + (constants.width - normalAbstractions)
      · -- (R1) with α = b: the heads differ, and the (R1) component tells them apart.
        have levelsDiffer : depth + approximantAbstractions - 1 - approximantHead ≠
            depth + normalAbstractions - 1 - normalHead := by
          intro same
          apply disagree
          unfold RootAgree
          have := Nat.le_max_left approximantAbstractions normalAbstractions
          have := Nat.le_max_right approximantAbstractions normalAbstractions
          have : max approximantAbstractions normalAbstractions = approximantAbstractions ∨
              max approximantAbstractions normalAbstractions = normalAbstractions := by
            rcases Nat.le_total approximantAbstractions normalAbstractions with ordered | ordered
            · exact .inr (Nat.max_eq_right ordered)
            · exact .inl (Nat.max_eq_left ordered)
          constructor <;> omega
        refine ⟨.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
            (headComponentXi constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) constants.tagCount
              (depth + approximantAbstractions - 1 - approximantHead)),
          closedParallel (closedConstantComponent _ _) (closedHeadComponentXi _ _ _ _), ?_, ?_⟩
        · intro trailing trailingClosed trailingLength
          have argumentsClosed := allClosedCandidateArgumentsXi constants positive
            (head := normalHead) candidateArgumentsFree trailingClosed
          have headK := headComponentApplyXi (hypotheses := fun _ _ => False)
            constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) constants.tagCount
            (depth + approximantAbstractions - 1 - approximantHead)
            (closedProjection positive (depth + normalAbstractions - 1 - normalHead))
            (fun term member => argumentsClosed term (List.mem_cons_of_mem _ member))
            (by simp [lengthPaddedSubstituted, trailingLength]; omega)
          have tagK := tagApplyXi (hypotheses := fun _ _ => False) candidateLevelBelow
            (depth + approximantAbstractions - 1 - approximantHead)
          rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm levelsDiffer))] at tagK
          exact .transitive (LatticeEta.parallelApplyAll _ _ _)
            (.transitive (.congruenceParallelLeft _ (constantK trailing trailingClosed trailingLength))
              (.transitive (.congruenceParallelRight _ (.transitive headK tagK))
                (.parallelIdempotent _)))
        · intro other otherClosed trailing trailingClosed trailingLength
          obtain ⟨found, taken, dropped⟩ := selectorsSelectedXi constants
            (count := normalArguments.length + (constants.width - normalAbstractions))
            (.parallel (.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
              (headComponentXi constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) constants.tagCount
                (depth + approximantAbstractions - 1 - approximantHead))) other)
          have foundAtLeaf : (selectorsXi constants
              (normalArguments.length + (constants.width - normalAbstractions))
              (.parallel (.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
                (headComponentXi constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) constants.tagCount
                  (depth + approximantAbstractions - 1 - approximantHead))) other))[
                constants.argumentBound - (truncatedArguments.length +
                  (constants.width - approximantAbstractions))]? =
              some (.parallel (.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
                (headComponentXi constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) constants.tagCount
                  (depth + approximantAbstractions - 1 - approximantHead))) other) := by
            rw [equalCounts]
            exact found
          have applied := headNodeApplyLatticeEta constants (hypotheses := fun _ _ => False) positive
            (by omega) approximantHeadBelow truncatedArgumentsFree approximantCountAtMost
            (allClosedSelectorsXi constants _ (closedParallel (closedParallel
              (closedConstantComponent _ _) (closedHeadComponentXi _ _ _ _)) otherClosed))
            (lengthSelectorsXi constants countAtMost _) foundAtLeaf trailing
          rw [equalCounts, taken, dropped] at applied
          have leafArgumentsClosed : AllClosed
              (paddedSubstituted constants depth approximantAbstractions truncatedArguments ++
                List.replicate (constants.argumentBound -
                  (normalArguments.length + (constants.width - normalAbstractions)))
                  (killXi constants.argumentBound) ++
                (List.replicate (normalArguments.length +
                  (constants.width - normalAbstractions)) (killXi constants.argumentBound) ++
                  trailing)) :=
            ((allClosedPaddedSubstituted constants positive truncatedArgumentsFree).append
              (allClosedReplicateKillXi constants _)).append
              ((allClosedReplicateKillXi constants _).append trailingClosed)
          have headZero := headComponentApplyXi (hypotheses := fun _ _ => False)
            constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) constants.tagCount
            (depth + approximantAbstractions - 1 - approximantHead)
            (closedProjection positive (depth + approximantAbstractions - 1 - approximantHead))
            leafArgumentsClosed
            (by simp [lengthPaddedSubstituted, trailingLength]; omega)
          have tagZero := tagApplyXi (hypotheses := fun _ _ => False) approximantLevelBelow
            (depth + approximantAbstractions - 1 - approximantHead)
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at tagZero
          have headRefines := LatticeEta.refinesClosedTermsXi.ofDerivable (.transitive headZero tagZero)
          exact ((((headRefines.parallelRight _).ofDerivable (LatticeEta.parallelApplyAll _ _ _)).parallelLeft
            _).ofDerivable (LatticeEta.parallelApplyAll _ _ _)).ofDerivable applied
      · -- (R1) with α ≠ b: the leaf selects Kill.
        refine ⟨constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount),
          closedConstantComponent _ _, constantK, ?_⟩
        intro other otherClosed trailing trailingClosed trailingLength
        have found := selectorsOtherXi constants countAtMost approximantCountAtMost equalCounts
          (.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount)) other)
        have applied := headNodeApplyLatticeEta constants (hypotheses := fun _ _ => False) positive
          (by omega) approximantHeadBelow truncatedArgumentsFree approximantCountAtMost
          (allClosedSelectorsXi constants _ (closedParallel (closedConstantComponent _ _) otherClosed))
          (lengthSelectorsXi constants countAtMost _) found trailing
        refine LatticeEta.RefinesClosedTerms.ofDerivable applied
          (killApplyXi constants.argumentBound ?_ ?_ _)
        · exact allClosedCons (closedProjection positive _)
            ((allClosedPaddedSubstituted constants positive truncatedArgumentsFree).append
              (fun term member => allClosedSelectorsXi constants _
                (closedParallel (closedConstantComponent _ _) otherClosed) term
                (List.mem_of_mem_take member)))
        · simp [lengthPaddedSubstituted, lengthSelectorsXi constants countAtMost]
          omega
  | @argument approximantAbstractions approximantHead approximantArguments
      normalAbstractions normalHead normalArguments position lowerArgument upperArgument
      agree lowerFound upperFound _ inner =>
      intro abstractions head arguments candidateEqual argumentsNormal truncated depth
        trailingCount truncates stratified truncatedFree candidateFree
        sizeAtMost tagRoom
      obtain ⟨rfl, rfl, rfl⟩ := headNodeInjective candidateEqual
      have approximantArgumentsStratified := stratified.headNodeArguments
      obtain ⟨truncatedArguments, rfl, argumentsTruncate⟩ := truncatesHeadNode truncates
      have sameLength := argumentsTruncate.length
      obtain ⟨approximantHeadBelow, truncatedArgumentsFree⟩ := freeBelowHeadNode truncatedFree
      obtain ⟨candidateHeadBelow, candidateArgumentsFree⟩ := freeBelowHeadNode candidateFree
      have lowerSize := termSizePaddedArgument lowerFound
      have upperSize := termSizePaddedArgument upperFound
      rw [termSizeHeadNode, termSizeHeadNode] at sizeAtMost tagRoom
      have := lengthAtMostArgumentsSize approximantArguments
      have := lengthAtMostArgumentsSize normalArguments
      have := Nat.le_max_left approximantAbstractions normalAbstractions
      have := Nat.le_max_right approximantAbstractions normalAbstractions
      have maximumCases : max approximantAbstractions normalAbstractions = approximantAbstractions ∨
          max approximantAbstractions normalAbstractions = normalAbstractions := by
        rcases Nat.le_total approximantAbstractions normalAbstractions with ordered | ordered
        · exact .inr (Nat.max_eq_right ordered)
        · exact .inl (Nat.max_eq_left ordered)
      unfold RootAgree at agree
      have countAtMost : normalArguments.length + (constants.width - normalAbstractions) ≤
          constants.argumentBound := by omega
      have approximantCountAtMost : truncatedArguments.length +
          (constants.width - approximantAbstractions) ≤ constants.argumentBound := by omega
      have equalCounts : truncatedArguments.length + (constants.width - approximantAbstractions) =
          normalArguments.length + (constants.width - normalAbstractions) := by omega
      have upperBelow : position < normalArguments.length +
          (max approximantAbstractions normalAbstractions - normalAbstractions) := by
        have below : position < (paddedArguments
            (max approximantAbstractions normalAbstractions - normalAbstractions)
            normalArguments).length := by
          rcases Nat.lt_or_ge position (paddedArguments
              (max approximantAbstractions normalAbstractions - normalAbstractions)
              normalArguments).length with inside | outside
          · exact inside
          · rw [List.getElem?_eq_none outside] at upperFound
            exact absurd upperFound (by simp)
        rw [lengthPaddedArguments] at below
        omega
      -- The next layer: the arguments at the chosen position, at the depth of the alignment.
      have upperPair := paddedSubstitutedLookup constants positive (depth := depth)
        (abstractions := normalAbstractions)
        (extra := max approximantAbstractions normalAbstractions - normalAbstractions) (by omega)
        candidateArgumentsFree upperFound
      obtain ⟨truncatedPadded, truncatedPaddedFound, paddedTruncates⟩ :=
        truncatesPadded argumentsTruncate
          (max approximantAbstractions normalAbstractions - approximantAbstractions) lowerFound
      have lowerPair := paddedSubstitutedLookup constants positive (depth := depth)
        (abstractions := approximantAbstractions)
        (extra := max approximantAbstractions normalAbstractions - approximantAbstractions)
        (by omega) truncatedArgumentsFree truncatedPaddedFound
      have upperDepth : depth + normalAbstractions +
          (max approximantAbstractions normalAbstractions - normalAbstractions) =
          depth + max approximantAbstractions normalAbstractions := by omega
      have lowerDepth : depth + approximantAbstractions +
          (max approximantAbstractions normalAbstractions - approximantAbstractions) =
          depth + max approximantAbstractions normalAbstractions := by omega
      rw [upperDepth] at upperPair
      rw [lowerDepth] at lowerPair
      have lowerStratified := stratifiedPaddedArguments approximantArgumentsStratified _
        lowerArgument (List.mem_of_getElem? lowerFound)
      have upperNormal := betaNormalPaddedArguments argumentsNormal _ upperArgument
        (List.mem_of_getElem? upperFound)
      cases upperNormal with
      | headNode nextAbstractions nextHead nextArguments nextArgumentsNormal =>
      have nextSmaller : termSize lowerArgument +
          termSize (headNode nextAbstractions nextHead nextArguments) <
          1 + argumentsSize approximantArguments + approximantAbstractions +
            (1 + argumentsSize normalArguments + normalAbstractions) := by
        rcases lowerSize with lowerSmall | ⟨lowerOne, lowerExtra⟩ <;>
          rcases upperSize with upperSmall | ⟨upperOne, upperExtra⟩ <;> omega
      obtain ⟨nextSigma, nextClosed, nextCandidate, nextApproximant⟩ :=
        inner rfl nextArgumentsNormal
          (normalArguments.length + (constants.width - normalAbstractions) + trailingCount)
          paddedTruncates lowerStratified lowerPair.2 upperPair.2 (by omega)
          (by
            have := tagRoomStep (width := constants.width) nextSmaller
            omega)
      obtain ⟨nextHeadBelow, nextArgumentsFree⟩ := freeBelowHeadNode upperPair.2
      rw [termSizeHeadNode] at nextSmaller
      have := lengthAtMostArgumentsSize nextArguments
      have nextCountAtMost : nextArguments.length + (constants.width - nextAbstractions) ≤
          constants.argumentBound := by omega
      let next := layerPermutators constants (depth + max approximantAbstractions normalAbstractions)
          constants.width ++
        selectorsXi constants (nextArguments.length + (constants.width - nextAbstractions))
          (.parallel nextSigma nextSigma)
      have nextListClosed : AllClosed next :=
        (allClosedLayerPermutators constants positive _ _).append
          (allClosedSelectorsXi constants _ (closedParallel nextClosed nextClosed))
      have positionBelow : position < constants.argumentBound := by omega
      refine ⟨.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
          (argumentComponent constants.argumentBound position next),
        closedParallel (closedConstantComponent _ _)
          (closedArgumentComponent _ _ nextListClosed), ?_, ?_⟩
      · intro trailing trailingClosed trailingLength
        have argumentsClosed := allClosedCandidateArgumentsXi constants positive
          (head := normalHead) candidateArgumentsFree trailingClosed
        have constantK := constantComponentApplyLatticeEta (hypotheses := fun _ _ => False)
          constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount) argumentsClosed
          (by rw [lengthCandidateArgumentsXi constants countAtMost, trailingLength])
        have selectedFound : (projection constants.tagCount
              (depth + normalAbstractions - 1 - normalHead) ::
            (paddedSubstituted constants depth normalAbstractions normalArguments ++
              List.replicate (constants.argumentBound -
                (normalArguments.length + (constants.width - normalAbstractions)))
                (killXi constants.argumentBound)))[position + 1]? =
            some (closeAll 0 (pathSubstitution constants
              (depth + max approximantAbstractions normalAbstractions))
              (headNode nextAbstractions nextHead nextArguments)) := by
          rw [List.getElem?_cons_succ, List.getElem?_append_left (by
            rw [lengthPaddedSubstituted]
            omega)]
          exact upperPair.1
        have selected := argumentComponentApplyLatticeEta (hypotheses := fun _ _ => False)
          constants.argumentBound position positionBelow nextListClosed
          (allClosedCons (closedProjection positive _)
            ((allClosedPaddedSubstituted constants positive candidateArgumentsFree).append
              (allClosedReplicateKillXi constants _)))
          (by simp [lengthPaddedSubstituted]; omega) selectedFound
          (List.replicate (normalArguments.length + (constants.width - normalAbstractions))
            (killXi constants.argumentBound) ++ trailing)
        have nextTrailingClosed := (allClosedReplicateKillXi constants
          (normalArguments.length + (constants.width - normalAbstractions))).append trailingClosed
        have nextHeadApplied := candidateApplyXi constants (hypotheses := fun _ _ => False) positive
          (depth := depth + max approximantAbstractions normalAbstractions)
          (by omega) nextHeadBelow nextArgumentsFree nextCountAtMost
          (closedParallel nextClosed nextClosed)
          (List.replicate (normalArguments.length + (constants.width - normalAbstractions))
            (killXi constants.argumentBound) ++ trailing)
        have nextK := nextCandidate _ nextTrailingClosed (by simp [trailingLength])
        exact .transitive (LatticeEta.parallelApplyAll _ _ _)
          (.transitive (.congruenceParallelLeft _ constantK)
            (.transitive (.congruenceParallelRight _
              (.transitive selected (.transitive nextHeadApplied
                (.transitive (LatticeEta.parallelApplyAll _ _ _)
                  (.transitive (.congruenceParallelLeft _ nextK)
                    (.transitive (.congruenceParallelRight _ nextK) (.parallelIdempotent _)))))))
              (.parallelIdempotent _)))
      · intro other otherClosed trailing trailingClosed trailingLength
        let sigma := Term.parallel (constantComponent constants.argumentBound (normalArguments.length + (constants.width - normalAbstractions) + trailingCount))
          (argumentComponent constants.argumentBound position next)
        have sigmaClosed : Closed sigma := closedParallel (closedConstantComponent _ _)
          (closedArgumentComponent _ _ nextListClosed)
        obtain ⟨found, taken, dropped⟩ := selectorsSelectedXi constants
          (count := normalArguments.length + (constants.width - normalAbstractions))
          (.parallel sigma other)
        have foundAtLeaf : (selectorsXi constants
            (normalArguments.length + (constants.width - normalAbstractions))
            (.parallel sigma other))[constants.argumentBound - (truncatedArguments.length +
              (constants.width - approximantAbstractions))]? = some (.parallel sigma other) := by
          rw [equalCounts]
          exact found
        have applied := headNodeApplyLatticeEta constants (hypotheses := fun _ _ => False) positive
          (by omega) approximantHeadBelow truncatedArgumentsFree approximantCountAtMost
          (allClosedSelectorsXi constants _ (closedParallel sigmaClosed otherClosed))
          (lengthSelectorsXi constants countAtMost _) foundAtLeaf trailing
        rw [equalCounts, taken, dropped] at applied
        have selectedFound : (projection constants.tagCount
              (depth + approximantAbstractions - 1 - approximantHead) ::
            (paddedSubstituted constants depth approximantAbstractions truncatedArguments ++
              List.replicate (constants.argumentBound -
                (normalArguments.length + (constants.width - normalAbstractions)))
                (killXi constants.argumentBound)))[position + 1]? =
            some (closeAll 0 (pathSubstitution constants
              (depth + max approximantAbstractions normalAbstractions)) truncatedPadded) := by
          rw [List.getElem?_cons_succ, List.getElem?_append_left (by
            rw [lengthPaddedSubstituted]
            omega)]
          exact lowerPair.1
        have selected := argumentComponentApplyLatticeEta (hypotheses := fun _ _ => False)
          constants.argumentBound position positionBelow nextListClosed
          (allClosedCons (closedProjection positive _)
            ((allClosedPaddedSubstituted constants positive truncatedArgumentsFree).append
              (allClosedReplicateKillXi constants _)))
          (by simp [lengthPaddedSubstituted]; omega) selectedFound
          (List.replicate (normalArguments.length + (constants.width - normalAbstractions))
            (killXi constants.argumentBound) ++ trailing)
        have nextTrailingClosed := (allClosedReplicateKillXi constants
          (normalArguments.length + (constants.width - normalAbstractions))).append trailingClosed
        have nextZero := nextApproximant nextSigma nextClosed _ nextTrailingClosed
          (by simp [trailingLength])
        have componentRefines := nextZero.ofDerivable selected
        exact ((((componentRefines.parallelRight _).ofDerivable
          (LatticeEta.parallelApplyAll _ _ _)).parallelLeft _).ofDerivable
          (LatticeEta.parallelApplyAll _ _ _)).ofDerivable applied

/-- The first half of section 21's separation, theorem S with Ξ A⃗ where the proofs file has 0: a
closed T′, a stratified truncation A of T′ and a closed βη normal form N with A ⋪ N have closed
arguments X⃗ with ∅ ⊢_{λ-lattice-η} N X⃗ = K and T′ X⃗ refining every closed term. The layer lemma
at the root, with width W = |A| + |N|, r = 2W and V = W² + 1, and Σ ∥ Σ at the root's selector
position. -/
theorem separationLatticeEta {reduct approximant candidate : Term} (reductClosed : Closed reduct)
    (truncates : Truncates approximant reduct) (stratified : Stratified approximant)
    (normal : NormalForm candidate)
    (conflicts : Conflicts approximant candidate) :
    ∃ arguments, AllClosed arguments ∧
      DerivableLatticeEta (fun _ _ => False) (applyAll candidate arguments) first ∧
      LatticeEta.RefinesClosedTerms (applyAll reduct arguments) := by
  have candidateNormal := betaNormalOfNormalForm normal
  cases candidateNormal with
  | headNode abstractions head arguments argumentsNormal =>
  let size := termSize approximant + termSize (headNode abstractions head arguments)
  let constants : SeparationConstants :=
    { argumentBound := size + size, tagCount := size * size + 1, width := size }
  have positive : 0 < constants.tagCount := Nat.succ_pos _
  obtain ⟨sigma, sigmaClosed, candidateSide, approximantSide⟩ :=
    layerSeparationXi constants positive (Nat.le_refl _) conflicts rfl argumentsNormal 0 truncates
      stratified (freeBelowOfClosed reductClosed 0) (freeBelowOfClosed normal.1 0) (Nat.le_refl _)
      (by simp [constants, size])
  obtain ⟨headBelow, argumentsFree⟩ := freeBelowHeadNode (freeBelowOfClosed normal.1 0)
  have sizeFacts := termSizeHeadNode abstractions head arguments
  have := lengthAtMostArgumentsSize arguments
  have countAtMost : arguments.length + (constants.width - abstractions) ≤
      constants.argumentBound := by simp [constants, size]; omega
  refine ⟨layerPermutators constants 0 constants.width ++
      selectorsXi constants (arguments.length + (constants.width - abstractions))
        (.parallel sigma sigma),
    (allClosedLayerPermutators constants positive _ _).append
      (allClosedSelectorsXi constants _ (closedParallel sigmaClosed sigmaClosed)), ?_, ?_⟩
  · have applied := candidateApplyXi constants (hypotheses := fun _ _ => False) positive
      (depth := 0) (by simp [constants, size]; omega) (by omega) argumentsFree countAtMost
      (closedParallel sigmaClosed sigmaClosed) []
    have candidateK := candidateSide [] allClosedNil rfl
    simp only [pathSubstitution, List.range_zero, List.reverse_nil, List.map_nil,
      List.append_nil] at applied
    exact .transitive applied (.transitive (LatticeEta.parallelApplyAll _ _ _)
      (.transitive (.congruenceParallelLeft _ candidateK)
        (.transitive (.congruenceParallelRight _ candidateK) (.parallelIdempotent _))))
  · have reductZero := approximantSide sigma sigmaClosed [] allClosedNil rfl
    simp only [pathSubstitution, List.range_zero, List.reverse_nil, List.map_nil,
      List.append_nil] at reductZero
    exact reductZero

/-! ## The consistency form of NF◇ -/

/-- Section 21's last step: if ∅ ⊢_{λ-lattice-η} T = T′, N X⃗ = K and T′ X⃗ refines every closed
term, then {N + T = T} ⊢_{λ-lattice-η} K = K*. N + T′ = T′ applied to X⃗ gives
K + T′ X⃗ = T′ X⃗ by (8), and `LatticeEta.inconsistentOfChoiceRefines`. -/
theorem inconsistentLatticeEtaOfSeparation {term reduct candidate : Term} {arguments : List Term}
    (equal : DerivableLatticeEta (fun _ _ => False) term reduct)
    (candidateFirst : DerivableLatticeEta (fun _ _ => False) (applyAll candidate arguments) first)
    (reductRefines : LatticeEta.RefinesClosedTerms (applyAll reduct arguments)) :
    ¬ ConsistentEquationLatticeEta (.choice candidate term) term := by
  intro consistent
  apply consistent
  let hypotheses := listed [(.choice candidate term, term)]
  have lift : ∀ {left right : Term}, DerivableLatticeEta (fun _ _ => False) left right →
      DerivableLatticeEta hypotheses left right :=
    DerivableLatticeEta.weaken (fun _ _ impossible => impossible.elim)
  have hypothesis : DerivableLatticeEta hypotheses (.choice candidate term) term :=
    .hypothesis (by simp [hypotheses, listed])
  have onReduct : DerivableLatticeEta hypotheses (.choice candidate reduct) reduct :=
    .transitive (DerivableLatticeEta.congruenceChoiceRight candidate (.symmetric (lift equal)))
      (.transitive hypothesis (lift equal))
  have applied : DerivableLatticeEta hypotheses
      (.choice (applyAll candidate arguments) (applyAll reduct arguments))
      (applyAll reduct arguments) :=
    .transitive (.symmetric (LatticeEta.choiceApplyAll arguments candidate reduct))
      (LatticeEta.congruenceApplyAll arguments onReduct)
  exact LatticeEta.inconsistentOfChoiceRefines reductRefines
    (.transitive (DerivableLatticeEta.congruenceChoiceLeft _ (.symmetric (lift candidateFirst)))
      applied)

namespace DdLP96Model

variable (model : DdLP96Model)

/-- The completeness of DdLP96's reading for NF◇_{λ-lattice-η}, given a model satisfying the fields
of `DdLP96Model`: for a closed T, N ∈ NF◇_{λ-lattice-η}(T) gives [[T]] ⊑ [[N]]. The proofs file's
section 20.5: every projection Pₙ[[T]] is below some approximant A of a T′ (theorem A in
⊢_{λ-lattice-η}); if A ⋪ N, the separation with Ξ makes N + T = T inconsistent in ⊢_{λ-lattice-η};
so A ⋪ N is false and lemma C gives [[A]] ⊑ [[N]]. -/
theorem completenessLatticeEta {term candidate : Term} (closed : Closed term)
    (consistent : ConsistentNormalFormLatticeEta term candidate) :
    model.below (model.interpret term model.topEnvironment)
      (model.interpret candidate model.topEnvironment) := by
  apply model.projectLeast
  intro level
  obtain ⟨reduct, approximant, equal, reductClosed, truncates, stratified, below⟩ :=
    model.approximationLatticeEta term closed level _
      (model.compactProject level _) (model.projectBelow level _)
  rcases Classical.em (Conflicts approximant candidate) with conflicts | fine
  · obtain ⟨_, _, candidateFirst, reductRefines⟩ :=
      separationLatticeEta reductClosed truncates stratified consistent.1 conflicts
    exact absurd consistent.2 (inconsistentLatticeEtaOfSeparation equal candidateFirst reductRefines)
  · exact model.orderTransitive below
      (model.interpretBelowOfNotConflicts _ (Nat.lt_succ_self _) stratified
        (betaNormalOfNormalForm consistent.1) fine _)

end DdLP96Model

end LambdaJit.ContextualPreorder
