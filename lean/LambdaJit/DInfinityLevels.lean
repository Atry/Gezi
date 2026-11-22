/-!
# The finite levels Dₙ of Wadsworth's D∞ with the two-point D₀

C. P. Wadsworth, The relation between computational and denotational properties for Scott's
D∞-models of the lambda-calculus, SIAM J. Comput. 5(3), 1976, p. 497: D₀ is a complete lattice,
D_{n+1} = [Dₙ → Dₙ], φ₀(x) = λy. x, ψ₀(x′) = x′(⊥), φ_{n+1}(x) = φₙ ∘ x ∘ ψₙ and
ψ_{n+1}(x′) = ψₙ ∘ x′ ∘ φₙ. Here D₀ is the two-point lattice (`twoPoint`), as in
the proofs file, section 20.1, so every Dₙ is finite, and the
continuous functions of a finite lattice are its monotone functions: D_{n+1} is the lattice of the
monotone functions of Dₙ under the pointwise order (`monotoneFunctions`).

This module builds the levels as finite distributive lattices with a list of all their elements
(`FiniteLattice`, the proofs file's fact (E1)), and Wadsworth's maps between any two levels,
`transfer source target`: the composite of the φ's from a lower level to a higher one and of the
ψ's from a higher level to a lower one (φ_{n,m} and ψ_{n,m} in Wadsworth's notation). It is defined
by one recursion on both levels, `transfer (n + 1) (m + 1) f = transfer n m ∘ f ∘ transfer m n`,
which for m = n + 1 and m + 1 = n is Wadsworth's φ_{n+1} and ψ_{n+1}. The facts proved: every
`transfer` preserves the lattice operations; going through a level at or above the lower of the two
ends loses nothing (`transferCompose`); a round trip is below the identity (`transferRoundTrip`,
Wadsworth's φₙ ∘ ψₙ ⊑ id); and a map to level 0 reflects ⊤ (`transferZeroTopReflect`).
-/

namespace LambdaJit.DInfinity

/-- A finite distributive lattice with ⊤ and ⊥, together with a list holding all its elements. -/
structure FiniteLattice where
  /-- The elements. -/
  Carrier : Type
  /-- The order. -/
  below : Carrier → Carrier → Prop
  /-- The binary meet. -/
  meet : Carrier → Carrier → Carrier
  /-- The binary join. -/
  join : Carrier → Carrier → Carrier
  /-- The greatest element. -/
  top : Carrier
  /-- The least element. -/
  bottom : Carrier
  orderReflexive : ∀ value, below value value
  orderTransitive : ∀ {lower middle upper}, below lower middle → below middle upper →
    below lower upper
  orderAntisymmetric : ∀ {left right}, below left right → below right left → left = right
  meetBelowLeft : ∀ left right, below (meet left right) left
  meetBelowRight : ∀ left right, below (meet left right) right
  meetGreatest : ∀ {left right lower}, below lower left → below lower right →
    below lower (meet left right)
  joinAboveLeft : ∀ left right, below left (join left right)
  joinAboveRight : ∀ left right, below right (join left right)
  joinLeast : ∀ {left right upper}, below left upper → below right upper →
    below (join left right) upper
  topGreatest : ∀ value, below value top
  bottomLeast : ∀ value, below bottom value
  distributive : ∀ value left right,
    below (meet value (join left right)) (join (meet value left) (meet value right))
  /-- A list of the elements. -/
  elements : List Carrier
  /-- Every element is in the list. -/
  memberElements : ∀ value, value ∈ elements

/-- The two-point lattice {⊥ < ⊤}, D₀. -/
def twoPoint : FiniteLattice where
  Carrier := Bool
  below lower upper := lower = true → upper = true
  meet := and
  join := or
  top := true
  bottom := false
  orderReflexive _ := id
  orderTransitive first second := fun holds => second (first holds)
  orderAntisymmetric {left right} first second := by
    cases left <;> cases right <;> simp_all
  meetBelowLeft left right := by cases left <;> cases right <;> simp
  meetBelowRight left right := by cases left <;> cases right <;> simp
  meetGreatest {left right lower} first second := by
    cases left <;> cases right <;> cases lower <;> simp_all
  joinAboveLeft left right := by cases left <;> cases right <;> simp
  joinAboveRight left right := by cases left <;> cases right <;> simp
  joinLeast {left right upper} first second := by
    cases left <;> cases right <;> cases upper <;> simp_all
  topGreatest _ := fun _ => rfl
  bottomLeast _ := fun holds => nomatch holds
  distributive value left right := by
    cases value <;> cases left <;> cases right <;> simp
  elements := [false, true]
  memberElements value := by cases value <;> simp

/-- For a type whose elements are all in the list `domain`, and a list `codomain` of all the
elements of another type, a list of functions that agrees on `domain` with every function. -/
theorem functionListExists {Domain Codomain : Type} (default : Codomain) (codomain : List Codomain)
    (memberCodomain : ∀ value, value ∈ codomain) :
    ∀ domain : List Domain, ∃ functions : List (Domain → Codomain),
      ∀ function : Domain → Codomain, ∃ listed ∈ functions,
        ∀ argument ∈ domain, listed argument = function argument
  | [] => ⟨[fun _ => default], fun _ => ⟨_, List.mem_singleton.mpr rfl, fun _ absent => nomatch absent⟩⟩
  | first :: rest => by
      classical
      obtain ⟨functions, complete⟩ := functionListExists default codomain memberCodomain rest
      refine ⟨functions.flatMap fun listed => codomain.map fun value =>
        fun argument => if argument = first then value else listed argument, ?_⟩
      intro function
      obtain ⟨listed, member, agrees⟩ := complete function
      refine ⟨fun argument => if argument = first then function first else listed argument,
        List.mem_flatMap.mpr ⟨listed, member, List.mem_map.mpr ⟨_, memberCodomain _, rfl⟩⟩, ?_⟩
      intro argument inList
      by_cases equal : argument = first
      · subst equal
        simp
      · simp only [equal, ite_false]
        cases List.mem_cons.mp inList with
        | inl isFirst => exact absurd isFirst equal
        | inr inRest => exact agrees argument inRest

/-- The monotone functions of a finite lattice under the pointwise order: D_{n+1} from Dₙ. -/
noncomputable def monotoneFunctions (lattice : FiniteLattice) : FiniteLattice where
  Carrier := {function : lattice.Carrier → lattice.Carrier //
    ∀ {lower upper}, lattice.below lower upper → lattice.below (function lower) (function upper)}
  below lower upper := ∀ argument, lattice.below (lower.1 argument) (upper.1 argument)
  meet left right := ⟨fun argument => lattice.meet (left.1 argument) (right.1 argument),
    fun below => lattice.meetGreatest
      (lattice.orderTransitive (lattice.meetBelowLeft _ _) (left.2 below))
      (lattice.orderTransitive (lattice.meetBelowRight _ _) (right.2 below))⟩
  join left right := ⟨fun argument => lattice.join (left.1 argument) (right.1 argument),
    fun below => lattice.joinLeast
      (lattice.orderTransitive (left.2 below) (lattice.joinAboveLeft _ _))
      (lattice.orderTransitive (right.2 below) (lattice.joinAboveRight _ _))⟩
  top := ⟨fun _ => lattice.top, fun _ => lattice.orderReflexive _⟩
  bottom := ⟨fun _ => lattice.bottom, fun _ => lattice.orderReflexive _⟩
  orderReflexive _ _ := lattice.orderReflexive _
  orderTransitive first second argument := lattice.orderTransitive (first argument) (second argument)
  orderAntisymmetric first second :=
    Subtype.ext (funext fun argument => lattice.orderAntisymmetric (first argument) (second argument))
  meetBelowLeft _ _ _ := lattice.meetBelowLeft _ _
  meetBelowRight _ _ _ := lattice.meetBelowRight _ _
  meetGreatest first second argument := lattice.meetGreatest (first argument) (second argument)
  joinAboveLeft _ _ _ := lattice.joinAboveLeft _ _
  joinAboveRight _ _ _ := lattice.joinAboveRight _ _
  joinLeast first second argument := lattice.joinLeast (first argument) (second argument)
  topGreatest _ _ := lattice.topGreatest _
  bottomLeast _ _ := lattice.bottomLeast _
  distributive _ _ _ _ := lattice.distributive _ _ _
  elements :=
    have := Classical.propDecidable
    (Classical.choose (functionListExists lattice.bottom lattice.elements lattice.memberElements
      lattice.elements)).filterMap fun function =>
        if monotone : ∀ {lower upper}, lattice.below lower upper →
            lattice.below (function lower) (function upper) then
          some ⟨function, monotone⟩
        else none
  memberElements value := by
    have := Classical.propDecidable
    obtain ⟨listed, member, agrees⟩ :=
      Classical.choose_spec (functionListExists lattice.bottom lattice.elements
        lattice.memberElements lattice.elements) value.1
    have same : listed = value.1 := funext fun argument => agrees argument (lattice.memberElements _)
    subst same
    refine List.mem_filterMap.mpr ⟨_, member, ?_⟩
    split
    · rfl
    · next notMonotone => exact absurd (fun {_ _} below => value.2 below) notMonotone

/-- The level Dₙ. -/
noncomputable def level : Nat → FiniteLattice
  | 0 => twoPoint
  | index + 1 => monotoneFunctions (level index)

/-- A monotone map from level `source` to level `target`. -/
abbrev MonotoneMap (source target : Nat) : Type :=
  {map : (level source).Carrier → (level target).Carrier //
    ∀ {lower upper}, (level source).below lower upper →
      (level target).below (map lower) (map upper)}

/-- Two elements of a level of functions with the same values are equal. -/
theorem functionExtensional {index : Nat} {left right : (level (index + 1)).Carrier}
    (same : ∀ argument, left.1 argument = right.1 argument) : left = right :=
  Subtype.ext (funext same)

/-- Wadsworth's maps between levels: φ_{n,m} from a lower level n to a higher level m, ψ_{n,m}
from a higher one to a lower one, the identity from a level to itself. -/
noncomputable def transfer : (source target : Nat) → MonotoneMap source target
  | 0, 0 => ⟨fun value => value, fun below => below⟩
  | 0, target + 1 => ⟨fun value => ⟨fun _ => (transfer 0 target).1 value,
      fun _ => (level target).orderReflexive _⟩, fun below _ => (transfer 0 target).2 below⟩
  | source + 1, 0 => ⟨fun function => (transfer source 0).1 (function.1 (level source).bottom),
      fun below => (transfer source 0).2 (below _)⟩
  | source + 1, target + 1 => ⟨fun function =>
      ⟨fun argument => (transfer source target).1 (function.1 ((transfer target source).1 argument)),
        fun below => (transfer source target).2 (function.2 ((transfer target source).2 below))⟩,
      fun below _ => (transfer source target).2 (below _)⟩
termination_by source target => source + target

theorem transferZeroZero (value : (level 0).Carrier) : (transfer 0 0).1 value = value := by
  rw [transfer]

theorem transferZeroSuccessor (target : Nat) (value : (level 0).Carrier)
    (argument : (level target).Carrier) :
    ((transfer 0 (target + 1)).1 value).1 argument = (transfer 0 target).1 value := by
  rw [transfer]

theorem transferSuccessorZero (source : Nat) (function : (level (source + 1)).Carrier) :
    (transfer (source + 1) 0).1 function = (transfer source 0).1 (function.1 (level source).bottom) := by
  rw [transfer]

theorem transferSuccessorSuccessor (source target : Nat) (function : (level (source + 1)).Carrier)
    (argument : (level target).Carrier) :
    ((transfer (source + 1) (target + 1)).1 function).1 argument =
      (transfer source target).1 (function.1 ((transfer target source).1 argument)) := by
  rw [transfer]

theorem transferMonotone (source target : Nat) {lower upper : (level source).Carrier}
    (below : (level source).below lower upper) :
    (level target).below ((transfer source target).1 lower) ((transfer source target).1 upper) :=
  (transfer source target).2 below

/-- The identity: `transfer n n` is the identity of level n. -/
theorem transferSame : ∀ (index : Nat) (value : (level index).Carrier),
    (transfer index index).1 value = value
  | 0, value => transferZeroZero value
  | index + 1, function => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor, transferSame index, transferSame index]

/-- `transfer` preserves ⊥. -/
theorem transferBottom : ∀ (source target : Nat),
    (transfer source target).1 (level source).bottom = (level target).bottom
  | 0, 0 => transferZeroZero _
  | 0, target + 1 => functionExtensional fun argument => by
      rw [transferZeroSuccessor, transferBottom 0 target]
      rfl
  | source + 1, 0 => by
      rw [transferSuccessorZero]
      exact transferBottom source 0
  | source + 1, target + 1 => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor]
      exact transferBottom source target
termination_by source target => source + target

/-- `transfer` preserves ⊤. -/
theorem transferTop : ∀ (source target : Nat),
    (transfer source target).1 (level source).top = (level target).top
  | 0, 0 => transferZeroZero _
  | 0, target + 1 => functionExtensional fun argument => by
      rw [transferZeroSuccessor, transferTop 0 target]
      rfl
  | source + 1, 0 => by
      rw [transferSuccessorZero]
      exact transferTop source 0
  | source + 1, target + 1 => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor]
      exact transferTop source target
termination_by source target => source + target

/-- `transfer` preserves binary meets. -/
theorem transferMeet : ∀ (source target : Nat) (left right : (level source).Carrier),
    (transfer source target).1 ((level source).meet left right) =
      (level target).meet ((transfer source target).1 left) ((transfer source target).1 right)
  | 0, 0, left, right => by rw [transferZeroZero, transferZeroZero, transferZeroZero]
  | 0, target + 1, left, right => functionExtensional fun argument => by
      rw [transferZeroSuccessor, transferMeet 0 target]
      show _ = (level target).meet (((transfer 0 (target + 1)).1 left).1 argument)
        (((transfer 0 (target + 1)).1 right).1 argument)
      rw [transferZeroSuccessor, transferZeroSuccessor]
  | source + 1, 0, left, right => by
      rw [transferSuccessorZero, transferSuccessorZero, transferSuccessorZero]
      exact transferMeet source 0 _ _
  | source + 1, target + 1, left, right => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor]
      show (transfer source target).1 ((level source).meet _ _) =
        (level target).meet (((transfer (source + 1) (target + 1)).1 left).1 argument)
          (((transfer (source + 1) (target + 1)).1 right).1 argument)
      rw [transferMeet source target, transferSuccessorSuccessor, transferSuccessorSuccessor]
termination_by source target => source + target

/-- `transfer` preserves binary joins. -/
theorem transferJoin : ∀ (source target : Nat) (left right : (level source).Carrier),
    (transfer source target).1 ((level source).join left right) =
      (level target).join ((transfer source target).1 left) ((transfer source target).1 right)
  | 0, 0, left, right => by rw [transferZeroZero, transferZeroZero, transferZeroZero]
  | 0, target + 1, left, right => functionExtensional fun argument => by
      rw [transferZeroSuccessor, transferJoin 0 target]
      show _ = (level target).join (((transfer 0 (target + 1)).1 left).1 argument)
        (((transfer 0 (target + 1)).1 right).1 argument)
      rw [transferZeroSuccessor, transferZeroSuccessor]
  | source + 1, 0, left, right => by
      rw [transferSuccessorZero, transferSuccessorZero, transferSuccessorZero]
      exact transferJoin source 0 _ _
  | source + 1, target + 1, left, right => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor]
      show (transfer source target).1 ((level source).join _ _) =
        (level target).join (((transfer (source + 1) (target + 1)).1 left).1 argument)
          (((transfer (source + 1) (target + 1)).1 right).1 argument)
      rw [transferJoin source target, transferSuccessorSuccessor, transferSuccessorSuccessor]
termination_by source target => source + target

/-- Going from `source` to `target` through a level `middle` at or above the lower of the two ends
is going directly: Wadsworth's φ_{m,k} ∘ φ_{n,m} = φ_{n,k}, ψ_{m,k} ∘ ψ_{n,m} = ψ_{n,k}, and
ψ_{m,k} ∘ φ_{n,m} = φ_{n,k} or ψ_{n,k}, by ψₙ ∘ φₙ = id. -/
theorem transferCompose : ∀ (middle source target : Nat), min source target ≤ middle →
    ∀ value : (level source).Carrier,
      (transfer middle target).1 ((transfer source middle).1 value) = (transfer source target).1 value
  | 0, 0, target, _, value => by rw [transferZeroZero]
  | 0, source + 1, 0, _, value => by rw [transferZeroZero]
  | 0, source + 1, target + 1, bound, _ => absurd bound (by omega)
  | middle + 1, 0, 0, _, value => by
      rw [transferSuccessorZero, transferZeroSuccessor, transferCompose middle 0 0 (by omega)]
  | middle + 1, 0, target + 1, _, value => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor, transferZeroSuccessor, transferZeroSuccessor,
        transferCompose middle 0 target (by omega)]
  | middle + 1, source + 1, 0, _, function => by
      rw [transferSuccessorZero, transferSuccessorSuccessor, transferBottom,
        transferCompose middle source 0 (by omega), transferSuccessorZero]
  | middle + 1, source + 1, target + 1, bound, function => functionExtensional fun argument => by
      rw [transferSuccessorSuccessor, transferSuccessorSuccessor,
        transferCompose middle source target (by omega),
        transferCompose middle target source (by omega), transferSuccessorSuccessor]

/-- A round trip is below the identity: Wadsworth's φₙ ∘ ψₙ ⊑ id, for any two levels. -/
theorem transferRoundTrip : ∀ (source target : Nat) (value : (level source).Carrier),
    (level source).below ((transfer target source).1 ((transfer source target).1 value)) value
  | 0, 0, value => by
      rw [transferZeroZero, transferZeroZero]
      exact (level 0).orderReflexive _
  | 0, target + 1, value => by
      rw [transferSuccessorZero, transferZeroSuccessor]
      exact transferRoundTrip 0 target value
  | source + 1, 0, function => fun argument => by
      rw [transferZeroSuccessor, transferSuccessorZero]
      exact (level source).orderTransitive (transferRoundTrip source 0 _)
        (function.2 ((level source).bottomLeast argument))
  | source + 1, target + 1, function => fun argument => by
      rw [transferSuccessorSuccessor, transferSuccessorSuccessor]
      exact (level source).orderTransitive (transferRoundTrip source target _)
        (function.2 (transferRoundTrip source target argument))
termination_by source target => source + target

/-- The map to level 0 reflects ⊤: an element of Dₙ whose image in D₀ is ⊤ is ⊤. -/
theorem transferZeroTopReflect : ∀ (source : Nat) (value : (level source).Carrier),
    (transfer source 0).1 value = (level 0).top → value = (level source).top
  | 0, value, isTop => by rw [transferZeroZero] at isTop; exact isTop
  | source + 1, function, isTop => by
      rw [transferSuccessorZero] at isTop
      have bottomTop := transferZeroTopReflect source _ isTop
      exact functionExtensional fun argument => (level source).orderAntisymmetric
        ((level source).topGreatest _)
        (by
          show (level source).below (level source).top _
          rw [← bottomTop]
          exact function.2 ((level source).bottomLeast argument))

/-! ## Joins of lists -/

/-- The join of a list of elements of a finite lattice. -/
def FiniteLattice.listJoin (lattice : FiniteLattice) (values : List lattice.Carrier) :
    lattice.Carrier :=
  values.foldr lattice.join lattice.bottom

theorem FiniteLattice.belowListJoin (lattice : FiniteLattice) :
    ∀ {values : List lattice.Carrier} {value}, value ∈ values →
      lattice.below value (lattice.listJoin values)
  | _ :: _, _, .head _ => lattice.joinAboveLeft _ _
  | _ :: _, _, .tail _ member =>
      lattice.orderTransitive (lattice.belowListJoin member) (lattice.joinAboveRight _ _)

theorem FiniteLattice.listJoinLeast (lattice : FiniteLattice) {upper : lattice.Carrier} :
    ∀ {values : List lattice.Carrier}, (∀ value ∈ values, lattice.below value upper) →
      lattice.below (lattice.listJoin values) upper
  | [], _ => lattice.bottomLeast _
  | _ :: _, bounded => lattice.joinLeast (bounded _ (.head _))
      (lattice.listJoinLeast fun value member => bounded value (.tail _ member))

end LambdaJit.DInfinity
