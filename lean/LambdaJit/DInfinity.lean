import LambdaJit.DInfinityLevels

/-!
# Wadsworth's D∞ with the two-point D₀: the inverse limit, its order, projections and suprema

D∞ is the inverse limit {(xₙ) | xₙ = ψₙ(x_{n+1})} of the levels of module `DInfinityLevels`
(C. P. Wadsworth, SIAM J. Comput. 5(3), 1976, p. 497), here `Limit`, ordered componentwise. Its
binary meets and joins, ⊤ and ⊥ are taken componentwise (the proofs file,
section 20.1, fact (E1)), and so are its suprema: the supremum of any countable family has as
component k the join, in the finite level k, of the elements below some member's component k
(`supremum`). φ_{n∞} is `embed n`, whose component k is `transfer n k`, and the projection
Pₙ = φ_{n∞} ∘ ψ_{∞n} is `project n`.

Proved here: the lattice laws; Wadsworth's (P1), (P3) and (P4) for `project`; that `project`
preserves meets, joins and ⊤ and maps into {⊥, ⊤} at level 0; the compactness of the elements of
𝔻ₙ, the fixed points of Pₙ (fact (E2), one direction); the list of the elements of 𝔻ₙ; and an
environment that gives every compact element to variables beyond every bound (the proofs file's ρ₀,
section 20.2).
-/

namespace LambdaJit.DInfinity

/-- Wadsworth's D∞ with the two-point D₀: the sequences (xₙ) with xₙ ∈ Dₙ and xₙ = ψₙ(x_{n+1}). -/
def Limit : Type :=
  {sequence : (index : Nat) → (level index).Carrier //
    ∀ index, (transfer (index + 1) index).1 (sequence (index + 1)) = sequence index}

namespace Limit

theorem extensional {left right : Limit} (same : ∀ index, left.1 index = right.1 index) :
    left = right :=
  Subtype.ext (funext same)

/-- A component is the image of every higher component: xₙ = ψ_{m,n}(xₘ) for m ≥ n. -/
theorem coherent (value : Limit) : ∀ (distance target : Nat),
    (transfer (target + distance) target).1 (value.1 (target + distance)) = value.1 target
  | 0, target => transferSame target _
  | distance + 1, target => by
      show (transfer (target + distance + 1) target).1 (value.1 (target + distance + 1)) = _
      rw [← transferCompose (target + distance) (target + distance + 1) target (by omega),
        value.2, coherent value distance]

theorem coherentOfBelow (value : Limit) {source target : Nat} (below : target ≤ source) :
    (transfer source target).1 (value.1 source) = value.1 target := by
  obtain ⟨distance, rfl⟩ : ∃ distance, source = target + distance := ⟨source - target, by omega⟩
  exact value.coherent distance target

/-- The image of a component in any level is below that level's component: ψ_{n,k}(xₙ) = x_k for
k ≤ n, and φ_{n,k}(xₙ) = φ_{n,k}(ψ_{k,n}(x_k)) ⊑ x_k for k > n. -/
theorem transferComponentBelow (value : Limit) (source target : Nat) :
    (level target).below ((transfer source target).1 (value.1 source)) (value.1 target) := by
  rcases Nat.le_total target source with below | above
  · rw [value.coherentOfBelow below]
    exact (level target).orderReflexive _
  · rw [← value.coherentOfBelow above]
    exact transferRoundTrip target source _

/-- The componentwise order of D∞. -/
def below (lower upper : Limit) : Prop :=
  ∀ index, (level index).below (lower.1 index) (upper.1 index)

/-- The componentwise meet. -/
noncomputable def meet (left right : Limit) : Limit :=
  ⟨fun index => (level index).meet (left.1 index) (right.1 index), fun index => by
    rw [transferMeet, left.2, right.2]⟩

/-- The componentwise join. -/
noncomputable def join (left right : Limit) : Limit :=
  ⟨fun index => (level index).join (left.1 index) (right.1 index), fun index => by
    rw [transferJoin, left.2, right.2]⟩

/-- ⊤, componentwise. -/
noncomputable def top : Limit :=
  ⟨fun index => (level index).top, fun index => transferTop (index + 1) index⟩

/-- ⊥, componentwise. -/
noncomputable def bottom : Limit :=
  ⟨fun index => (level index).bottom, fun index => transferBottom (index + 1) index⟩

theorem orderReflexive (value : Limit) : below value value :=
  fun index => (level index).orderReflexive _

theorem orderTransitive {lower middle upper : Limit} (first : below lower middle)
    (second : below middle upper) : below lower upper :=
  fun index => (level index).orderTransitive (first index) (second index)

theorem orderAntisymmetric {left right : Limit} (first : below left right)
    (second : below right left) : left = right :=
  extensional fun index => (level index).orderAntisymmetric (first index) (second index)

/-- φ_{n∞}: the element of D∞ whose component k is φ_{n,k} or ψ_{n,k} of a ∈ Dₙ. -/
noncomputable def embed (source : Nat) (value : (level source).Carrier) : Limit :=
  ⟨fun index => (transfer source index).1 value, fun index =>
    transferCompose (index + 1) source index (by omega) value⟩

/-- Pₙ = φ_{n∞} ∘ ψ_{∞n}. -/
noncomputable def project (level : Nat) (value : Limit) : Limit :=
  embed level (value.1 level)

theorem embedSame (source : Nat) (value : (level source).Carrier) :
    (embed source value).1 source = value :=
  transferSame source value

theorem embedMonotone (source : Nat) {lower upper : (level source).Carrier}
    (below : (level source).below lower upper) : Limit.below (embed source lower) (embed source upper) :=
  fun index => transferMonotone source index below

/-- φ_{m∞} ∘ φ_{n,m} = φ_{n∞} for m ≥ n. -/
theorem embedTransfer {source middle : Nat} (below : source ≤ middle)
    (value : (level source).Carrier) :
    embed middle ((transfer source middle).1 value) = embed source value :=
  extensional fun index => transferCompose middle source index (by omega) value

theorem projectEmbed (projection source : Nat) (value : (level source).Carrier) :
    project projection (embed source value) = embed projection ((transfer source projection).1 value) :=
  rfl

theorem projectMonotone (projection : Nat) {lower upper : Limit} (below : Limit.below lower upper) :
    Limit.below (project projection lower) (project projection upper) :=
  embedMonotone projection (below projection)

/-- (P1) xₙ ⊑ x. -/
theorem projectBelow (projection : Nat) (value : Limit) : below (project projection value) value :=
  fun index => value.transferComponentBelow projection index

/-- (P4) (xₙ)ₘ = x_{min(n, m)}. -/
theorem projectProject (inner outer : Nat) (value : Limit) :
    project outer (project inner value) = project (min inner outer) value := by
  rcases Nat.le_total inner outer with below | above
  · rw [Nat.min_eq_left below]
    exact embedTransfer below _
  · rw [Nat.min_eq_right above]
    show embed outer ((transfer inner outer).1 (value.1 inner)) = _
    rw [value.coherentOfBelow above]
    rfl

/-- Pₙ is idempotent. -/
theorem projectIdempotent (projection : Nat) (value : Limit) :
    project projection (project projection value) = project projection value := by
  rw [projectProject, Nat.min_self]

/-- Pₙ x ⊑ Pₘ x for n ≤ m. -/
theorem projectIndexMonotone {lower upper : Nat} (below : lower ≤ upper) (value : Limit) :
    Limit.below (project lower value) (project upper value) := by
  have same : project lower (project upper value) = project lower value := by
    rw [projectProject, Nat.min_eq_right below]
  rw [← same]
  exact projectBelow lower _

/-- (P1) xₙ ⊑ x_{n+1}. -/
theorem projectIncreasing (projection : Nat) (value : Limit) :
    below (project projection value) (project (projection + 1) value) :=
  projectIndexMonotone (Nat.le_succ projection) value

/-- (P3) every upper bound of the xₙ is above x. -/
theorem projectLeast (value upper : Limit) (bounded : ∀ projection, below (project projection value) upper) :
    below value upper := fun index => by
  have component := bounded index index
  rw [show (project index value).1 index = value.1 index from embedSame index _] at component
  exact component

theorem projectMeet (projection : Nat) (left right : Limit) :
    project projection (meet left right) = meet (project projection left) (project projection right) :=
  extensional fun index => transferMeet projection index _ _

theorem projectJoin (projection : Nat) (left right : Limit) :
    project projection (join left right) = join (project projection left) (project projection right) :=
  extensional fun index => transferJoin projection index _ _

theorem embedTop (source : Nat) : embed source (level source).top = top :=
  extensional fun index => transferTop source index

theorem embedBottom (source : Nat) : embed source (level source).bottom = bottom :=
  extensional fun index => transferBottom source index

theorem embedMeet (source : Nat) (left right : (level source).Carrier) :
    embed source ((level source).meet left right) = meet (embed source left) (embed source right) :=
  extensional fun index => transferMeet source index _ _

theorem embedJoin (source : Nat) (left right : (level source).Carrier) :
    embed source ((level source).join left right) = join (embed source left) (embed source right) :=
  extensional fun index => transferJoin source index _ _

theorem projectTop : project 0 top = top := embedTop 0

/-- (E4) 𝔻₀ = {⊥, ⊤}. -/
theorem projectZeroTwoPoint (value : Limit) : project 0 value = bottom ∨ project 0 value = top := by
  show embed 0 (value.1 0) = bottom ∨ embed 0 (value.1 0) = top
  cases component : value.1 0 with
  | false => exact .inl (embedBottom 0)
  | true => exact .inr (embedTop 0)

theorem topNotBottom : top ≠ bottom := fun equal => by
  have component := congrArg (fun value : Limit => value.1 0) equal
  exact Bool.noConfusion component

/-! ## Suprema of countable families -/

/-- The elements of level `index` below the component `index` of some member of `family`. -/
noncomputable def lowerElements (family : Nat → Limit) (index : Nat) : List (level index).Carrier :=
  (level index).elements.filter fun value =>
    @decide (∃ member, (level index).below value ((family member).1 index)) (Classical.propDecidable _)

theorem memberLowerElements {family : Nat → Limit} {index : Nat} {value : (level index).Carrier} :
    value ∈ lowerElements family index ↔ ∃ member, (level index).below value ((family member).1 index) := by
  unfold lowerElements
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun holds => holds.2, fun holds => ⟨(level index).memberElements _, holds⟩⟩

theorem transferListJoin (source target : Nat) :
    ∀ values : List (level source).Carrier,
      (transfer source target).1 ((level source).listJoin values) =
        (level target).listJoin (values.map (transfer source target).1)
  | [] => transferBottom source target
  | first :: rest => by
      show (transfer source target).1 ((level source).join first ((level source).listJoin rest)) = _
      rw [transferJoin, transferListJoin source target rest]
      rfl

/-- The supremum of a countable family, componentwise. -/
noncomputable def supremum (family : Nat → Limit) : Limit :=
  ⟨fun index => (level index).listJoin (lowerElements family index), fun index => by
    apply (level index).orderAntisymmetric
    · rw [transferListJoin]
      apply (level index).listJoinLeast
      intro value member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨which, originalBelow⟩ := memberLowerElements.mp originalMember
      apply (level index).belowListJoin
      refine memberLowerElements.mpr ⟨which, ?_⟩
      rw [← (family which).2 index]
      exact transferMonotone _ _ originalBelow
    · apply (level index).listJoinLeast
      intro value member
      obtain ⟨which, valueBelow⟩ := memberLowerElements.mp member
      rw [← (family which).2 index] at valueBelow
      exact (level index).orderTransitive valueBelow (transferMonotone _ _
        ((level (index + 1)).belowListJoin (memberLowerElements.mpr
          ⟨which, (level (index + 1)).orderReflexive _⟩)))⟩

theorem supremumAbove (family : Nat → Limit) (member : Nat) : below (family member) (supremum family) :=
  fun index => (level index).belowListJoin
    (memberLowerElements.mpr ⟨member, (level index).orderReflexive _⟩)

theorem supremumLeast {family : Nat → Limit} {upper : Limit}
    (bounded : ∀ member, below (family member) upper) : below (supremum family) upper :=
  fun index => (level index).listJoinLeast fun _ member => by
    obtain ⟨which, valueBelow⟩ := memberLowerElements.mp member
    exact (level index).orderTransitive valueBelow (bounded which index)

theorem supremumMonotone {lower upper : Nat → Limit} (below : ∀ member, Limit.below (lower member) (upper member)) :
    Limit.below (supremum lower) (supremum upper) :=
  supremumLeast fun member => orderTransitive (below member) (supremumAbove upper member)

/-- An increasing family. -/
def Increasing (family : Nat → Limit) : Prop := ∀ member, below (family member) (family (member + 1))

theorem increasingMonotone {family : Nat → Limit} (increasing : Increasing family) :
    ∀ {lower upper : Nat}, lower ≤ upper → below (family lower) (family upper)
  | lower, upper, bound => by
      obtain ⟨distance, rfl⟩ : ∃ distance, upper = lower + distance := ⟨upper - lower, by omega⟩
      clear bound
      induction distance with
      | zero => exact orderReflexive _
      | succ distance inner => exact orderTransitive inner (increasing _)

/-- Finitely many elements each below some member of an increasing family are all below one
member. -/
theorem belowOneMember {family : Nat → Limit} (increasing : Increasing family) (index : Nat) :
    ∀ values : List (level index).Carrier,
      (∀ value ∈ values, ∃ member, (level index).below value ((family member).1 index)) →
        ∃ member, ∀ value ∈ values, (level index).below value ((family member).1 index)
  | [], _ => ⟨0, fun _ absent => nomatch absent⟩
  | first :: rest, each => by
      obtain ⟨firstMember, firstBelow⟩ := each first (.head _)
      obtain ⟨restMember, restBelow⟩ :=
        belowOneMember increasing index rest fun value member => each value (.tail _ member)
      refine ⟨max firstMember restMember, fun value member => ?_⟩
      cases List.mem_cons.mp member with
      | inl isFirst =>
          subst isFirst
          exact (level index).orderTransitive firstBelow
            (increasingMonotone increasing (Nat.le_max_left _ _) index)
      | inr inRest =>
          exact (level index).orderTransitive (restBelow value inRest)
            (increasingMonotone increasing (Nat.le_max_right _ _) index)

/-- Every component of the supremum of an increasing family is attained by a member: the levels
are finite. -/
theorem supremumAttained {family : Nat → Limit} (increasing : Increasing family) (index : Nat) :
    ∃ member, (level index).below ((supremum family).1 index) ((family member).1 index) := by
  obtain ⟨member, each⟩ := belowOneMember increasing index (lowerElements family index)
    fun _ member => memberLowerElements.mp member
  exact ⟨member, (level index).listJoinLeast each⟩

/-- (E2) An element of 𝔻ₙ below the supremum of an increasing family is below one of its members. -/
theorem compact (projection : Nat) (compactValue : Limit) (family : Nat → Limit) (limit : Limit)
    (fixed : project projection compactValue = compactValue) (increasing : Increasing family)
    (least : ∀ upper, (∀ member, below (family member) upper) → below limit upper)
    (compactBelow : below compactValue limit) : ∃ member, below compactValue (family member) := by
  have belowSupremum := orderTransitive compactBelow (least _ (supremumAbove family))
  obtain ⟨member, attained⟩ := supremumAttained increasing projection
  refine ⟨member, ?_⟩
  rw [← fixed]
  exact orderTransitive (embedMonotone projection
      ((level projection).orderTransitive (belowSupremum projection) attained))
    (projectBelow projection _)

/-! ## The finite levels 𝔻ₙ of D∞ and a rich environment -/

/-- The elements of 𝔻ₙ, the image of Dₙ under φ_{n∞}. -/
noncomputable def compactList (projection : Nat) : List Limit :=
  (level projection).elements.map (embed projection)

theorem memberCompactList (projection : Nat) (value : Limit) :
    value ∈ compactList projection ↔ project projection value = value := by
  constructor
  · intro member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    show embed projection ((embed projection original).1 projection) = _
    rw [embedSame]
  · intro fixed
    rw [← fixed]
    exact List.mem_map.mpr ⟨_, (level projection).memberElements _, rfl⟩

/-- One step of the walk along the diagonals of ℕ × ℕ: (a + 1, b) to (a, b + 1), and (0, b) to
(b + 1, 0). -/
def diagonalStep : Nat × Nat → Nat × Nat
  | (0, second) => (second + 1, 0)
  | (first + 1, second) => (first, second + 1)

/-- The walk along the diagonals of ℕ × ℕ from (0, 0). -/
def diagonal : Nat → Nat × Nat
  | 0 => (0, 0)
  | index + 1 => diagonalStep (diagonal index)

/-- The triangular numbers: the index at which the walk starts diagonal `sum`. -/
def triangle : Nat → Nat
  | 0 => 0
  | sum + 1 => triangle sum + sum + 1

theorem diagonalTriangle : ∀ (sum second : Nat), second ≤ sum →
    diagonal (triangle sum + second) = (sum - second, second)
  | 0, 0, _ => rfl
  | 0, _ + 1, bound => absurd bound (by omega)
  | sum + 1, 0, _ => by
      show diagonalStep (diagonal (triangle sum + sum)) = _
      rw [diagonalTriangle sum sum (Nat.le_refl _), Nat.sub_self]
      rfl
  | sum + 1, second + 1, bound => by
      show diagonalStep (diagonal (triangle (sum + 1) + second)) = _
      rw [diagonalTriangle (sum + 1) second (by omega)]
      obtain ⟨rest, equal⟩ : ∃ rest, sum + 1 - second = rest + 1 := ⟨sum - second, by omega⟩
      rw [equal]
      show (rest, second + 1) = _
      congr 1
      omega

/-- Every pair is visited by the walk at an index at or beyond its second coordinate. -/
theorem diagonalVisits (first second : Nat) : ∃ index, second ≤ index ∧ diagonal index = (first, second) :=
  ⟨triangle (first + second) + second, Nat.le_add_left _ _, by
    rw [diagonalTriangle _ _ (Nat.le_add_left _ _), Nat.add_sub_cancel]⟩

/-- The proofs file's ρ₀ (section 20.2): variable i, with the walk at (a, b) and at a at (n, p),
is the p-th element of 𝔻ₙ (⊥ beyond the list's end). -/
noncomputable def richEnvironment (index : Nat) : Limit :=
  ((compactList (diagonal (diagonal index).1).1)[(diagonal (diagonal index).1).2]?).getD bottom

theorem richEnvironmentRich (projection : Nat) (value : Limit) (fixed : project projection value = value)
    (bound : Nat) : ∃ index, bound ≤ index ∧ richEnvironment index = value := by
  obtain ⟨position, inside, isValue⟩ :=
    List.getElem_of_mem ((memberCompactList projection value).mpr fixed)
  obtain ⟨pairIndex, _, pairVisited⟩ := diagonalVisits projection position
  obtain ⟨index, beyond, visited⟩ := diagonalVisits pairIndex bound
  refine ⟨index, beyond, ?_⟩
  unfold richEnvironment
  rw [visited]
  simp only
  rw [pairVisited]
  simp only
  rw [List.getElem?_eq_getElem inside, isValue]
  rfl

end Limit

end LambdaJit.DInfinity
