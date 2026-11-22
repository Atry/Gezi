import LambdaJit.DInfinity

/-!
# Application and abstraction in Wadsworth's D∞

Application is Wadsworth's (P7) taken as the definition: x(y) = ⊔ₙ φ_{n∞}(x_{n+1}(yₙ)), the
supremum of an increasing family (`applicationFamily`), where x_{n+1} ∈ D_{n+1} is a function of
Dₙ. Abstraction maps a monotone function F of D∞ to the element whose component n + 1 is the
function a ↦ F(φ_{n∞}(a))ₙ of Dₙ (`abstraction`); when F is continuous in the sense that every
projection of F(d) is below F of a projection of d (`Continuous`), the abstraction applied to d is
F(d) (`applyAbstraction`).

Proved here, besides: Wadsworth's (P6), (P8), (P11) and (P12) at m = n (`applyProjectFunction`
gives both), the half of (P7) that is not a definition, the facts (E4) and (E5) of
the proofs file, section 20.1, and that application is continuous
(`applyContinuous`).
-/

namespace LambdaJit.DInfinity

namespace Limit

/-- The family whose supremum is x(y): its member n is φ_{n∞}(x_{n+1}(yₙ)). -/
noncomputable def applicationFamily (function argument : Limit) (member : Nat) : Limit :=
  embed member ((function.1 (member + 1)).1 (argument.1 member))

/-- Application in D∞, Wadsworth's (P7): x(y) = ⊔ₙ φ_{n∞}(x_{n+1}(yₙ)). -/
noncomputable def apply (function argument : Limit) : Limit :=
  supremum (applicationFamily function argument)

/-- The component n + 1 of x, as a function of Dₙ, is ψ_{m+1,n+1}(x_{m+1}) for m ≥ n. -/
theorem componentFunction (function : Limit) {lower upper : Nat} (below : lower ≤ upper)
    (argument : (level lower).Carrier) :
    (function.1 (lower + 1)).1 argument =
      (transfer upper lower).1 ((function.1 (upper + 1)).1 ((transfer lower upper).1 argument)) := by
  rw [← function.coherentOfBelow (Nat.succ_le_succ below), transferSuccessorSuccessor]

theorem applicationFamilyIncreasing (function argument : Limit) :
    Increasing (applicationFamily function argument) := fun member => by
  unfold applicationFamily
  rw [← embedTransfer (Nat.le_succ member) ((function.1 (member + 1)).1 (argument.1 member))]
  apply embedMonotone
  rw [componentFunction function (Nat.le_succ member)]
  refine (level (member + 1)).orderTransitive (transferRoundTrip (member + 1) member _) ?_
  apply (function.1 (member + 1 + 1)).2
  rw [← argument.2 member]
  exact transferRoundTrip (member + 1) member _

/-- Application is monotone in the function. -/
theorem applyMonotoneFunction {lower upper : Limit} (below : Limit.below lower upper) (argument : Limit) :
    Limit.below (apply lower argument) (apply upper argument) :=
  supremumMonotone fun member => embedMonotone member (below (member + 1) _)

/-- Application is monotone in the argument. -/
theorem applyMonotoneArgument (function : Limit) {lower upper : Limit} (below : Limit.below lower upper) :
    Limit.below (apply function lower) (apply function upper) :=
  supremumMonotone fun member => embedMonotone member ((function.1 (member + 1)).2 (below member))

/-- (P11) and (P12) at m = n: x_{n+1}(y) = φ_{n∞}(x_{n+1}(yₙ)), an element of 𝔻ₙ that depends on
yₙ only. -/
theorem applyProjectFunction (projection : Nat) (function argument : Limit) :
    apply (project (projection + 1) function) argument =
      embed projection ((function.1 (projection + 1)).1 (argument.1 projection)) := by
  apply orderAntisymmetric
  · apply supremumLeast
    intro member
    show Limit.below (embed member
      (((transfer (projection + 1) (member + 1)).1 (function.1 (projection + 1))).1 (argument.1 member))) _
    rw [transferSuccessorSuccessor]
    refine orderTransitive (embedMonotone member (transferMonotone projection member
      ((function.1 (projection + 1)).2 (argument.transferComponentBelow member projection)))) ?_
    exact projectBelow member (embed projection _)
  · refine orderTransitive ?_ (supremumAbove _ projection)
    show Limit.below _ (embed projection
      (((transfer (projection + 1) (projection + 1)).1 (function.1 (projection + 1))).1
        (argument.1 projection)))
    rw [transferSame]
    exact orderReflexive _

/-- (P12) with m = n: x_{n+1}(y) = x_{n+1}(yₙ). -/
theorem applyProjectArgument (projection : Nat) (function argument : Limit) :
    apply (project (projection + 1) function) argument =
      apply (project (projection + 1) function) (project projection argument) := by
  rw [applyProjectFunction, applyProjectFunction]
  show _ = embed projection ((function.1 (projection + 1)).1
    ((transfer projection projection).1 (argument.1 projection)))
  rw [transferSame]

/-- (P11) with m = n: x_{n+1}(y) = (x_{n+1}(y))ₙ. -/
theorem applyProjectResult (projection : Nat) (function argument : Limit) :
    project projection (apply (project (projection + 1) function) argument) =
      apply (project (projection + 1) function) argument := by
  rw [applyProjectFunction]
  show embed projection ((transfer projection projection).1 _) = _
  rw [transferSame]

/-- (P7), the half that is not the definition: every upper bound of the x_{n+1}(yₙ) is above x(y). -/
theorem applyLeast (function argument upper : Limit)
    (bounded : ∀ projection,
      Limit.below (apply (project (projection + 1) function) (project projection argument)) upper) :
    Limit.below (apply function argument) upper :=
  supremumLeast fun member => by
    have bound := bounded member
    rw [applyProjectFunction] at bound
    show Limit.below (embed member _) upper
    have same : (project member argument).1 member = argument.1 member := embedSame member _
    rw [same] at bound
    exact bound

/-- The component n of x(φ_{n∞}(a)) is x_{n+1}(a). -/
theorem applyEmbedComponent (function : Limit) (projection : Nat) (argument : (level projection).Carrier) :
    (apply function (embed projection argument)).1 projection =
      (function.1 (projection + 1)).1 argument := by
  apply (level projection).orderAntisymmetric
  · apply (level projection).listJoinLeast
    intro value member
    obtain ⟨which, valueBelow⟩ := memberLowerElements.mp member
    refine (level projection).orderTransitive valueBelow ?_
    show (level projection).below ((transfer which projection).1
      ((function.1 (which + 1)).1 ((transfer projection which).1 argument))) _
    rcases Nat.le_total projection which with below | above
    · rw [componentFunction function below]
      exact (level projection).orderReflexive _
    · rw [componentFunction function above]
      refine (level projection).orderTransitive (transferRoundTrip projection which _) ?_
      exact (function.1 (projection + 1)).2 (transferRoundTrip projection which _)
  · have above := supremumAbove (applicationFamily function (embed projection argument)) projection
      projection
    unfold applicationFamily at above
    rw [embedSame, embedSame] at above
    exact above

/-- (P6) extensionality: x ⊑ y if and only if x(z) ⊑ y(z) for every z. -/
theorem extensionalBelow {left right : Limit} :
    Limit.below left right ↔ ∀ argument, Limit.below (apply left argument) (apply right argument) := by
  constructor
  · exact fun below argument => applyMonotoneFunction below argument
  · intro pointwise
    have successor : ∀ projection,
        (level (projection + 1)).below (left.1 (projection + 1)) (right.1 (projection + 1)) :=
      fun projection argument => by
        have component := pointwise (embed projection argument) projection
        rw [applyEmbedComponent, applyEmbedComponent] at component
        exact component
    intro index
    cases index with
    | zero =>
        rw [← left.2 0, ← right.2 0]
        exact transferMonotone 1 0 (successor 0)
    | succ index => exact successor index

/-- (P8) ⊥(y) = ⊥. -/
theorem applyBottom (argument : Limit) : apply bottom argument = bottom :=
  orderAntisymmetric
    (supremumLeast fun member => by
      show Limit.below (embed member (level member).bottom) bottom
      rw [embedBottom]
      exact orderReflexive _)
    (fun index => (level index).bottomLeast _)

/-- (E5) ⊤ y = ⊤. -/
theorem applyTop (argument : Limit) : apply top argument = top :=
  orderAntisymmetric (fun index => (level index).topGreatest _)
    (orderTransitive (by
      show Limit.below top (embed 0 (level 0).top)
      rw [embedTop]
      exact orderReflexive _) (supremumAbove _ 0))

theorem meetBelowLeft (left right : Limit) : Limit.below (meet left right) left :=
  fun index => (level index).meetBelowLeft _ _

theorem meetBelowRight (left right : Limit) : Limit.below (meet left right) right :=
  fun index => (level index).meetBelowRight _ _

theorem meetGreatest {left right lower : Limit} (first : Limit.below lower left)
    (second : Limit.below lower right) : Limit.below lower (meet left right) :=
  fun index => (level index).meetGreatest (first index) (second index)

theorem joinAboveLeft (left right : Limit) : Limit.below left (join left right) :=
  fun index => (level index).joinAboveLeft _ _

theorem joinAboveRight (left right : Limit) : Limit.below right (join left right) :=
  fun index => (level index).joinAboveRight _ _

theorem joinLeast {left right upper : Limit} (first : Limit.below left upper)
    (second : Limit.below right upper) : Limit.below (join left right) upper :=
  fun index => (level index).joinLeast (first index) (second index)

/-- (E5) the meet is pointwise in the function position. -/
theorem applyMeet (left right argument : Limit) :
    apply (meet left right) argument = meet (apply left argument) (apply right argument) := by
  have family : applicationFamily (meet left right) argument =
      fun member => meet (applicationFamily left argument member) (applicationFamily right argument member) :=
    funext fun member => embedMeet member _ _
  apply orderAntisymmetric
  · exact meetGreatest (applyMonotoneFunction (meetBelowLeft _ _) _)
      (applyMonotoneFunction (meetBelowRight _ _) _)
  · intro index
    obtain ⟨leftMember, leftAttained⟩ :=
      supremumAttained (applicationFamilyIncreasing left argument) index
    obtain ⟨rightMember, rightAttained⟩ :=
      supremumAttained (applicationFamilyIncreasing right argument) index
    have bigger : Limit.below
        (meet (applicationFamily left argument (max leftMember rightMember))
          (applicationFamily right argument (max leftMember rightMember)))
        (apply (meet left right) argument) := by
      unfold apply
      rw [family]
      exact supremumAbove (fun member => meet (applicationFamily left argument member)
        (applicationFamily right argument member)) (max leftMember rightMember)
    refine (level index).orderTransitive ?_ (bigger index)
    exact (level index).meetGreatest
      ((level index).orderTransitive ((level index).meetBelowLeft _ _)
        ((level index).orderTransitive leftAttained
          (increasingMonotone (applicationFamilyIncreasing left argument)
            (Nat.le_max_left _ _) index)))
      ((level index).orderTransitive ((level index).meetBelowRight _ _)
        ((level index).orderTransitive rightAttained
          (increasingMonotone (applicationFamilyIncreasing right argument)
            (Nat.le_max_right _ _) index)))

/-- (E5) the join is pointwise in the function position. -/
theorem applyJoin (left right argument : Limit) :
    apply (join left right) argument = join (apply left argument) (apply right argument) := by
  have family : applicationFamily (join left right) argument =
      fun member => join (applicationFamily left argument member) (applicationFamily right argument member) :=
    funext fun member => embedJoin member _ _
  apply orderAntisymmetric
  · unfold apply
    rw [family]
    exact supremumLeast fun member => joinLeast
      (orderTransitive (supremumAbove _ member) (joinAboveLeft _ _))
      (orderTransitive (supremumAbove _ member) (joinAboveRight _ _))
  · exact joinLeast (applyMonotoneFunction (joinAboveLeft _ _) _)
      (applyMonotoneFunction (joinAboveRight _ _) _)

/-- (E4), the direction used: x(⊥) = ⊤ gives x = ⊤. -/
theorem topOfApplyBottom (value : Limit) (isTop : apply value bottom = top) : value = top := by
  obtain ⟨member, attained⟩ :=
    supremumAttained (applicationFamilyIncreasing value bottom) 0
  have componentTop : (transfer member 0).1 ((value.1 (member + 1)).1 (level member).bottom) =
      (level 0).top := by
    apply (level 0).orderAntisymmetric ((level 0).topGreatest _)
    have topBelow : (level 0).below (level 0).top ((supremum (applicationFamily value bottom)).1 0) := by
      show (level 0).below _ ((apply value bottom).1 0)
      rw [isTop]
      exact (level 0).orderReflexive _
    exact (level 0).orderTransitive topBelow attained
  have bottomTop := transferZeroTopReflect member _ componentTop
  have functionTop : value.1 (member + 1) = (level (member + 1)).top :=
    functionExtensional fun argument => (level member).orderAntisymmetric
      ((level member).topGreatest _)
      (by
        show (level member).below (level member).top _
        rw [← bottomTop]
        exact (value.1 (member + 1)).2 ((level member).bottomLeast argument))
  have projectTop : project (member + 1) value = top := by
    show embed (member + 1) (value.1 (member + 1)) = top
    rw [functionTop, embedTop]
  apply orderAntisymmetric (fun index => (level index).topGreatest _)
  rw [← projectTop]
  exact projectBelow _ _

/-- Application is continuous: every projection of x(y) is below x′(y′) for projections x′, y′ of
x and y. -/
theorem applyContinuous (function argument : Limit) (projection : Nat) :
    ∃ approximation, Limit.below (project projection (apply function argument))
      (apply (project approximation function) (project approximation argument)) := by
  obtain ⟨member, below⟩ := compact projection (project projection (apply function argument))
    (applicationFamily function argument) (apply function argument) (projectIdempotent _ _)
    (applicationFamilyIncreasing function argument) (fun _ bounded => supremumLeast bounded)
    (projectBelow _ _)
  refine ⟨member + 1, orderTransitive below ?_⟩
  rw [applyProjectFunction]
  show Limit.below (embed member _) (embed member ((function.1 (member + 1)).1
    ((transfer (member + 1) member).1 (argument.1 (member + 1)))))
  rw [argument.2 member]
  exact orderReflexive _

/-! ## Abstraction -/

/-- A monotone function of D∞. -/
def Monotone (function : Limit → Limit) : Prop :=
  ∀ {lower upper}, Limit.below lower upper → Limit.below (function lower) (function upper)

/-- A continuous function of D∞, in the form used here: every projection of F(d) is below F of
some projection of d. With monotonicity this is Scott continuity on D∞. -/
def Continuous (function : Limit → Limit) : Prop :=
  ∀ value projection, ∃ approximation,
    Limit.below (project projection (function value)) (function (project approximation value))

/-- The components of the abstraction of a monotone F: component n + 1 is a ↦ F(φ_{n∞}(a))ₙ. -/
noncomputable def abstractionComponent (function : Limit → Limit) (monotone : Monotone function) :
    (index : Nat) → (level index).Carrier
  | 0 => (function (embed 0 (level 0).bottom)).1 0
  | index + 1 => ⟨fun argument => (function (embed index argument)).1 index,
      fun below => monotone (embedMonotone index below) index⟩

/-- The abstraction of a monotone function of D∞. -/
noncomputable def abstraction (function : Limit → Limit) (monotone : Monotone function) : Limit :=
  ⟨abstractionComponent function monotone, fun index => by
    cases index with
    | zero =>
        show (transfer 1 0).1 (abstractionComponent function monotone 1) = _
        rw [transferSuccessorZero, transferZeroZero]
        rfl
    | succ index =>
        apply functionExtensional
        intro argument
        rw [transferSuccessorSuccessor]
        show (transfer (index + 1) index).1
          ((function (embed (index + 1) ((transfer index (index + 1)).1 argument))).1 (index + 1)) =
            (function (embed index argument)).1 index
        rw [embedTransfer (Nat.le_succ index)]
        exact (function (embed index argument)).2 index⟩

theorem applicationFamilyAbstraction (function : Limit → Limit) (monotone : Monotone function)
    (argument : Limit) (member : Nat) :
    applicationFamily (abstraction function monotone) argument member =
      project member (function (project member argument)) :=
  rfl

/-- The abstraction of a monotone, continuous F applied to d is F(d). -/
theorem applyAbstraction (function : Limit → Limit) (monotone : Monotone function)
    (continuous : Continuous function) (argument : Limit) :
    apply (abstraction function monotone) argument = function argument := by
  apply orderAntisymmetric
  · apply supremumLeast
    intro member
    rw [applicationFamilyAbstraction]
    exact orderTransitive (projectBelow _ _) (monotone (projectBelow _ _))
  · apply projectLeast
    intro projection
    obtain ⟨approximation, below⟩ := continuous argument projection
    have bigger : Limit.below (project projection (function (project approximation argument)))
        (project (max projection approximation)
          (function (project (max projection approximation) argument))) :=
      orderTransitive (projectIndexMonotone (Nat.le_max_left _ _) _)
        (projectMonotone _ (monotone (projectIndexMonotone (Nat.le_max_right _ _) _)))
    rw [← projectIdempotent]
    refine orderTransitive (projectMonotone projection below) (orderTransitive bigger ?_)
    rw [← applicationFamilyAbstraction function monotone]
    exact supremumAbove _ _

/-- The abstraction is monotone in the function, pointwise. -/
theorem abstractionMonotone {lower upper : Limit → Limit} {lowerMonotone : Monotone lower}
    {upperMonotone : Monotone upper} (below : ∀ value, Limit.below (lower value) (upper value)) :
    Limit.below (abstraction lower lowerMonotone) (abstraction upper upperMonotone) := by
  intro index
  cases index with
  | zero => exact below _ 0
  | succ index => exact fun argument => below _ index

end Limit

end LambdaJit.DInfinity
