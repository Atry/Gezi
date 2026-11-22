import LambdaJit.DInfinityModel
import LambdaJit.ParallelTypesTheorems

/-!
# Least fixed points in Wadsworth's D∞, and the reading of Turing's fixed point combinator

`leastFixedPoint f` is the supremum of the iterates fⁱ(⊥) of an element f of D∞ read as a function
by application. It is a fixed point of f (`applyLeastFixedPoint`), below every prefixed point
(`leastFixedPointBelow`), monotone in f (`leastFixedPointMonotone`), and an element compact
below it is below one iterate (`compactBelowIterate`), which is the form of fixed-point induction
used in module `StaticArgumentFixpoint`.

Park's theorem (`halvesApply`): for an element a that applies as A = λx.λf. f (x x f) does,
a a f = `leastFixedPoint f`. Its instances: the reading of Turing's combinator Θ = A A
(`ParallelTypesTheorems.fixpoint`, `interpretFixpointApply`) and of the by-value combinator
Θ′ = A′ A′, A′ = λx.λf. f (λv. x x f v) (`interpretFixpointByValueApply`), under every
environment. The direction ⊑ is Park's argument by
projections (Barendregt 1984, chapter 19, for Curry's Y): writing aₙ for the projection of the
reading a of A to 𝔻ₙ, x_{k+1}(y) ⊑ (x(y_k))_k gives a_{k+2} a_{k+2} f ⊑ f (a_{k+1} a_{k+1} f_k), so
that aₙ aₙ f ⊑ lfp f by induction on n; D₀ is two-point, and the projections of a and of a a₀ to
𝔻₀ are ⊥ because they do not read ⊤ on ⊥. Continuity of application then gives a a f ⊑ lfp f.
The direction ⊒ holds because a a f = f (a a f) by the β rule.

These are facts of the model, a bridge to Definition 14 (`DdLP96Model.contextualEquivalenceOfInterpretEqual`);
the model does not define the semantics.
-/

namespace LambdaJit.DInfinity

namespace Limit

open LambdaJit.Semantics
open LambdaJit.ContextualPreorder (extendEnvironment)

theorem bottomLeast (value : Limit) : below bottom value :=
  fun index => (level index).bottomLeast _

theorem equalBelow {left right : Limit} (equal : left = right) : below left right := by
  rw [equal]
  exact orderReflexive _

/-- Application is monotone in both of its places. -/
theorem applyMonotone {lowerFunction upperFunction lowerArgument upperArgument : Limit}
    (functionBelow : below lowerFunction upperFunction) (argumentBelow : below lowerArgument upperArgument) :
    below (apply lowerFunction lowerArgument) (apply upperFunction upperArgument) :=
  orderTransitive (applyMonotoneFunction functionBelow _) (applyMonotoneArgument _ argumentBelow)

/-! ## Least fixed points -/

/-- The iterates fⁱ(⊥) of f. -/
noncomputable def iterate (function : Limit) : Nat → Limit
  | 0 => bottom
  | count + 1 => apply function (iterate function count)

theorem iterateIncreasing (function : Limit) : Increasing (iterate function) := by
  intro count
  induction count with
  | zero => exact bottomLeast _
  | succ count below => exact applyMonotoneArgument function below

/-- The least fixed point of f, the supremum of its iterates. -/
noncomputable def leastFixedPoint (function : Limit) : Limit :=
  supremum (iterate function)

/-- The least fixed point is below every prefixed point. -/
theorem leastFixedPointBelow {function value : Limit} (prefixed : below (apply function value) value) :
    below (leastFixedPoint function) value := by
  apply supremumLeast
  intro count
  induction count with
  | zero => exact bottomLeast _
  | succ count below => exact orderTransitive (applyMonotoneArgument function below) prefixed

/-- An element of 𝔻ₙ below the least fixed point is below one of the iterates. -/
theorem compactBelowIterate {function compactValue : Limit} (projection : Nat)
    (fixed : project projection compactValue = compactValue)
    (compactBelow : below compactValue (leastFixedPoint function)) :
    ∃ count, below compactValue (iterate function count) :=
  compact projection compactValue (iterate function) (leastFixedPoint function) fixed
    (iterateIncreasing function) (fun _ bounded => supremumLeast bounded) compactBelow

/-- Every projection of the least fixed point is below one iterate. -/
theorem projectBelowIterate (function : Limit) (projection : Nat) :
    ∃ count, below (project projection (leastFixedPoint function)) (iterate function count) :=
  compactBelowIterate projection (projectIdempotent _ _) (projectBelow _ _)

/-- f(lfp f) ⊑ lfp f, by continuity of application: every projection of f(lfp f) is below
f′(x) for a projection x of lfp f, and x is below one iterate. -/
theorem applyLeastFixedPointBelow (function : Limit) :
    below (apply function (leastFixedPoint function)) (leastFixedPoint function) := by
  apply projectLeast
  intro projection
  obtain ⟨approximation, continuous⟩ :=
    applyContinuous function (leastFixedPoint function) projection
  obtain ⟨count, belowIterate⟩ := projectBelowIterate function approximation
  refine orderTransitive continuous ?_
  refine orderTransitive (applyMonotone (projectBelow _ _) belowIterate) ?_
  exact supremumAbove (iterate function) (count + 1)

/-- The least fixed point is a fixed point. -/
theorem applyLeastFixedPoint (function : Limit) :
    apply function (leastFixedPoint function) = leastFixedPoint function :=
  orderAntisymmetric (applyLeastFixedPointBelow function)
    (leastFixedPointBelow (applyMonotoneArgument function (applyLeastFixedPointBelow function)))

theorem leastFixedPointMonotone {lower upper : Limit} (functionBelow : below lower upper) :
    below (leastFixedPoint lower) (leastFixedPoint upper) :=
  leastFixedPointBelow (orderTransitive (applyMonotoneFunction functionBelow _)
    (equalBelow (applyLeastFixedPoint upper)))

/-! ## Projections to 𝔻₀ and the projections of application -/

/-- An element that reads below ⊤ somewhere projects to ⊥ in 𝔻₀: the projection is ⊥ or ⊤, and a
projection ⊤ makes the element ⊤, which reads ⊤ everywhere. -/
theorem projectZeroBottom {value argument : Limit} (notTop : apply value argument ≠ top) :
    project 0 value = bottom := by
  rcases projectZeroTwoPoint value with isBottom | isTop
  · exact isBottom
  · exfalso
    apply notTop
    have valueTop : value = top :=
      orderAntisymmetric (topGreatest _) (by rw [← isTop]; exact projectBelow 0 value)
    rw [valueTop]
    exact applyTop argument

theorem applyBottomBottom : apply bottom bottom ≠ top := by
  rw [applyBottom]
  exact fun equal => topNotBottom equal.symm

/-- x_{k+1}(y) ⊑ (x(y_k))_k. -/
theorem applyProjectSuccessorBelow (projection : Nat) (function argument : Limit) :
    below (apply (project (projection + 1) function) argument)
      (project projection (apply function (project projection argument))) := by
  rw [← applyProjectResult, applyProjectArgument]
  exact projectMonotone projection (applyMonotoneFunction (projectBelow _ _) _)

/-! ## Park's theorem for Turing's combinator -/

/-- The reading of A = λx.λf. f (x x f) applied to x and f is f (x x f). -/
theorem interpretFixpointHalfApply (environment : Nat → Limit) (first second : Limit) :
    apply (apply (interpret ParallelTypesTheorems.fixpointHalf environment) first) second =
      apply second (apply (apply first first) second) := by
  rw [ParallelTypesTheorems.fixpointHalf, interpretAbstraction, interpretAbstraction]
  rfl

section

/- An element a that applies as A = λx.λf. f (x x f) does: a x f = f (x x f). -/
variable {half : Limit}
  (halfBehaviour : ∀ first second, apply (apply half first) second = apply second (apply (apply first first) second))

include halfBehaviour in
theorem projectZeroHalf : project 0 half = bottom := by
  apply projectZeroBottom (argument := bottom)
  intro isTop
  have applied := congrArg (fun value => apply value bottom) isTop
  simp only [halfBehaviour, applyBottom, applyTop] at applied
  exact topNotBottom applied.symm

include halfBehaviour in
theorem projectZeroHalfApplied : project 0 (apply half (project 0 half)) = bottom := by
  apply projectZeroBottom (argument := bottom)
  rw [projectZeroHalf halfBehaviour, halfBehaviour, applyBottom]
  exact fun equal => topNotBottom equal.symm

include halfBehaviour in
/-- aₙ aₙ f ⊑ lfp f for every n and f, by induction on n, two levels at a time. -/
theorem projectedHalvesBelow : ∀ (projection : Nat) (function : Limit),
    below (apply (apply (project projection half) (project projection half)) function)
      (leastFixedPoint function) ∧
    below (apply (apply (project (projection + 1) half) (project (projection + 1) half)) function)
      (leastFixedPoint function) := by
  intro projection
  induction projection with
  | zero =>
      intro function
      constructor
      · rw [projectZeroHalf halfBehaviour, applyBottom, applyBottom]
        exact bottomLeast _
      · have inner := applyProjectSuccessorBelow 0 half (project 1 half)
        rw [projectProject, Nat.min_eq_right (Nat.zero_le 1), projectZeroHalfApplied halfBehaviour] at inner
        refine orderTransitive (applyMonotoneFunction inner function) ?_
        rw [applyBottom]
        exact bottomLeast _
  | succ projection belowBoth =>
      intro function
      refine ⟨(belowBoth function).2, ?_⟩
      -- a_{k+2} a_{k+2} ⊑ (a a_{k+1})_{k+1}
      have inner := applyProjectSuccessorBelow (projection + 1) half (project (projection + 2) half)
      rw [projectProject, Nat.min_eq_right (Nat.le_succ (projection + 1))] at inner
      refine orderTransitive (applyMonotoneFunction inner function) ?_
      refine orderTransitive (applyProjectSuccessorBelow projection _ function) ?_
      refine orderTransitive (projectBelow _ _) ?_
      rw [halfBehaviour]
      refine orderTransitive (applyMonotone (projectBelow projection function)
        (orderTransitive ((belowBoth (project projection function)).2)
          (leastFixedPointMonotone (projectBelow projection function)))) ?_
      exact applyLeastFixedPointBelow function

include halfBehaviour in
/-- Park's theorem: a a f is the least fixed point of f. -/
theorem halvesApply (function : Limit) : apply (apply half half) function = leastFixedPoint function := by
  apply orderAntisymmetric
  · apply projectLeast
    intro projection
    obtain ⟨outer, outerBelow⟩ := applyContinuous (apply half half) function projection
    obtain ⟨inner, innerBelow⟩ := applyContinuous half half outer
    refine orderTransitive outerBelow ?_
    refine orderTransitive (applyMonotone innerBelow (projectBelow outer function)) ?_
    exact (projectedHalvesBelow halfBehaviour inner function).1
  · exact leastFixedPointBelow (equalBelow (halfBehaviour half function).symm)

end

/-- Park's theorem for Θ: the reading of Θ applied to f is the least fixed point of f. -/
theorem interpretFixpointApply (environment : Nat → Limit) (function : Limit) :
    apply (interpret ParallelTypesTheorems.fixpoint environment) function = leastFixedPoint function :=
  halvesApply (interpretFixpointHalfApply environment) function

/-- Two elements that apply alike are equal. -/
theorem equalOfApply {left right : Limit} (same : ∀ argument, apply left argument = apply right argument) :
    left = right :=
  orderAntisymmetric (extensionalBelow.mpr fun argument => equalBelow (same argument))
    (extensionalBelow.mpr fun argument => equalBelow (same argument).symm)

/-- A′ = λx.λf. f (λv. x x f v), the half of the by-value fixed point combinator Θ′ = A′ A′
(the library's `wren_fixpoint_by_value` once its layers are read). -/
def fixpointByValueHalf : Term :=
  .abstraction (.abstraction (.application (.boundVariable 0)
    (.abstraction (.application (.application (.application (.boundVariable 2) (.boundVariable 2))
      (.boundVariable 1)) (.boundVariable 0)))))

/-- The reading of A′ applied to x and f is f (x x f), by the η rule in the model. -/
theorem interpretFixpointByValueHalfApply (environment : Nat → Limit) (first second : Limit) :
    apply (apply (interpret fixpointByValueHalf environment) first) second =
      apply second (apply (apply first first) second) := by
  rw [fixpointByValueHalf, interpretAbstraction, interpretAbstraction]
  show apply second (interpret _ _) = _
  congr 1
  exact equalOfApply fun value => by rw [interpretAbstraction]; rfl

/-- Park's theorem for Θ′ = A′ A′. -/
theorem interpretFixpointByValueApply (environment : Nat → Limit) (function : Limit) :
    apply (interpret (.application fixpointByValueHalf fixpointByValueHalf) environment) function =
      leastFixedPoint function :=
  halvesApply (interpretFixpointByValueHalfApply environment) function

end Limit

end LambdaJit.DInfinity
