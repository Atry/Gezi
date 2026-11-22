import LambdaJit.DInfinityFixedPoint
import LambdaJit.RefinementSearch

/-!
# The static argument transformation in Wadsworth's D∞

Section 18.1 of the proofs file, on elements of D∞: with
F = λs.λn.λg. K (λm. s m g) n g and G = λt.λn. K t n h, the least fixed points satisfy
λn. (lfp F) n h = lfp G (`staticArgumentLeastFixedPoint`), so (lfp F) x h = (lfp G) x for every x
(`staticArgumentLeastFixedPointApply`). The elements F, G, K and the swap λs.λg.λm. s m g are
given by how they apply (the hypotheses), so the statement names no term.

1. q = λn. (lfp F) n h is a prefixed point of G, since lfp F is a fixed point of F; so
   lfp G ⊑ q (`leastFixedPointBelow`).
2. q ⊑ lfp G: a projection of (lfp F) n h is below (Fⁱ ⊥) n h for some i, by continuity of
   application and compactness (`projectBelowIterate`), and (Fⁱ ⊥) n h ⊑ (lfp G) n by induction
   on i, since K's reading is monotone and lfp G is a fixed point of G. This is the
   fixed-point induction of section 18.1.

A fact of the model, the bridge to Definition 14 through
`DdLP96Model.contextualEquivalenceOfInterpretEqual`; the model does not define the semantics.
-/

namespace LambdaJit.DInfinity

namespace Limit

section

variable {static dropped swapped body held : Limit}
  (swappedBehaviour : ∀ function argument value,
    apply (apply (apply swapped function) argument) value = apply (apply function value) argument)
  (staticBehaviour : ∀ function count argument,
    apply (apply (apply static function) count) argument =
      apply (apply (apply body (apply (apply swapped function) argument)) count) argument)
  (droppedBehaviour : ∀ function count,
    apply (apply dropped function) count = apply (apply (apply body function) count) held)

include swappedBehaviour staticBehaviour droppedBehaviour in
/-- Every iterate of F, applied to n and h, is below (lfp G) n. -/
theorem iterateStaticBelow : ∀ (count : Nat) (argument : Limit),
    below (apply (apply (iterate static count) argument) held)
      (apply (leastFixedPoint dropped) argument) := by
  intro count
  induction count with
  | zero =>
      intro argument
      show below (apply (apply bottom argument) held) _
      rw [applyBottom, applyBottom]
      exact bottomLeast _
  | succ count belowDropped =>
      intro argument
      show below (apply (apply (apply static (iterate static count)) argument) held) _
      rw [staticBehaviour]
      have swappedBelow : below (apply (apply swapped (iterate static count)) held)
          (leastFixedPoint dropped) := by
        rw [extensionalBelow]
        intro value
        rw [swappedBehaviour]
        exact belowDropped value
      refine orderTransitive
        (applyMonotoneFunction (applyMonotoneFunction (applyMonotoneArgument body swappedBelow) _) _) ?_
      rw [← droppedBehaviour, applyLeastFixedPoint]
      exact orderReflexive _

include swappedBehaviour staticBehaviour droppedBehaviour in
/-- λn. (lfp F) n h = lfp G. -/
theorem staticArgumentLeastFixedPoint :
    apply (apply swapped (leastFixedPoint static)) held = leastFixedPoint dropped := by
  apply orderAntisymmetric
  · rw [extensionalBelow]
    intro argument
    rw [swappedBehaviour]
    apply projectLeast
    intro projection
    obtain ⟨outer, outerBelow⟩ :=
      applyContinuous (apply (leastFixedPoint static) argument) held projection
    obtain ⟨inner, innerBelow⟩ := applyContinuous (leastFixedPoint static) argument outer
    obtain ⟨count, iterateAbove⟩ := projectBelowIterate static inner
    refine orderTransitive outerBelow ?_
    refine orderTransitive (applyMonotone (orderTransitive innerBelow
      (applyMonotone iterateAbove (projectBelow inner argument))) (projectBelow outer held)) ?_
    exact iterateStaticBelow swappedBehaviour staticBehaviour droppedBehaviour count argument
  · apply leastFixedPointBelow
    rw [extensionalBelow]
    intro argument
    apply equalBelow
    rw [droppedBehaviour, swappedBehaviour, ← applyLeastFixedPoint static, staticBehaviour,
      applyLeastFixedPoint]

include swappedBehaviour staticBehaviour droppedBehaviour in
/-- (lfp F) x h = (lfp G) x. -/
theorem staticArgumentLeastFixedPointApply (argument : Limit) :
    apply (apply (leastFixedPoint static) argument) held = apply (leastFixedPoint dropped) argument := by
  rw [← swappedBehaviour, staticArgumentLeastFixedPoint swappedBehaviour staticBehaviour droppedBehaviour]

end

/-! ## Readings of the terms of the static-argument lemmas of the entry `wren`

The bodies below are those of the two sides of each lemma after one development
(`RefinementSearch.developed`) of the side with its metavariables abstracted
(`StatementNormalisation.abstracted`); their free indices are the variables of those
abstractions. The proofs that the developed sides are these terms are in module
`WrenLemmaProofs`. -/

open LambdaJit.Semantics
open LambdaJit.ContextualPreorder (extendEnvironment)
open LambdaJit.RefinementSearch (underAbstractions)

/-- Two terms under as many abstractions read alike in every environment when their bodies do. -/
theorem interpretUnderAbstractions : ∀ {count : Nat} {left right leftBody rightBody : Term},
    underAbstractions count left = some leftBody → underAbstractions count right = some rightBody →
    (∀ environment, interpret leftBody environment = interpret rightBody environment) →
    ∀ environment, interpret left environment = interpret right environment := by
  intro count
  induction count with
  | zero =>
      intro left right leftBody rightBody leftUnder rightUnder same
      simp only [underAbstractions, Option.some.injEq] at leftUnder rightUnder
      subst leftUnder rightUnder
      exact same
  | succ remaining remainingSame =>
      intro left right leftBody rightBody leftUnder rightUnder same environment
      cases left <;> cases right <;> simp only [underAbstractions, reduceCtorEq] at leftUnder rightUnder
      exact equalOfApply fun value => by
        rw [interpretAbstraction, interpretAbstraction]
        exact remainingSame leftUnder rightUnder same _

/-- Θ′ = A′ A′. -/
def byValueFixpoint : Term := .application fixpointByValueHalf fixpointByValueHalf

/-- λs.λg.λm. s m g. -/
def swap : Term :=
  .abstraction (.abstraction (.abstraction
    (.application (.application (.boundVariable 2) (.boundVariable 0)) (.boundVariable 1))))

theorem interpretSwapApply (environment : Nat → Limit) (function argument value : Limit) :
    apply (apply (apply (interpret swap environment) function) argument) value =
      apply (apply function value) argument := by
  rw [swap, interpretAbstraction, interpretAbstraction, interpretAbstraction]
  rfl

/-! ### `wren_static_argument_fixpoint`: Θ′ F X H = Θ′ G X + (its typed branch) -/

/-- F = λs.λn.λg. K (λm. s m g) n g, K the variable 8 of the body. -/
def staticArgumentStatic : Term :=
  .abstraction (.abstraction (.abstraction
    (.application (.application (.application (.boundVariable 11)
      (.abstraction (.application (.application (.boundVariable 3) (.boundVariable 0)) (.boundVariable 1))))
      (.boundVariable 1)) (.boundVariable 0))))

/-- G = λt.λn. K t n H, K the variable 8 and H the variable 6 of the body. -/
def staticArgumentDropped : Term :=
  .abstraction (.abstraction
    (.application (.application (.application (.boundVariable 10) (.boundVariable 1)) (.boundVariable 0))
      (.boundVariable 8)))

/-- Θ′ F X H, X the variable 7 of the body. -/
def staticArgumentLeft : Term :=
  .application (.application (.application byValueFixpoint staticArgumentStatic) (.boundVariable 7))
    (.boundVariable 6)

/-- Θ′ G X. -/
def staticArgumentRight : Term :=
  .application (.application byValueFixpoint staticArgumentDropped) (.boundVariable 7)

/-- Θ′ F X H and Θ′ G X read alike in every environment (section 18.1). -/
theorem interpretStaticArgument (environment : Nat → Limit) :
    interpret staticArgumentLeft environment = interpret staticArgumentRight environment := by
  show apply (apply (apply (interpret byValueFixpoint environment) (interpret staticArgumentStatic environment))
      (environment 7)) (environment 6) =
    apply (apply (interpret byValueFixpoint environment) (interpret staticArgumentDropped environment))
      (environment 7)
  rw [byValueFixpoint, interpretFixpointByValueApply, interpretFixpointByValueApply]
  refine staticArgumentLeastFixedPointApply (swapped := interpret swap environment) (body := environment 8)
    (interpretSwapApply environment) ?_ ?_ (environment 7)
  · intro function count argument
    rw [staticArgumentStatic, interpretAbstraction, interpretAbstraction, interpretAbstraction]
    show apply (apply (apply (environment 8) (interpret _ _)) count) argument = _
    congr 3
    exact equalOfApply fun value => by
      rw [interpretAbstraction, interpretSwapApply]
      rfl
  · intro function count
    rw [staticArgumentDropped, interpretAbstraction, interpretAbstraction]
    rfl

/-! ### `wren_own_loop_lifted` and `wren_own_loop_lifted_respelled`: Θ′ G X S = Θ′ F X H S

The loop is lambda-dropped on the left, its static argument H free in G, and lambda-lifted on
the right, H passed to F at every call. With K the loop's body over its static argument, F and G
are the F and G of section 18.1, up to the β rule. -/

theorem interpretApplicationEquation (function argument : Term) (environment : Nat → Limit) :
    interpret (.application function argument) environment =
      apply (interpret function environment) (interpret argument environment) := rfl

theorem interpretVariableEquation (index : Nat) (environment : Nat → Limit) :
    interpret (.boundVariable index) environment = environment index := rfl

/-- t m (t m x), the loop's recursive calls, under the binders of the iteration m: t is the
variable `recursion`, x the variable `state`, m the variable 0. -/
def ownLoopCalls (recursion state : Term) : Term :=
  .application (.application recursion (.boundVariable 0))
    (.application (.application recursion (.boundVariable 0)) state)

/-- t m (t m x) of the lifted loop, t m g standing for t m: t is the variable `recursion` and g
the variable `held`. -/
def ownLoopLiftedCalls (recursion held state : Term) : Term :=
  .application (.application (.application recursion (.boundVariable 0)) held)
    (.application (.application (.application recursion (.boundVariable 0)) held) state)

/-- K = λt.λn.λg.λx. n x (λm. t m (t m x)) (λm. E), E the exit `exit` over t = 4, g = 2, x = 1,
m = 0. -/
def ownLoopBody (exit : Term) : Term :=
  .abstraction (.abstraction (.abstraction (.abstraction
    (.application (.application (.application (.boundVariable 2) (.boundVariable 0))
      (.abstraction (ownLoopCalls (.boundVariable 4) (.boundVariable 1))))
      (.abstraction exit)))))

/-- G = λt.λn.λx. n x (λm. t m (t m x)) (λm. E), H the variable 5 of the body. -/
def ownLoopDropped (exit : Term) : Term :=
  .abstraction (.abstraction (.abstraction
    (.application (.application (.application (.boundVariable 1) (.boundVariable 0))
      (.abstraction (ownLoopCalls (.boundVariable 3) (.boundVariable 1))))
      (.abstraction exit))))

/-- F = λs.λn.λg.λx. n x (λm. s m g (s m g x)) (λm. E). -/
def ownLoopLifted (exit : Term) : Term :=
  .abstraction (.abstraction (.abstraction (.abstraction
    (.application (.application (.application (.boundVariable 2) (.boundVariable 0))
      (.abstraction (ownLoopLiftedCalls (.boundVariable 4) (.boundVariable 2) (.boundVariable 1))))
      (.abstraction exit)))))

/-- The exits of `wren_own_loop_lifted`: λm. H (t m (t m x)), in K, G and F. -/
def liftedBodyExit : Term := .application (.boundVariable 2) (ownLoopCalls (.boundVariable 4) (.boundVariable 1))
def liftedDroppedExit : Term := .application (.boundVariable 9) (ownLoopCalls (.boundVariable 3) (.boundVariable 1))
def liftedLiftedExit : Term :=
  .application (.boundVariable 2) (ownLoopLiftedCalls (.boundVariable 4) (.boundVariable 2) (.boundVariable 1))

/-- The exits of `wren_own_loop_lifted_respelled`: λm. t m (t m (H x)). -/
def respelledBodyExit : Term :=
  ownLoopCalls (.boundVariable 4) (.application (.boundVariable 2) (.boundVariable 1))
def respelledDroppedExit : Term :=
  ownLoopCalls (.boundVariable 3) (.application (.boundVariable 9) (.boundVariable 1))
def respelledLiftedExit : Term :=
  ownLoopLiftedCalls (.boundVariable 4) (.boundVariable 2) (.application (.boundVariable 2) (.boundVariable 1))

/-- Θ′ G X S, X the variable 4 and S the variable 3 of the body. -/
def ownLoopLeft (exit : Term) : Term :=
  .application (.application (.application byValueFixpoint (ownLoopDropped exit)) (.boundVariable 4))
    (.boundVariable 3)

/-- Θ′ F X H S, H the variable 5 of the body. -/
def ownLoopRight (exit : Term) : Term :=
  .application (.application (.application (.application byValueFixpoint (ownLoopLifted exit))
    (.boundVariable 4)) (.boundVariable 5)) (.boundVariable 3)

/-- Θ′ G X S and Θ′ F X H S read alike in every environment when the exits of F and G read as the
exit of K with t := λm. s m g, and with g := H: section 18.1 with K the loop's body. -/
theorem interpretOwnLoop {bodyExit droppedExit liftedExit : Term}
    (liftedExits : ∀ environment function count held state iteration,
      interpret liftedExit (extendEnvironment iteration (extendEnvironment state (extendEnvironment held
        (extendEnvironment count (extendEnvironment function environment))))) =
      interpret bodyExit (extendEnvironment iteration (extendEnvironment state (extendEnvironment held
        (extendEnvironment count (extendEnvironment
          (apply (apply (interpret swap environment) function) held) environment))))))
    (droppedExits : ∀ environment function count state iteration,
      interpret droppedExit (extendEnvironment iteration (extendEnvironment state
        (extendEnvironment count (extendEnvironment function environment)))) =
      interpret bodyExit (extendEnvironment iteration (extendEnvironment state (extendEnvironment
        (environment 5) (extendEnvironment count (extendEnvironment function environment))))))
    (environment : Nat → Limit) :
    interpret (ownLoopLeft droppedExit) environment = interpret (ownLoopRight liftedExit) environment := by
  show apply (apply (apply (interpret byValueFixpoint environment) (interpret (ownLoopDropped droppedExit) environment))
      (environment 4)) (environment 3) =
    apply (apply (apply (apply (interpret byValueFixpoint environment) (interpret (ownLoopLifted liftedExit) environment))
      (environment 4)) (environment 5)) (environment 3)
  rw [byValueFixpoint, interpretFixpointByValueApply, interpretFixpointByValueApply]
  congr 1
  refine (staticArgumentLeastFixedPointApply (swapped := interpret swap environment)
    (body := interpret (ownLoopBody bodyExit) environment) (interpretSwapApply environment) ?_ ?_
    (environment 4)).symm
  · intro function count held
    apply equalOfApply
    intro state
    simp only [ownLoopLifted, ownLoopBody, interpretAbstraction, interpretApplicationEquation,
      interpretVariableEquation, extendEnvironment]
    congr 1
    · congr 1
      apply equalOfApply
      intro iteration
      simp only [ownLoopCalls, ownLoopLiftedCalls, interpretAbstraction, interpretApplicationEquation,
        interpretVariableEquation, extendEnvironment, interpretSwapApply]
    · apply equalOfApply
      intro iteration
      rw [interpretAbstraction, interpretAbstraction]
      exact liftedExits environment function count held state iteration
  · intro function count
    apply equalOfApply
    intro state
    simp only [ownLoopDropped, ownLoopBody, interpretAbstraction, interpretApplicationEquation,
      interpretVariableEquation, extendEnvironment]
    refine congr (congrArg Limit.apply ?_) ?_
    · rfl
    · apply equalOfApply
      intro iteration
      rw [interpretAbstraction, interpretAbstraction]
      exact droppedExits environment function count state iteration

/-- `wren_own_loop_lifted`'s two sides, after one development, read alike. -/
theorem interpretOwnLoopLifted (environment : Nat → Limit) :
    interpret (ownLoopLeft liftedDroppedExit) environment =
      interpret (ownLoopRight liftedLiftedExit) environment :=
  interpretOwnLoop (bodyExit := liftedBodyExit)
    (by intros; simp only [liftedBodyExit, liftedLiftedExit, ownLoopCalls, ownLoopLiftedCalls,
      interpretApplicationEquation, interpretVariableEquation, extendEnvironment, interpretSwapApply])
    (by intros; simp only [liftedBodyExit, liftedDroppedExit, ownLoopCalls,
      interpretApplicationEquation, interpretVariableEquation, extendEnvironment])
    environment

/-- `wren_own_loop_lifted_respelled`'s two sides, after one development, read alike. -/
theorem interpretOwnLoopRespelled (environment : Nat → Limit) :
    interpret (ownLoopLeft respelledDroppedExit) environment =
      interpret (ownLoopRight respelledLiftedExit) environment :=
  interpretOwnLoop (bodyExit := respelledBodyExit)
    (by intros; simp only [respelledBodyExit, respelledLiftedExit, ownLoopCalls, ownLoopLiftedCalls,
      interpretApplicationEquation, interpretVariableEquation, extendEnvironment, interpretSwapApply])
    (by intros; simp only [respelledBodyExit, respelledDroppedExit, ownLoopCalls,
      interpretApplicationEquation, interpretVariableEquation, extendEnvironment])
    environment

end Limit

end LambdaJit.DInfinity
