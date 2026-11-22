import LambdaJit.Defunctionalization

/-!
# The prelude's equation lemmas in ⊢^{defunctionalized}_{λ-lattice-η}

D5 puts in its first tier the lemmas that
⊢^{defunctionalized}_{λ-lattice-η} (module `Theory`, the relation `Equal`) proves on every
instance. This module proves that the fifteen equation lemmas of
`gezi/corpora/standard_library/prelude.pl` are such lemmas: the twelve rows of the recursive
functions `natural_equal`, `natural_at_least`, `natural_difference` and `natural_double`, and the
β laws `apply_to_applied` (A1), `identity_applied` (I1) and `compose_applied`. For each, the two
sides as the index of the standard library holds them (`lemma_sides/4`: a thunk whose holes are the
metavariables, or a closed term when the lemma has none), applied to arbitrary finite terms, one per
metavariable, are equal.

## The sides

A side is written with the finite terms of the defines it names: a library name's handle stands
for the layer of its define (D1), whose solution is the finite term below, `fixpoint` unfolded to
Turing's fixed point combinator. `zero` and `true` are one layer, K's (`Readback.Witness.first`),
`false` is K*'s (`Agreement.secondThunk`), and `identity` is I's (`Readback.Witness.identity`). The
test `gezi/tests/defunctionalization_agreement.plt` checks that every side here, printed in
the Prolog syntax, is the side `lemma_sides/4` holds with every handle replaced by the finite term
of its layer.

## The proofs

`headStep` contracts the head redex of a term: an application of a thunk with holes fills the
first hole (the first clause of the defunctionalized β rule), a thunk without holes at the head is
the instance of its code (the second clause), and an application whose function has a head redex
contracts it. Every head step is an equation of `Equal` (`headStepEqual`). Each lemma is proved by
`equalOfHeadSteps`, with the numbers of head steps after which the two sides are one term; the
kernel checks the equation of the two results by evaluation (`rfl`) with the arguments left as
variables, so the head steps never inspect an argument and the proof covers every instance.
-/

namespace LambdaJit.PreludeLemmas

open LambdaJit.Defunctionalization

/-! ## Head steps -/

/-- The contraction of the head redex of a term, none when its head is no redex. -/
def headStep : FiniteTerm → Option FiniteTerm
  | .apply (.thunk code (hole :: holes) fillings) argument =>
      some (.thunk code holes (fill hole holes fillings argument))
  | .apply function argument => (headStep function).map (fun reduced => .apply reduced argument)
  | .thunk code [] fillings => code.instantiate fillings
  | _ => none

/-- At most `fuel` head steps from `term`. -/
def headSteps : Nat → FiniteTerm → FiniteTerm
  | 0, term => term
  | fuel + 1, term =>
      match headStep term with
      | some next => headSteps fuel next
      | none => term

/-- A head step is an equation of λ-lattice-η on defunctionalized terms. -/
theorem headStepEqual : ∀ {term next : FiniteTerm}, headStep term = some next → Equal term next
  | .apply (.thunk _ (_ :: _) _) _, _, stepped => by
      simp only [headStep, Option.some.injEq] at stepped
      subst stepped
      exact .betaFill
  | .apply (.thunk _ [] _) _, _, stepped => by
      simp only [headStep, Option.map_eq_some_iff] at stepped
      obtain ⟨_, instantiated, rfl⟩ := stepped
      exact .congruenceApply (.betaInstance instantiated) (.reflexive _)
  | .apply (.apply _ _) _, _, stepped => by
      simp only [headStep, Option.map_eq_some_iff] at stepped
      obtain ⟨_, reduced, rfl⟩ := stepped
      exact .congruenceApply (headStepEqual reduced) (.reflexive _)
  | .apply (.choice _ _) _, _, stepped => by simp [headStep] at stepped
  | .apply (.parallel _ _) _, _, stepped => by simp [headStep] at stepped
  | .thunk _ [] _, _, stepped => by
      simp only [headStep] at stepped
      exact .betaInstance stepped
  | .thunk _ (_ :: _) _, _, stepped => by simp [headStep] at stepped
  | .choice _ _, _, stepped => by simp [headStep] at stepped
  | .parallel _ _, _, stepped => by simp [headStep] at stepped

/-- Head steps are equations of λ-lattice-η on defunctionalized terms. -/
theorem headStepsEqual : ∀ (fuel : Nat) (term : FiniteTerm), Equal term (headSteps fuel term)
  | 0, term => .reflexive term
  | fuel + 1, term => by
      unfold headSteps
      cases stepped : headStep term with
      | none => exact .reflexive term
      | some next => exact .transitive (headStepEqual stepped) (headStepsEqual fuel next)

/-- Two terms are equal when some numbers of head steps take them to one term. -/
theorem equalOfHeadSteps {left right : FiniteTerm} (leftFuel rightFuel : Nat)
    (meet : headSteps leftFuel left = headSteps rightFuel right) : Equal left right :=
  .transitive (headStepsEqual leftFuel left) (meet ▸ .symmetric (headStepsEqual rightFuel right))

/-! ## The defines -/

/-- `λx.λf. f (x x f)`, Turing's fixed point combinator being this term applied to itself. -/
def fixpointGenerator : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))) [.slot 1, .slot 0] []

/-- `fixpoint`, `(λx.λf. f (x x f)) (λx.λf. f (x x f))`. -/
def fixpoint : FiniteTerm := .apply fixpointGenerator fixpointGenerator

/-- `zero`, `λz.λ_. z`: K's layer. -/
def zero : FiniteTerm := Readback.Witness.first

/-- `true`, `λt.λ_. t`: K's layer, one address with `zero`. -/
def booleanTrue : FiniteTerm := Readback.Witness.first

/-- `false`, `λ_.λf. f`: K*'s layer. -/
def booleanFalse : FiniteTerm := Agreement.secondThunk

/-- `successor`, `λn.λ_.λs. s n`. -/
def successor : FiniteTerm := .thunk (.apply (.slot 0) (.slot 1)) [.slot 1, .ignored, .slot 0] []

/-- `identity`, `λx. x`: I's layer. -/
def identity : FiniteTerm := Readback.Witness.identity

/-- `compose`, `λf.λg.λx. f (g x)`. -/
def compose : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 0, .slot 1, .slot 2] []

/-- `apply_to`, `λa.λf. f a`. -/
def applyTo : FiniteTerm := .thunk (.apply (.slot 0) (.slot 1)) [.slot 1, .slot 0] []

/-- `natural_equal`, `fixpoint (λself.λm.λn. m (n true (λ_. false)) (λm1. n false (self m1)))`. -/
def naturalEqual : FiniteTerm :=
  .apply fixpoint (.thunk (.apply (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3)))
      (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.apply (.slot 2) (.slot 3))) [.slot 3]
        [.slot 1, .slot 4, .slot 5]))
    [.slot 5, .slot 0, .slot 1]
    [booleanTrue, .thunk (.slot 0) [.ignored, .ignored, .slot 0] [], booleanFalse])

/-- `natural_at_least`, `fixpoint (λself.λm.λn. n true (λn1. m false (λm1. self m1 n1)))`. -/
def naturalAtLeast : FiniteTerm :=
  .apply fixpoint (.thunk (.apply (.apply (.slot 0) (.slot 1))
      (.thunk (.apply (.apply (.slot 0) (.slot 1))
          (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1] [.slot 2, .slot 3]))
        [.slot 3] [.slot 2, .slot 3, .slot 4]))
    [.slot 4, .slot 2, .slot 0] [booleanTrue, booleanFalse])

/-- `natural_difference`, `fixpoint (λself.λm.λn. n m (λn1. m zero (λm1. self m1 n1)))`. -/
def naturalDifference : FiniteTerm :=
  .apply fixpoint (.thunk (.apply (.apply (.slot 0) (.slot 1))
      (.thunk (.apply (.apply (.slot 0) (.slot 1))
          (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1] [.slot 2, .slot 3]))
        [.slot 3] [.slot 1, .slot 2, .slot 3]))
    [.slot 3, .slot 1, .slot 0] [zero])

/-- `natural_double`, `fixpoint (λself.λn. n zero (λn1. successor (successor (self n1))))`. -/
def naturalDouble : FiniteTerm :=
  .apply fixpoint (.thunk (.apply (.apply (.slot 0) (.slot 1))
      (.thunk (.apply (.slot 0) (.apply (.slot 0) (.apply (.slot 1) (.slot 2)))) [.slot 2]
        [.slot 2, .slot 3]))
    [.slot 3, .slot 0] [zero, successor])

/-! ## The sides of the lemmas -/

/-- `natural_equal @ zero @ zero`. -/
def naturalEqualZeroZeroLeft : FiniteTerm := .apply (.apply naturalEqual zero) zero

/-- `true`. -/
def naturalEqualZeroZeroRight : FiniteTerm := booleanTrue

/-- `N^(natural_equal @ zero @ (successor @ N))`. -/
def naturalEqualZeroSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2]
    [.apply naturalEqual zero, successor]

/-- `N^false`. -/
def naturalEqualZeroSuccessorRight : FiniteTerm := .thunk (.slot 0) [.ignored, .ignored, .slot 0] []

/-- `M^(natural_equal @ (successor @ M) @ zero)`. -/
def naturalEqualSuccessorZeroLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.slot 3)) [.slot 2]
    [naturalEqual, successor, zero]

/-- `M^false`. -/
def naturalEqualSuccessorZeroRight : FiniteTerm := .thunk (.slot 0) [.ignored, .ignored, .slot 0] []

/-- `M^N^(natural_equal @ (successor @ M) @ (successor @ N))`. -/
def naturalEqualSuccessorSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 1) (.slot 3)))
    [.slot 2, .slot 3] [naturalEqual, successor]

/-- `M^N^(natural_equal @ M @ N)`. -/
def naturalEqualSuccessorSuccessorRight : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1, .slot 2] [naturalEqual]

/-- `M^(natural_at_least @ M @ zero)`. -/
def naturalAtLeastZeroLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1] [naturalAtLeast, zero]

/-- `M^true`. -/
def naturalAtLeastZeroRight : FiniteTerm := .thunk (.slot 0) [.ignored, .slot 0, .ignored] []

/-- `N^(natural_at_least @ zero @ (successor @ N))`. -/
def naturalAtLeastZeroSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2]
    [.apply naturalAtLeast zero, successor]

/-- `N^false`. -/
def naturalAtLeastZeroSuccessorRight : FiniteTerm := .thunk (.slot 0) [.ignored, .ignored, .slot 0] []

/-- `M^N^(natural_at_least @ (successor @ M) @ (successor @ N))`. -/
def naturalAtLeastSuccessorSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 1) (.slot 3)))
    [.slot 2, .slot 3] [naturalAtLeast, successor]

/-- `M^N^(natural_at_least @ M @ N)`. -/
def naturalAtLeastSuccessorSuccessorRight : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1, .slot 2] [naturalAtLeast]

/-- `M^(natural_difference @ M @ zero)`. -/
def naturalDifferenceZeroLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1] [naturalDifference, zero]

/-- `M^M`, I's layer. -/
def naturalDifferenceZeroRight : FiniteTerm := identity

/-- `N^(natural_difference @ zero @ (successor @ N))`. -/
def naturalDifferenceZeroSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2]
    [.apply naturalDifference zero, successor]

/-- `N^zero`. -/
def naturalDifferenceZeroSuccessorRight : FiniteTerm := .thunk (.slot 0) [.ignored, .slot 0, .ignored] []

/-- `M^N^(natural_difference @ (successor @ M) @ (successor @ N))`. -/
def naturalDifferenceSuccessorSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 1) (.slot 3)))
    [.slot 2, .slot 3] [naturalDifference, successor]

/-- `M^N^(natural_difference @ M @ N)`. -/
def naturalDifferenceSuccessorSuccessorRight : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1, .slot 2] [naturalDifference]

/-- `natural_double @ zero`. -/
def naturalDoubleZeroLeft : FiniteTerm := .apply naturalDouble zero

/-- `zero`. -/
def naturalDoubleZeroRight : FiniteTerm := zero

/-- `N^(natural_double @ (successor @ N))`. -/
def naturalDoubleSuccessorLeft : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [naturalDouble, successor]

/-- `N^(successor @ (successor @ (natural_double @ N)))`. -/
def naturalDoubleSuccessorRight : FiniteTerm :=
  .thunk (.apply (.slot 0) (.apply (.slot 0) (.apply (.slot 1) (.slot 2)))) [.slot 2]
    [successor, naturalDouble]

/-- `A^F^(apply_to @ A @ F)`. -/
def applyToAppliedLeft : FiniteTerm :=
  .thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1, .slot 2] [applyTo]

/-- `A^F^(F @ A)`, `apply_to`'s layer. -/
def applyToAppliedRight : FiniteTerm := applyTo

/-- `X^(identity @ X)`. -/
def identityAppliedLeft : FiniteTerm := .thunk (.apply (.slot 0) (.slot 1)) [.slot 1] [identity]

/-- `X^X`, I's layer. -/
def identityAppliedRight : FiniteTerm := identity

/-- `F^G^X^(compose @ F @ G @ X)`. -/
def composeAppliedLeft : FiniteTerm :=
  .thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3))
    [.slot 1, .slot 2, .slot 3] [compose]

/-- `F^G^X^(F @ (G @ X))`, `compose`'s layer. -/
def composeAppliedRight : FiniteTerm := compose

/-! ## The lemmas on every instance -/

theorem naturalEqualZeroZero : Equal naturalEqualZeroZeroLeft naturalEqualZeroZeroRight :=
  equalOfHeadSteps 13 0 rfl

theorem naturalEqualZeroSuccessor (argument : FiniteTerm) :
    Equal (.apply naturalEqualZeroSuccessorLeft argument)
      (.apply naturalEqualZeroSuccessorRight argument) :=
  equalOfHeadSteps 16 0 rfl

theorem naturalEqualSuccessorZero (argument : FiniteTerm) :
    Equal (.apply naturalEqualSuccessorZeroLeft argument)
      (.apply naturalEqualSuccessorZeroRight argument) :=
  equalOfHeadSteps 18 1 rfl

theorem naturalEqualSuccessorSuccessor (first second : FiniteTerm) :
    Equal (.apply (.apply naturalEqualSuccessorSuccessorLeft first) second)
      (.apply (.apply naturalEqualSuccessorSuccessorRight first) second) :=
  equalOfHeadSteps 20 3 rfl

theorem naturalAtLeastZero (argument : FiniteTerm) :
    Equal (.apply naturalAtLeastZeroLeft argument) (.apply naturalAtLeastZeroRight argument) :=
  equalOfHeadSteps 12 1 rfl

theorem naturalAtLeastZeroSuccessor (argument : FiniteTerm) :
    Equal (.apply naturalAtLeastZeroSuccessorLeft argument)
      (.apply naturalAtLeastZeroSuccessorRight argument) :=
  equalOfHeadSteps 18 1 rfl

theorem naturalAtLeastSuccessorSuccessor (first second : FiniteTerm) :
    Equal (.apply (.apply naturalAtLeastSuccessorSuccessorLeft first) second)
      (.apply (.apply naturalAtLeastSuccessorSuccessorRight first) second) :=
  equalOfHeadSteps 21 2 rfl

theorem naturalDifferenceZero (argument : FiniteTerm) :
    Equal (.apply naturalDifferenceZeroLeft argument)
      (.apply naturalDifferenceZeroRight argument) :=
  equalOfHeadSteps 11 1 rfl

theorem naturalDifferenceZeroSuccessor (argument : FiniteTerm) :
    Equal (.apply naturalDifferenceZeroSuccessorLeft argument)
      (.apply naturalDifferenceZeroSuccessorRight argument) :=
  equalOfHeadSteps 18 1 rfl

theorem naturalDifferenceSuccessorSuccessor (first second : FiniteTerm) :
    Equal (.apply (.apply naturalDifferenceSuccessorSuccessorLeft first) second)
      (.apply (.apply naturalDifferenceSuccessorSuccessorRight first) second) :=
  equalOfHeadSteps 21 2 rfl

theorem naturalDoubleZero : Equal naturalDoubleZeroLeft naturalDoubleZeroRight :=
  equalOfHeadSteps 9 0 rfl

theorem naturalDoubleSuccessor (argument : FiniteTerm) :
    Equal (.apply naturalDoubleSuccessorLeft argument)
      (.apply naturalDoubleSuccessorRight argument) :=
  equalOfHeadSteps 12 0 rfl

theorem applyToApplied (argument function : FiniteTerm) :
    Equal (.apply (.apply applyToAppliedLeft argument) function)
      (.apply (.apply applyToAppliedRight argument) function) :=
  equalOfHeadSteps 3 0 rfl

theorem identityApplied (argument : FiniteTerm) :
    Equal (.apply identityAppliedLeft argument) (.apply identityAppliedRight argument) :=
  equalOfHeadSteps 2 0 rfl

theorem composeApplied (outer inner argument : FiniteTerm) :
    Equal (.apply (.apply (.apply composeAppliedLeft outer) inner) argument)
      (.apply (.apply (.apply composeAppliedRight outer) inner) argument) :=
  equalOfHeadSteps 4 0 rfl

end LambdaJit.PreludeLemmas
