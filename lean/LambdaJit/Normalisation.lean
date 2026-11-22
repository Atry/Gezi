import LambdaJit.LatticeEtaDerivability
import LambdaJit.TermSubstitution

/-!
# A fuelled beta-eta normaliser on the terms of the calculus

On the terms of the calculus of module `Terms` (de Bruijn terms, the set Λ_{+∥}), this module
defines a one-step contraction `step`, which contracts the leftmost outermost beta redex or eta
redex, and a normaliser `normalise fuel term`, which contracts until no redex is left (`some` the
term reached) or until it has made `fuel` contractions and a redex is still left (`none`). The two
contractions are the β rule and the η rule of `DerivableLatticeEta`, ⊢_{λ-lattice-η}, the relation
with no unit law (module `LatticeEtaDerivability`):

- a beta redex (λx. M) N contracts to M[x := N], `instantiate M N`, the right side of
  `DerivableLatticeEta.beta`;
- an eta redex λx. F x with x ∉ FV(F), as `EtaRedex` defines it (the abstraction's body is
  `application F (boundVariable 0)` and index 0 does not occur free in F), contracts to F with
  its free indices lowered by one, `lower F`. F is the shift of `lower F` (`shiftLower`), so the
  contraction is the instance of `DerivableLatticeEta.eta` at `lower F`; conversely, the
  contraction finds every left side of the η rule, with its right side as the contractum
  (`etaContractumShift`).

A second normaliser, `normalForm depth budget term`, reduces the term to weak head normal form
(`weakHead`) and then the subterms of that form, each contraction spending one unit of `budget`,
so that a subterm brought to normal form is not searched again; `normalFormSound` is its soundness
theorem, and `normalFormWithin fuel term` takes `fuel` as both bounds.

The search for a redex looks under abstractions, into both positions of an application, and into
both sides of a choice and of a parallel. A choice or a parallel is never contracted itself: the normaliser uses none of the numbered equations.

`normaliseSound` is the soundness theorem: when `normalise fuel term` is `some result`, the
equation E ⊢_{λ-lattice-η} term = result holds for every set E of hypotheses, derived with
reflexivity, transitivity, the β rule, the η rule and the congruences in the arguments of the
constructors only, no hypothesis and no numbered equation; reflexivity is a theorem of the β rule,
symmetry and transitivity, and the congruences other than those in the argument of an application
and in the body of an abstraction are theorems of these and the congruence in the argument of an
application. Its corollary `derivableOfNormaliseEqual`: two terms that normalise to one term are equal by
⊢_{λ-lattice-η} from every E. The end-to-end check of design decision D6
needs this comparison for the two sides of a
lemma, which are in general beta-eta equal and not syntactically equal. The normaliser's output
is used only through `normaliseSound`, so its statement is the trusted part, not the normaliser.
`normaliseNoRedex` adds that a result has no redex left: none of its subterms is a beta redex or
an eta redex.

The fixtures at the end are checked by the kernel (`decide`).
-/

namespace LambdaJit.Semantics

namespace Term

/-! ## One contraction, and the normaliser -/

/-- The contractum of the application of `function` to `argument` when that application is a
beta redex (λx. M) N, which is M[x := N], `instantiate M N`; `none` when `function` is not an
abstraction. -/
def betaContractum : Term → Term → Option Term
  | abstraction body, argument => some (instantiate body argument)
  | _, _ => none

/-- One contraction, of the leftmost outermost redex: the term itself when it is a beta redex or
an eta redex, otherwise the first redex found in its subterms from left to right, which are the
body of an abstraction, the function and then the argument of an application, and the left and
then the right side of a choice or a parallel. `none` when the term has no redex. -/
def step : Term → Option Term
  | boundVariable _ => none
  | abstraction body =>
      match etaContractum body with
      | some contractum => some contractum
      | none => (step body).map abstraction
  | application function argument =>
      match betaContractum function argument with
      | some contractum => some contractum
      | none =>
          match step function with
          | some contracted => some (application contracted argument)
          | none => (step argument).map (application function)
  | choice left right =>
      match step left with
      | some contracted => some (choice contracted right)
      | none => (step right).map (choice left)
  | parallel left right =>
      match step left with
      | some contracted => some (parallel contracted right)
      | none => (step right).map (parallel left)

/-- Contracts by `step` until no redex is left, making at most `fuel` contractions: `some` the
term reached once it has no redex, `none` when it still has one after `fuel` contractions. -/
def normalise : Nat → Term → Option Term
  | 0, term =>
      match step term with
      | none => some term
      | some _ => none
  | remaining + 1, term =>
      match step term with
      | none => some term
      | some contracted => normalise remaining contracted

/-! ## A normal form by weak head reduction, then the subterms

`normalise` searches for the leftmost outermost redex from the root at every contraction, so that
the subterms of a term that are already normal are searched again at each contraction after them.
`normalForm` reduces a term to weak head normal form and then the subterms of that form, so that
it does not visit again a subterm it has brought to normal form. -/

/-- Weak head reduction: the head beta redex of `term` contracted while there is one, each
contraction spending one unit of `budget`. `some` the weak head normal form with the budget left;
`none` when the budget, or the `depth` of nested reductions, runs out first. -/
def weakHead : Nat → Nat → Term → Option (Term × Nat)
  | 0, _, _ => none
  | depth + 1, budget, application function argument =>
      match weakHead depth budget function with
      | some (abstraction body, remaining) =>
          match remaining with
          | 0 => none
          | remaining + 1 => weakHead depth remaining (instantiate body argument)
      | some (head, remaining) => some (application head argument, remaining)
      | none => none
  | _ + 1, budget, term => some (term, budget)

/-- The abstraction of `body`, eta contracted when it is an eta redex. -/
def etaAbstraction (body : Term) : Term :=
  match etaContractum body with
  | some contractum => contractum
  | none => abstraction body

/-- A normal form of `term`: its weak head normal form (`weakHead`), then the normal forms of the
subterms of that form, each from the budget the one before it left, an abstraction whose body's
normal form is an eta redex eta contracted. `some` the result with the budget left; `none` when the
budget or the `depth` runs out first. -/
def normalForm : Nat → Nat → Term → Option (Term × Nat)
  | 0, _, _ => none
  | depth + 1, budget, term =>
      match weakHead depth budget term with
      | some (abstraction body, remaining) =>
          match normalForm depth remaining body with
          | some (bodyNormal, afterBody) => some (etaAbstraction bodyNormal, afterBody)
          | none => none
      | some (application function argument, remaining) =>
          match normalForm depth remaining function with
          | some (functionNormal, afterFunction) =>
              match normalForm depth afterFunction argument with
              | some (argumentNormal, afterArgument) => some (application functionNormal argumentNormal, afterArgument)
              | none => none
          | none => none
      | some (choice left right, remaining) =>
          match normalForm depth remaining left with
          | some (leftNormal, afterLeft) =>
              match normalForm depth afterLeft right with
              | some (rightNormal, afterRight) => some (choice leftNormal rightNormal, afterRight)
              | none => none
          | none => none
      | some (parallel left right, remaining) =>
          match normalForm depth remaining left with
          | some (leftNormal, afterLeft) =>
              match normalForm depth afterLeft right with
              | some (rightNormal, afterRight) => some (parallel leftNormal rightNormal, afterRight)
              | none => none
          | none => none
      | some (boundVariable index, remaining) => some (boundVariable index, remaining)
      | none => none

/-- `normalForm` with `fuel` as both the depth and the budget, the budget left dropped. -/
def normalFormWithin (fuel : Nat) (term : Term) : Option Term :=
  (normalForm fuel fuel term).map Prod.fst

/-- The beta contraction finds exactly the beta redexes: it answers `some contractum` when
`function` is an abstraction λx. M, and then `contractum` is M[x := `argument`]. -/
theorem betaContractumEqualSome {function argument contractum : Term} :
    betaContractum function argument = some contractum ↔
      ∃ body, function = abstraction body ∧ contractum = instantiate body argument := by
  constructor
  · intro found
    cases function with
    | abstraction body =>
        simp only [betaContractum, Option.some.injEq] at found
        exact ⟨body, rfl, found.symm⟩
    | _ => simp [betaContractum] at found
  · rintro ⟨body, rfl, rfl⟩
    rfl

end Term

open Term

/-! ## Soundness -/

section Soundness

variable {hypotheses : Term → Term → Prop}

/-- The beta contraction is the β rule: an application with a beta contractum is equal to it. -/
theorem betaContractumSound {function argument contractum : Term}
    (found : betaContractum function argument = some contractum) :
    DerivableLatticeEta hypotheses (application function argument) contractum := by
  obtain ⟨body, rfl, rfl⟩ := betaContractumEqualSome.mp found
  exact .beta body argument

/-- The eta contraction is the η rule: an abstraction with an eta contractum `lower function` is
equal to it, by `DerivableLatticeEta.eta (lower function)`, whose abstraction's body is
`application (shift (lower function)) (boundVariable 0)`, that is
`application function (boundVariable 0)` by `shiftLower`. -/
theorem etaContractumSound {body contractum : Term}
    (found : etaContractum body = some contractum) :
    DerivableLatticeEta hypotheses (abstraction body) contractum := by
  obtain ⟨function, rfl, absent, rfl⟩ := etaContractumEqualSome.mp found
  have etaInstance := DerivableLatticeEta.eta (hypotheses := hypotheses) (lower function)
  rw [shiftLower function absent] at etaInstance
  exact etaInstance

/-- One contraction is sound: E ⊢_{λ-lattice-η} equates a term with the term `step`
contracts it to, for every set E of hypotheses, by the β rule or the η rule at the redex and the
congruence rules around it. -/
theorem stepSound : ∀ {term contracted : Term},
    step term = some contracted → DerivableLatticeEta hypotheses term contracted := by
  intro term
  induction term with
  | boundVariable index =>
      intro contracted stepped
      simp [step] at stepped
  | abstraction body bodySound =>
      intro contracted stepped
      simp only [step] at stepped
      split at stepped
      · next contractum found =>
          rw [Option.some.injEq] at stepped
          subst stepped
          exact etaContractumSound found
      · next notFound =>
          obtain ⟨bodyContracted, bodyStepped, rfl⟩ := Option.map_eq_some_iff.mp stepped
          exact .congruenceAbstraction (bodySound bodyStepped)
  | application function argument functionSound argumentSound =>
      intro contracted stepped
      simp only [step] at stepped
      split at stepped
      · next contractum found =>
          rw [Option.some.injEq] at stepped
          subst stepped
          exact betaContractumSound found
      · next notFound =>
          split at stepped
          · next functionContracted functionStepped =>
              rw [Option.some.injEq] at stepped
              subst stepped
              exact .congruenceFunction argument (functionSound functionStepped)
          · next functionNormal =>
              obtain ⟨argumentContracted, argumentStepped, rfl⟩ :=
                Option.map_eq_some_iff.mp stepped
              exact .congruenceArgument function (argumentSound argumentStepped)
  | choice left right leftSound rightSound =>
      intro contracted stepped
      simp only [step] at stepped
      split at stepped
      · next leftContracted leftStepped =>
          rw [Option.some.injEq] at stepped
          subst stepped
          exact .congruenceChoiceLeft right (leftSound leftStepped)
      · next leftNormal =>
          obtain ⟨rightContracted, rightStepped, rfl⟩ := Option.map_eq_some_iff.mp stepped
          exact .congruenceChoiceRight left (rightSound rightStepped)
  | parallel left right leftSound rightSound =>
      intro contracted stepped
      simp only [step] at stepped
      split at stepped
      · next leftContracted leftStepped =>
          rw [Option.some.injEq] at stepped
          subst stepped
          exact .congruenceParallelLeft right (leftSound leftStepped)
      · next leftNormal =>
          obtain ⟨rightContracted, rightStepped, rfl⟩ := Option.map_eq_some_iff.mp stepped
          exact .congruenceParallelRight left (rightSound rightStepped)

/-- The normaliser is sound: when `normalise fuel term` is `some result`, the equation
E ⊢_{λ-lattice-η} term = result for every set E of hypotheses. The derivation chains the
contractions by transitivity (`stepSound`), and is reflexivity when `term` has no redex. -/
theorem normaliseSound : ∀ {fuel : Nat} {term result : Term},
    normalise fuel term = some result → DerivableLatticeEta hypotheses term result := by
  intro fuel
  induction fuel with
  | zero =>
      intro term result normalised
      simp only [normalise] at normalised
      split at normalised
      · rw [Option.some.injEq] at normalised
        subst normalised
        exact .reflexive term
      · cases normalised
  | succ remaining remainingSound =>
      intro term result normalised
      simp only [normalise] at normalised
      split at normalised
      · rw [Option.some.injEq] at normalised
        subst normalised
        exact .reflexive term
      · next contracted stepped =>
          exact .transitive (stepSound stepped) (remainingSound normalised)

/-- Two terms that the normaliser takes to one term `normal`, with any fuels, are equal by
E ⊢_{λ-lattice-η} for every set E of hypotheses: each is equal to `normal` (`normaliseSound`),
and symmetry and transitivity join the two equations. -/
theorem derivableOfNormaliseEqual {leftFuel rightFuel : Nat} {left right normal : Term}
    (leftNormalised : normalise leftFuel left = some normal)
    (rightNormalised : normalise rightFuel right = some normal) :
    DerivableLatticeEta hypotheses left right :=
  .transitive (normaliseSound leftNormalised) (.symmetric (normaliseSound rightNormalised))

/-- Weak head reduction is sound: when `weakHead depth budget term` is `some (result, remaining)`,
E ⊢_{λ-lattice-η} term = result for every set E of hypotheses, by the β rule at each head redex
and the congruence in the function of an application around it. -/
theorem weakHeadSound : ∀ {depth budget : Nat} {term result : Term} {remaining : Nat},
    weakHead depth budget term = some (result, remaining) →
      DerivableLatticeEta hypotheses term result := by
  intro depth
  induction depth with
  | zero =>
      intro budget term result remaining reduced
      simp [weakHead] at reduced
  | succ depth depthSound =>
      intro budget term result remaining reduced
      cases term with
      | application function argument =>
          simp only [weakHead] at reduced
          split at reduced
          · rename_i body afterFunction functionReduced
            split at reduced
            · cases reduced
            · exact .transitive (.congruenceFunction argument (depthSound functionReduced))
                (.transitive (.beta body argument) (depthSound reduced))
          · rename_i head afterFunction _ functionReduced
            rw [Option.some.injEq, Prod.mk.injEq] at reduced
            obtain ⟨rfl, rfl⟩ := reduced
            exact .congruenceFunction argument (depthSound functionReduced)
          · cases reduced
      | boundVariable index =>
          simp only [weakHead, Option.some.injEq, Prod.mk.injEq] at reduced
          obtain ⟨rfl, rfl⟩ := reduced
          exact .reflexive _
      | abstraction body =>
          simp only [weakHead, Option.some.injEq, Prod.mk.injEq] at reduced
          obtain ⟨rfl, rfl⟩ := reduced
          exact .reflexive _
      | choice left right =>
          simp only [weakHead, Option.some.injEq, Prod.mk.injEq] at reduced
          obtain ⟨rfl, rfl⟩ := reduced
          exact .reflexive _
      | parallel left right =>
          simp only [weakHead, Option.some.injEq, Prod.mk.injEq] at reduced
          obtain ⟨rfl, rfl⟩ := reduced
          exact .reflexive _

/-- An abstraction is equal to its eta contraction (`etaContractumSound`), or to itself. -/
theorem etaAbstractionSound (body : Term) :
    DerivableLatticeEta hypotheses (abstraction body) (etaAbstraction body) := by
  unfold etaAbstraction
  split
  · rename_i contractum found
    exact etaContractumSound found
  · exact .reflexive _

/-- `normalForm` is sound: when `normalForm depth budget term` is `some (result, remaining)`,
E ⊢_{λ-lattice-η} term = result for every set E of hypotheses: the weak head reduction
(`weakHeadSound`), the congruences around the normal forms of the subterms, and the η rule at an
abstraction eta contracted (`etaAbstractionSound`). -/
theorem normalFormSound : ∀ {depth budget : Nat} {term result : Term} {remaining : Nat},
    normalForm depth budget term = some (result, remaining) →
      DerivableLatticeEta hypotheses term result := by
  intro depth
  induction depth with
  | zero =>
      intro budget term result remaining normalised
      simp [normalForm] at normalised
  | succ depth depthSound =>
      intro budget term result remaining normalised
      simp only [normalForm] at normalised
      split at normalised
      · rename_i body afterHead headReduced
        split at normalised
        · rename_i bodyNormal afterBody bodyNormalised
          rw [Option.some.injEq, Prod.mk.injEq] at normalised
          obtain ⟨rfl, rfl⟩ := normalised
          exact .transitive (weakHeadSound headReduced)
            (.transitive (.congruenceAbstraction (depthSound bodyNormalised))
              (etaAbstractionSound bodyNormal))
        · cases normalised
      · rename_i function argument afterHead headReduced
        split at normalised
        · rename_i functionNormal afterFunction functionNormalised
          split at normalised
          · rename_i argumentNormal afterArgument argumentNormalised
            rw [Option.some.injEq, Prod.mk.injEq] at normalised
            obtain ⟨rfl, rfl⟩ := normalised
            exact .transitive (weakHeadSound headReduced)
              (.transitive (.congruenceFunction argument (depthSound functionNormalised))
                (.congruenceArgument functionNormal (depthSound argumentNormalised)))
          · cases normalised
        · cases normalised
      · rename_i left right afterHead headReduced
        split at normalised
        · rename_i leftNormal afterLeft leftNormalised
          split at normalised
          · rename_i rightNormal afterRight rightNormalised
            rw [Option.some.injEq, Prod.mk.injEq] at normalised
            obtain ⟨rfl, rfl⟩ := normalised
            exact .transitive (weakHeadSound headReduced)
              (.congruenceChoice (depthSound leftNormalised) (depthSound rightNormalised))
          · cases normalised
        · cases normalised
      · rename_i left right afterHead headReduced
        split at normalised
        · rename_i leftNormal afterLeft leftNormalised
          split at normalised
          · rename_i rightNormal afterRight rightNormalised
            rw [Option.some.injEq, Prod.mk.injEq] at normalised
            obtain ⟨rfl, rfl⟩ := normalised
            exact .transitive (weakHeadSound headReduced)
              (.transitive (.congruenceParallelLeft right (depthSound leftNormalised))
                (.congruenceParallelRight leftNormal (depthSound rightNormalised)))
          · cases normalised
        · cases normalised
      · rename_i index afterHead headReduced
        rw [Option.some.injEq, Prod.mk.injEq] at normalised
        obtain ⟨rfl, rfl⟩ := normalised
        exact weakHeadSound headReduced
      · cases normalised

/-- `normalFormWithin` is sound (`normalFormSound`). -/
theorem normalFormWithinSound {fuel : Nat} {term result : Term}
    (normalised : normalFormWithin fuel term = some result) :
    DerivableLatticeEta hypotheses term result := by
  obtain ⟨⟨reached, remaining⟩, found, rfl⟩ := Option.map_eq_some_iff.mp normalised
  exact normalFormSound found

/-- Two terms that `normalFormWithin` takes to one term `normal`, with any fuels, are equal by
E ⊢_{λ-lattice-η} for every set E of hypotheses (`normalFormWithinSound`). -/
theorem derivableOfNormalFormWithinEqual {leftFuel rightFuel : Nat} {left right normal : Term}
    (leftNormalised : normalFormWithin leftFuel left = some normal)
    (rightNormalised : normalFormWithin rightFuel right = some normal) :
    DerivableLatticeEta hypotheses left right :=
  .transitive (normalFormWithinSound leftNormalised)
    (.symmetric (normalFormWithinSound rightNormalised))

end Soundness

/-! ## The result has no redex -/

/-- `step` misses no redex: when it answers `none`, no subterm of the term is a beta redex or an
eta redex. -/
theorem noRedexOfStepNone : ∀ {term : Term}, step term = none →
    EverySubterm (fun subterm => ¬ BetaRedex subterm ∧ ¬ EtaRedex subterm) term := by
  intro term
  induction term with
  | boundVariable index =>
      intro _
      refine ⟨?_, ?_⟩
      · rintro ⟨_, _, impossible⟩
        cases impossible
      · rintro ⟨_, impossible, _⟩
        cases impossible
  | abstraction body bodyNoRedex =>
      intro stepped
      simp only [step] at stepped
      split at stepped
      · cases stepped
      · next notFound =>
          refine ⟨⟨?_, ?_⟩, bodyNoRedex (Option.map_eq_none_iff.mp stepped)⟩
          · rintro ⟨_, _, impossible⟩
            cases impossible
          · rintro ⟨function, equal, absent⟩
            injection equal with bodyEqual
            subst bodyEqual
            have found := etaContractumEqualSome.mpr ⟨function, rfl, absent, rfl⟩
            rw [notFound] at found
            cases found
  | application function argument functionNoRedex argumentNoRedex =>
      intro stepped
      simp only [step] at stepped
      split at stepped
      · cases stepped
      · next notFound =>
          split at stepped
          · cases stepped
          · next functionNormal =>
              refine ⟨⟨?_, ?_⟩, functionNoRedex functionNormal,
                argumentNoRedex (Option.map_eq_none_iff.mp stepped)⟩
              · rintro ⟨body, _, equal⟩
                injection equal with functionEqual
                subst functionEqual
                simp [betaContractum] at notFound
              · rintro ⟨_, impossible, _⟩
                cases impossible
  | choice left right leftNoRedex rightNoRedex =>
      intro stepped
      simp only [step] at stepped
      split at stepped
      · cases stepped
      · next leftNormal =>
          refine ⟨⟨?_, ?_⟩, leftNoRedex leftNormal,
            rightNoRedex (Option.map_eq_none_iff.mp stepped)⟩
          · rintro ⟨_, _, impossible⟩
            cases impossible
          · rintro ⟨_, impossible, _⟩
            cases impossible
  | parallel left right leftNoRedex rightNoRedex =>
      intro stepped
      simp only [step] at stepped
      split at stepped
      · cases stepped
      · next leftNormal =>
          refine ⟨⟨?_, ?_⟩, leftNoRedex leftNormal,
            rightNoRedex (Option.map_eq_none_iff.mp stepped)⟩
          · rintro ⟨_, _, impossible⟩
            cases impossible
          · rintro ⟨_, impossible, _⟩
            cases impossible

/-- A result of the normaliser has no redex: none of its subterms is a beta redex or an eta
redex. -/
theorem normaliseNoRedex : ∀ {fuel : Nat} {term result : Term},
    normalise fuel term = some result →
      EverySubterm (fun subterm => ¬ BetaRedex subterm ∧ ¬ EtaRedex subterm) result := by
  intro fuel
  induction fuel with
  | zero =>
      intro term result normalised
      simp only [normalise] at normalised
      split at normalised
      · next normal =>
          rw [Option.some.injEq] at normalised
          subst normalised
          exact noRedexOfStepNone normal
      · cases normalised
  | succ remaining remainingNoRedex =>
      intro term result normalised
      simp only [normalise] at normalised
      split at normalised
      · next normal =>
          rw [Option.some.injEq] at normalised
          subst normalised
          exact noRedexOfStepNone normal
      · exact remainingNoRedex normalised

/-! ## Fixtures

Each fixture states the result of `normalise` and the kernel checks it by evaluation
(`decide`). The fuel of a fixture with a result is the number of contractions its docstring
describes; with one less fuel each gives `none` (measured 2026-10-04 with `#eval`, and checked
below for 2 + 2). Under `depth` abstractions, an index `depth + k` is the free variable k of the
term at the root. -/

namespace NormalisationFixtures

/-- λx. x. -/
def identity : Term := abstraction (boundVariable 0)

/-- (λx. x) (λy. y) normalises to λy. y, by one beta contraction. -/
example : normalise 1 (application identity identity) = some identity := by decide

/-- λx. (λy. y) x normalises to λy. y, by one eta contraction at the root: index 0 does not occur
free in the closed λy. y. -/
example : normalise 1 (abstraction (application identity (boundVariable 0))) = some identity := by
  decide

/-- λx. K x, with K = λx. λy. x (`first`) closed, normalises to K, by one eta contraction. -/
example : normalise 1 (abstraction (application first (boundVariable 0))) = some first := by
  decide

/-- λx. z x, with z free (index 1 under the binder), normalises to z, index 0 at the root: the eta
contraction lowers the free index. -/
example :
    normalise 1 (abstraction (application (boundVariable 1) (boundVariable 0))) =
      some (boundVariable 0) := by
  decide

/-- λx. x x has no redex: index 0 occurs free in the function x, so it is not an eta redex. -/
example : normalise 0 selfApplication = some selfApplication := by decide

/-- (λx. λy. x) z, with z free, normalises to λy. z: the beta contraction shifts z under the
binder of λy, where z is index 1. -/
example :
    normalise 1 (application first (boundVariable 0)) = some (abstraction (boundVariable 1)) := by
  decide

/-- (λx. λy. x y) z, with z free, normalises to z: a beta contraction at the root gives λy. z y,
then an eta contraction gives z. -/
example :
    normalise 2
        (application (abstraction (abstraction (application (boundVariable 1) (boundVariable 0))))
          (boundVariable 0)) =
      some (boundVariable 0) := by
  decide

/-- A choice under a binder: λx. ((λy. y) x + x) normalises to λx. (x + x). The redex inside the
choice is contracted; the choice itself is not (none of the numbered equations is used, so
x + x stays). -/
example :
    normalise 1 (abstraction (choice (application identity (boundVariable 0)) (boundVariable 0))) =
      some (abstraction (choice (boundVariable 0) (boundVariable 0))) := by
  decide

/-- The search reaches the right side of a choice: λx. (x + λy. x y) normalises to λx. (x + x), by
an eta contraction under two binders. -/
example :
    normalise 1
        (abstraction
          (choice (boundVariable 0) (abstraction (application (boundVariable 1) (boundVariable 0))))) =
      some (abstraction (choice (boundVariable 0) (boundVariable 0))) := by
  decide

/-- Both sides of a parallel: (λx. x) a ∥ (λx. x) b, with a and b free, normalises to a ∥ b in two
contractions, the left side first. -/
example :
    normalise 2
        (parallel (application identity (boundVariable 0)) (application identity (boundVariable 1))) =
      some (parallel (boundVariable 0) (boundVariable 1)) := by
  decide

/-- Ω has no normal form: its one redex contracts to Ω again, so the fuel runs out. -/
example : normalise 10 Omega = none := by decide

/-- The Church numeral two, λf. λx. f (f x). -/
def two : Term :=
  abstraction (abstraction (application (boundVariable 1)
    (application (boundVariable 1) (boundVariable 0))))

/-- The Church numeral four, λf. λx. f (f (f (f x))). -/
def four : Term :=
  abstraction (abstraction (application (boundVariable 1) (application (boundVariable 1)
    (application (boundVariable 1) (application (boundVariable 1) (boundVariable 0))))))

/-- Addition on Church numerals, λm. λn. λf. λx. m f (n f x). -/
def plus : Term :=
  abstraction (abstraction (abstraction (abstraction
    (application (application (boundVariable 3) (boundVariable 1))
      (application (application (boundVariable 2) (boundVariable 1)) (boundVariable 0))))))

/-- 2 + 2 normalises to 4, in six contractions. -/
example : normalise 6 (application (application plus two) two) = some four := by decide

/-- With fuel 5 the normaliser stops one contraction short of 4. -/
example : normalise 5 (application (application plus two) two) = none := by decide

/-- `normalFormWithin` takes 2 + 2 to 4 as well. -/
example : normalFormWithin 20 (application (application plus two) two) = some four := by decide

/-- `normalFormWithin` finds no normal form of Ω: each weak head contraction spends a unit of the
budget, and Ω contracts to itself. -/
example : normalFormWithin 10 Omega = none := by decide

/-- λx. z x, with z free, is eta contracted after its body is normal: z, index 0 at the root. -/
example :
    normalFormWithin 5 (abstraction (application (boundVariable 1) (boundVariable 0))) =
      some (boundVariable 0) := by
  decide

/-- Both sides of a choice under a binder are brought to normal form:
λx. ((λy. y) x + x) gives λx. (x + x). -/
example :
    normalFormWithin 5
        (abstraction (choice (application identity (boundVariable 0)) (boundVariable 0))) =
      some (abstraction (choice (boundVariable 0) (boundVariable 0))) := by
  decide

/-- (λx. x) (λy. y) and λx. (λy. y) x are equal by E ⊢_{λ-lattice-η} for every E: the normaliser takes both to
λy. y (`derivableOfNormaliseEqual`). -/
example (hypotheses : Term → Term → Prop) :
    DerivableLatticeEta hypotheses (application identity identity)
      (abstraction (application identity (boundVariable 0))) :=
  derivableOfNormaliseEqual (leftFuel := 1) (rightFuel := 1) (normal := identity) (by decide)
    (by decide)

/-- E ⊢_{λ-lattice-η} 2 + 2 = 4 for every E, by `normaliseSound`. -/
example (hypotheses : Term → Term → Prop) :
    DerivableLatticeEta hypotheses (application (application plus two) two) four :=
  normaliseSound (fuel := 6) (by decide)

end NormalisationFixtures

end LambdaJit.Semantics
