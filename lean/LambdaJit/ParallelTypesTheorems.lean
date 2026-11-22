import LambdaJit.LatticeEtaDerivability

/-!
# The lemmas of `parallel_types.pl` and `filtered_recursion_naturals.pl` as theorems of λ-lattice-η

The three lemmas of `gezi/corpora/standard_library/parallel_types.pl` and the four of
`gezi/corpora/standard_library/filtered_recursion_naturals.pl` are derived here from
no hypothesis by ⊢_{λ-lattice-η}, the relation `DerivableLatticeEta` of module `LatticeEtaDerivability`, on the terms
of Λ_{+∥} with de Bruijn indices (module `Terms`): `successorFiltered`, `successorFilteredChained`,
`naturalFoldFilteredContract`, `naturalFoldFilteredContractChained`,
`naturalFoldFilteredBranch`, `naturalFoldFilteredBranchInContext` and `naturalDoubleAsFold`, each
named after its lemma with `nat` written out as `natural`. An equation derivable by
⊢_{λ-lattice-η} with no hypothesis is a contextual equivalence
(`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`), so each of the seven is sound by
Definition 14. The paper proofs are the proofs file, sections 7 and 9; the proofs
here follow them step by step, and each theorem's docstring names the steps.

The docstrings of this module encode types, and write A ≤ B for the equation A + B = B: ≤ is the
converse of the order ⊑ of the proofs file (A ≤ B when B ⊑ A, that is A + B = B), read as subtyping, and "A refines B",
in the names of theorems and hypotheses, is A ≤ B as well.

What is trusted is how each library define is written as a term: the definitions below, each
with its file's text quoted, the choice `+` as `choice`, the parallel `∥` as `parallel`, and a
library name as that name's term. In a lemma, `@` is `application` and a two-element list is the
`choice` of its elements in order. A metavariable of a lemma is an argument of its theorem, and
any term, closed or open: no proof needs closedness.

The steps the paper leaves to the reader and that are lemmas here:

- The β rule with an argument that is a metavariable: the contractum carries the argument shifted under
  the binders it crosses, and module `Terms`' `substituteShiftFromCancel` (substituting into a
  shifted term gives the term back) and `shiftFromShiftFrom` (shifts commute) bring it back to the
  argument. The paper names its variables and needs neither.
- The equations of the library terms by the β rule: `zeroApply`, `successorApply`, `composeApply`,
  `filterNaturalApply`, `naturalFoldFilteredApply`, `naturalFoldApply`; the fixpoint equation,
  `fixpointUnfold`, whose left side contracts by the β rule twice to its right side, fixpoint being
  Turing's fixed point combinator; and
  `naturalTypeUnfold`, the paper's "nat_type 与 zero + successor nat_type 由 β 相等".
- The order facts of section 9's preamble: `refinesTransitive`, `choiceRefinesOfRefines`,
  `refinesChoiceRight`, `parallelRefinesLeft`, and `DerivableLatticeEta.parallelRefinesRight`, each read
  from its derivation without the unit law in section 6 (module `FourEquations`).
- The step shared by the four contracts, compose filter_nat F = F when F x ≤ nat_type for the
  variable x, by the β rule, T9 and the η rule: `composeFilterNaturalOfRefines`.

The theorems are about the terms of Λ_{+∥}. The lemma statements that
`gezi/prolog/gezi/lean_statements.pl` exports are article terms over the IR, where
`fixpoint` is an ordinary define whose layer is the IR of its body, one thunk applied to itself;
module `LibraryLemmaProofs` joins the interpretation of each of their sides (module
`Interpretation`) to the sides of the theorem here by a search that the kernel evaluates.
-/

namespace LambdaJit.ParallelTypesTheorems

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Shifting and substitution -/

/-- Substituting at index 1 into a term shifted twice removes one of the shifts. -/
theorem substituteOneShiftTwice (term replacement : Term) :
    substitute 1 replacement (shift (shift term)) = shift term := by
  have raised : shift (shift term) = shiftFrom 1 (shift term) :=
    shiftFromShiftFrom term 0 0 (Nat.le_refl 0)
  rw [raised]
  exact substituteShiftFromCancel (shift term) 1 replacement

/-- Substituting at index 2 into a term shifted three times removes one of the shifts. -/
theorem substituteTwoShiftThrice (term replacement : Term) :
    substitute 2 replacement (shift (shift (shift term))) = shift (shift term) := by
  have raisedOnce : shiftFrom 1 (shift term) = shift (shift term) :=
    (shiftFromShiftFrom term 0 0 (Nat.le_refl 0)).symm
  have raised : shift (shift (shift term)) = shiftFrom 2 (shift (shift term)) := by
    have commuted := shiftFromShiftFrom (shift term) 1 0 (Nat.zero_le 1)
    -- commuted : shiftFrom 0 (shiftFrom 1 (shift term)) = shiftFrom 2 (shiftFrom 0 (shift term))
    rw [raisedOnce] at commuted
    exact commuted
  rw [raised]
  exact substituteShiftFromCancel (shift (shift term)) 2 replacement

/-- `freeIndicesBelow bound term`: every index that occurs free in `term`, counted at the root
of `term`, is below `bound`. A computable test, so that the closedness of a concrete term is
proved by evaluation. -/
def freeIndicesBelow : Nat → Term → Bool
  | bound, boundVariable index => decide (index < bound)
  | bound, abstraction body => freeIndicesBelow (bound + 1) body
  | bound, application function argument =>
      freeIndicesBelow bound function && freeIndicesBelow bound argument
  | bound, choice left right => freeIndicesBelow bound left && freeIndicesBelow bound right
  | bound, parallel left right => freeIndicesBelow bound left && freeIndicesBelow bound right

/-- The test `freeIndicesBelow` is sound: no index at or above `bound` occurs free. -/
theorem notOccursFreeOfFreeIndicesBelow : ∀ (term : Term) (bound : Nat),
    freeIndicesBelow bound term = true → ∀ index, bound ≤ index → ¬ OccursFree index term
  | boundVariable other, bound, tested, index, atOrAbove, occurs => by
      simp only [freeIndicesBelow, decide_eq_true_eq] at tested
      simp only [OccursFree] at occurs
      omega
  | abstraction body, bound, tested, index, atOrAbove, occurs => by
      simp only [freeIndicesBelow] at tested
      simp only [OccursFree] at occurs
      exact notOccursFreeOfFreeIndicesBelow body (bound + 1) tested (index + 1) (by omega) occurs
  | application function argument, bound, tested, index, atOrAbove, occurs => by
      simp only [freeIndicesBelow, Bool.and_eq_true] at tested
      simp only [OccursFree] at occurs
      rcases occurs with inFunction | inArgument
      · exact notOccursFreeOfFreeIndicesBelow function bound tested.1 index atOrAbove inFunction
      · exact notOccursFreeOfFreeIndicesBelow argument bound tested.2 index atOrAbove inArgument
  | choice left right, bound, tested, index, atOrAbove, occurs => by
      simp only [freeIndicesBelow, Bool.and_eq_true] at tested
      simp only [OccursFree] at occurs
      rcases occurs with inLeft | inRight
      · exact notOccursFreeOfFreeIndicesBelow left bound tested.1 index atOrAbove inLeft
      · exact notOccursFreeOfFreeIndicesBelow right bound tested.2 index atOrAbove inRight
  | parallel left right, bound, tested, index, atOrAbove, occurs => by
      simp only [freeIndicesBelow, Bool.and_eq_true] at tested
      simp only [OccursFree] at occurs
      rcases occurs with inLeft | inRight
      · exact notOccursFreeOfFreeIndicesBelow left bound tested.1 index atOrAbove inLeft
      · exact notOccursFreeOfFreeIndicesBelow right bound tested.2 index atOrAbove inRight

/-- A term whose free indices are all below 0 is closed. -/
theorem closedOfFreeIndicesBelow {term : Term} (tested : freeIndicesBelow 0 term = true) :
    Closed term :=
  fun index => notOccursFreeOfFreeIndicesBelow term 0 tested index (Nat.zero_le index)

/-- Substitution leaves a closed term unchanged. -/
theorem substituteClosed {term : Term} (closed : Closed term) (depth : Nat)
    (replacement : Term) : substitute depth replacement term = term :=
  substituteUnchanged term depth replacement (fun index _ => closed index)

/-! ## The library defines as terms

Each define is its file's text read as a term of Λ_{+∥} with de Bruijn indices: the choice `+` is
`choice`, the parallel `∥` is `parallel`, and every library name the text leaves free is replaced by
that name's own term, the Lean definition of the same name below. There is no delta step: a
library name is a label on its term, so the name is its body. -/

/-- The define `zero`, the Scott numeral zero. Its file,
`gezi/corpora/standard_library/prelude/zero.lambdalattice`, reads:

    λz.λ_.z
-/
def zero : Term := abstraction (abstraction (boundVariable 1))

/-- The define `successor`, the Scott successor. Its file,
`gezi/corpora/standard_library/prelude/successor.lambdalattice`, reads:

    λn.λ_.λs.s n
-/
def successor : Term :=
  abstraction (abstraction (abstraction (application (boundVariable 0) (boundVariable 2))))

/-- The define `compose`. Its file,
`gezi/corpora/standard_library/prelude/compose.lambdalattice`, reads:

    λf.λg.λx.f (g x)
-/
def compose : Term :=
  abstraction (abstraction (abstraction
    (application (boundVariable 2) (application (boundVariable 1) (boundVariable 0)))))

/-- The term that `fixpoint` applies to itself:

    λx.λf.f (x x f)
-/
def fixpointHalf : Term :=
  abstraction (abstraction
    (application (boundVariable 0)
      (application (application (boundVariable 1) (boundVariable 1)) (boundVariable 0))))

/-- The define `fixpoint`, Turing's fixed point combinator, `fixpointHalf` applied to itself.
Its file, `gezi/corpora/standard_library/prelude/fixpoint.lambdalattice`, reads:

    (λx.λf.f (x x f)) (λx.λf.f (x x f))
-/
def fixpoint : Term := application fixpointHalf fixpointHalf

/-- The define `nat_type`, with `fixpoint`, `zero` and `successor` replaced by their terms. Its
file, `gezi/corpora/standard_library/parallel_types/nat_type.lambdalattice`, reads:

    % The type of the Scott naturals as a choice: every numeral is in
    % NF◇_{λ-lattice-unit-η}(nat_type), and NF◇_{λ-lattice-unit-η}(x ∥ nat_type) is
    % contained in NF◇_{λ-lattice-unit-η}(x) ∩ NF◇_{λ-lattice-unit-η}(nat_type)
    % (the proofs file). FIXME: that nothing else is in https://github.com/Atry/private-overlay/issues/2013
    % NF◇_{λ-lattice-unit-η}(nat_type) is not yet proved.
    fixpoint (λn. zero + successor n)
-/
def naturalType : Term :=
  application fixpoint (abstraction (choice zero (application successor (boundVariable 0))))

/-- The define `filter_nat`, with `nat_type` replaced by its term. Its file,
`gezi/corpora/standard_library/parallel_types/filter_nat.lambdalattice`, reads:

    % The filter of the naturals: λx. x ∥ nat_type.
    λx. x ∥ nat_type
-/
def filterNatural : Term := abstraction (parallel (boundVariable 0) naturalType)

/-- The define `nat_fold`, with `fixpoint` replaced by its term. Its file,
`gezi/corpora/standard_library/parallel_types/nat_fold.lambdalattice`, reads:

    % Structural recursion over a Scott natural, with no filter:
    % nat_fold z s n is s (s (... (s z))), n times.
    λz.λs. fixpoint (λself.λn. n z (λp. s (self p)))
-/
def naturalFold : Term :=
  abstraction (abstraction (application fixpoint
    (abstraction (abstraction
      (application (application (boundVariable 0) (boundVariable 3))
        (abstraction
          (application (boundVariable 3) (application (boundVariable 2) (boundVariable 0)))))))))

/-- The define `nat_fold_filtered`, with `nat_fold`, `filter_nat` and `compose` replaced by their
terms. Its file,
`gezi/corpora/standard_library/parallel_types/nat_fold_filtered.lambdalattice`, reads:

    % Structural recursion with the base and every step filtered by nat_type.
    λz.λs. nat_fold (filter_nat z) (compose filter_nat (compose s filter_nat))
-/
def naturalFoldFiltered : Term :=
  abstraction (abstraction
    (application (application naturalFold (application filterNatural (boundVariable 1)))
      (application (application compose filterNatural)
        (application (application compose (boundVariable 0)) filterNatural))))

/-- The define `natural_double`, with `fixpoint`, `zero` and `successor` replaced by their terms.
Its file, `gezi/corpora/standard_library/prelude/natural_double.lambdalattice`, reads:

    fixpoint (λself.λn.n zero (λn1.successor (successor (self n1))))
-/
def naturalDouble : Term :=
  application fixpoint (abstraction (abstraction
    (application (application (boundVariable 0) zero)
      (abstraction (application successor
        (application successor (application (boundVariable 2) (boundVariable 0))))))))

/-! Each library term that a substitution below meets is closed, by evaluating
`freeIndicesBelow`. -/

theorem closedZero : Closed zero := closedOfFreeIndicesBelow rfl
theorem closedSuccessor : Closed successor := closedOfFreeIndicesBelow rfl
theorem closedCompose : Closed compose := closedOfFreeIndicesBelow rfl
theorem closedFixpoint : Closed fixpoint := closedOfFreeIndicesBelow rfl
theorem closedNaturalType : Closed naturalType := closedOfFreeIndicesBelow rfl
theorem closedFilterNatural : Closed filterNatural := closedOfFreeIndicesBelow rfl
theorem closedNaturalFold : Closed naturalFold := closedOfFreeIndicesBelow rfl

/-! Substitution leaves each of these terms unchanged, since it is closed; the contractions
of the β rule below rewrite with these equations. A shift of a closed library term, which leaves it
unchanged too, is left to evaluation where a proof states the shifted term. -/

theorem substituteZero (depth : Nat) (replacement : Term) :
    substitute depth replacement zero = zero :=
  substituteClosed closedZero depth replacement
theorem substituteSuccessor (depth : Nat) (replacement : Term) :
    substitute depth replacement successor = successor :=
  substituteClosed closedSuccessor depth replacement
theorem substituteCompose (depth : Nat) (replacement : Term) :
    substitute depth replacement compose = compose :=
  substituteClosed closedCompose depth replacement
theorem substituteFixpoint (depth : Nat) (replacement : Term) :
    substitute depth replacement fixpoint = fixpoint :=
  substituteClosed closedFixpoint depth replacement
theorem substituteNaturalType (depth : Nat) (replacement : Term) :
    substitute depth replacement naturalType = naturalType :=
  substituteClosed closedNaturalType depth replacement
theorem substituteFilterNatural (depth : Nat) (replacement : Term) :
    substitute depth replacement filterNatural = filterNatural :=
  substituteClosed closedFilterNatural depth replacement
theorem substituteNaturalFold (depth : Nat) (replacement : Term) :
    substitute depth replacement naturalFold = naturalFold :=
  substituteClosed closedNaturalFold depth replacement

/-! ## Equations of the library terms, by the β rule -/

section Combinators

variable {hypotheses : Term → Term → Prop}

/-- The β rule with its contractum given: (λx. M) N = R when M[x := N] is R. -/
theorem betaTo {body argument result : Term} (contracted : instantiate body argument = result) :
    DerivableLatticeEta hypotheses (application (abstraction body) argument) result := by
  rw [← contracted]
  exact .beta body argument

/-- zero z k = z. -/
theorem zeroApply (base continuation : Term) :
    DerivableLatticeEta hypotheses (application (application zero base) continuation) base :=
  .transitive
    (.congruenceFunction continuation
      (betaTo (body := abstraction (boundVariable 1)) (argument := base)
        (result := abstraction (shift base)) rfl))
    (betaTo (substituteShift base continuation))

/-- successor n z k = k n. -/
theorem successorApply (predecessor base continuation : Term) :
    DerivableLatticeEta hypotheses
      (application (application (application successor predecessor) base) continuation)
      (application continuation predecessor) := by
  have first : DerivableLatticeEta hypotheses (application successor predecessor)
      (abstraction (abstraction
        (application (boundVariable 0) (shift (shift predecessor))))) :=
    betaTo rfl
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction
        (application (boundVariable 0) (shift (shift predecessor))))) base)
      (abstraction (application (boundVariable 0) (shift predecessor))) := by
    apply betaTo
    show abstraction (application (boundVariable 0)
      (substitute 1 (shift base) (shift (shift predecessor)))) = _
    rw [substituteOneShiftTwice]
  have third : DerivableLatticeEta hypotheses
      (application (abstraction (application (boundVariable 0) (shift predecessor)))
        continuation)
      (application continuation predecessor) := by
    apply betaTo
    show application continuation (substitute 0 continuation (shift predecessor)) = _
    rw [substituteShift]
  exact .transitive (.congruenceFunction continuation (.congruenceFunction base first))
    (.transitive (.congruenceFunction continuation second) third)

/-- compose f g x = f (g x). -/
theorem composeApply (outer inner argument : Term) :
    DerivableLatticeEta hypotheses (application (application (application compose outer) inner) argument)
      (application outer (application inner argument)) := by
  have first : DerivableLatticeEta hypotheses (application compose outer)
      (abstraction (abstraction (application (shift (shift outer))
        (application (boundVariable 1) (boundVariable 0))))) :=
    betaTo rfl
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction (application (shift (shift outer))
        (application (boundVariable 1) (boundVariable 0))))) inner)
      (abstraction (application (shift outer) (application (shift inner) (boundVariable 0)))) := by
    apply betaTo
    show abstraction (application (substitute 1 (shift inner) (shift (shift outer)))
      (application (shift inner) (boundVariable 0))) = _
    rw [substituteOneShiftTwice]
  have third : DerivableLatticeEta hypotheses
      (application
        (abstraction (application (shift outer) (application (shift inner) (boundVariable 0))))
        argument)
      (application outer (application inner argument)) := by
    apply betaTo
    show application (substitute 0 argument (shift outer))
      (application (substitute 0 argument (shift inner)) argument) = _
    rw [substituteShift, substituteShift]
  exact .transitive (.congruenceFunction argument (.congruenceFunction inner first))
    (.transitive (.congruenceFunction argument second) third)

/-- The fixpoint equation: fixpoint f = f (fixpoint f). The term fixpoint is A A with
A = λx.λf. f (x x f); the β rule contracts A A to λf. f (A A f), and the β rule again contracts
that applied to f to f (A A f), which is f (fixpoint f). -/
theorem fixpointUnfold (function : Term) :
    DerivableLatticeEta hypotheses (application fixpoint function)
      (application function (application fixpoint function)) := by
  have halfApplied : DerivableLatticeEta hypotheses fixpoint
      (abstraction (application (boundVariable 0) (application fixpoint (boundVariable 0)))) :=
    betaTo rfl
  have unfolded : DerivableLatticeEta hypotheses
      (application
        (abstraction (application (boundVariable 0) (application fixpoint (boundVariable 0))))
        function)
      (application function (application fixpoint function)) := by
    apply betaTo
    show application function (application (substitute 0 function fixpoint) function) = _
    rw [substituteFixpoint]
  exact .transitive (.congruenceFunction function halfApplied) unfolded

/-- filter_nat x = x ∥ nat_type. -/
theorem filterNaturalApply (argument : Term) :
    DerivableLatticeEta hypotheses (application filterNatural argument) (parallel argument naturalType) := by
  apply betaTo
  show parallel argument (substitute 0 argument naturalType) = _
  rw [substituteNaturalType]

/-- nat_type = zero + successor nat_type, by the fixpoint equation and the β rule. -/
theorem naturalTypeUnfold :
    DerivableLatticeEta hypotheses naturalType (choice zero (application successor naturalType)) := by
  have unfolded := fixpointUnfold (hypotheses := hypotheses)
    (abstraction (choice zero (application successor (boundVariable 0))))
  have contracted : DerivableLatticeEta hypotheses
      (application (abstraction (choice zero (application successor (boundVariable 0))))
        naturalType)
      (choice zero (application successor naturalType)) := by
    apply betaTo
    show choice (substitute 0 naturalType zero)
      (application (substitute 0 naturalType successor) naturalType) = _
    rw [substituteZero, substituteSuccessor]
  exact .transitive unfolded contracted

end Combinators

/-! ## The structural recursion `nat_fold` and its filtered branch, by the β rule -/

section Recursion

variable {hypotheses : Term → Term → Prop}

/-- The term that `nat_fold z s` contracts to by the β rule twice,
fixpoint (λself.λn. n z (λp. s (self p))) with `base` and `step` placed under the binders. -/
def naturalFoldFixpoint (base step : Term) : Term :=
  application fixpoint (abstraction (abstraction
    (application (application (boundVariable 0) (shift (shift base)))
      (abstraction (application (shift (shift (shift step)))
        (application (boundVariable 2) (boundVariable 0)))))))

/-- nat_fold z s = fixpoint (λself.λn. n z (λp. s (self p))), by the β rule twice. -/
theorem naturalFoldToFixpoint (base step : Term) :
    DerivableLatticeEta hypotheses (application (application naturalFold base) step)
      (naturalFoldFixpoint base step) := by
  have first : DerivableLatticeEta hypotheses (application naturalFold base)
      (abstraction (application fixpoint (abstraction (abstraction
        (application (application (boundVariable 0) (shift (shift (shift base))))
          (abstraction (application (boundVariable 3)
            (application (boundVariable 2) (boundVariable 0))))))))) := by
    apply betaTo
    show abstraction (application (substitute 1 (shift base) fixpoint)
      (abstraction (abstraction
        (application (application (boundVariable 0) (shift (shift (shift base))))
          (abstraction (application (boundVariable 3)
            (application (boundVariable 2) (boundVariable 0)))))))) = _
    rw [substituteFixpoint]
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (application fixpoint (abstraction (abstraction
        (application (application (boundVariable 0) (shift (shift (shift base))))
          (abstraction (application (boundVariable 3)
            (application (boundVariable 2) (boundVariable 0))))))))) step)
      (naturalFoldFixpoint base step) := by
    apply betaTo
    show application (substitute 0 step fixpoint) (abstraction (abstraction
        (application (application (boundVariable 0)
          (substitute 2 (shift (shift step)) (shift (shift (shift base)))))
          (abstraction (application (shift (shift (shift step)))
            (application (boundVariable 2) (boundVariable 0))))))) = _
    rw [substituteFixpoint, substituteTwoShiftThrice]
    rfl
  exact .transitive (.congruenceFunction step first) second

/-- nat_fold z s y = y z (λp. s (r p)), r being `naturalFoldFixpoint z s`: the β rule twice, the
fixpoint equation, and the β rule twice more. -/
theorem naturalFoldApply (base step argument : Term) :
    DerivableLatticeEta hypotheses
      (application (application (application naturalFold base) step) argument)
      (application (application argument base)
        (abstraction (application (shift step)
          (application (shift (naturalFoldFixpoint base step)) (boundVariable 0))))) := by
  have unfolded := fixpointUnfold (hypotheses := hypotheses) (abstraction (abstraction
    (application (application (boundVariable 0) (shift (shift base)))
      (abstraction (application (shift (shift (shift step)))
        (application (boundVariable 2) (boundVariable 0)))))))
  have stepContracted : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction
        (application (application (boundVariable 0) (shift (shift base)))
          (abstraction (application (shift (shift (shift step)))
            (application (boundVariable 2) (boundVariable 0)))))))
        (naturalFoldFixpoint base step))
      (abstraction (application (application (boundVariable 0) (shift base))
        (abstraction (application (shift (shift step))
          (application (shift (shift (naturalFoldFixpoint base step))) (boundVariable 0)))))) := by
    apply betaTo
    show abstraction (application (application (boundVariable 0)
        (substitute 1 (shift (naturalFoldFixpoint base step)) (shift (shift base))))
      (abstraction (application
        (substitute 2 (shift (shift (naturalFoldFixpoint base step))) (shift (shift (shift step))))
        (application (shift (shift (naturalFoldFixpoint base step))) (boundVariable 0))))) = _
    rw [substituteOneShiftTwice, substituteTwoShiftThrice]
  have argumentContracted : DerivableLatticeEta hypotheses
      (application (abstraction (application (application (boundVariable 0) (shift base))
        (abstraction (application (shift (shift step))
          (application (shift (shift (naturalFoldFixpoint base step))) (boundVariable 0))))))
        argument)
      (application (application argument base)
        (abstraction (application (shift step)
          (application (shift (naturalFoldFixpoint base step)) (boundVariable 0))))) := by
    apply betaTo
    show application (application argument (substitute 0 argument (shift base)))
      (abstraction (application (substitute 1 (shift argument) (shift (shift step)))
        (application (substitute 1 (shift argument) (shift (shift (naturalFoldFixpoint base step))))
          (boundVariable 0)))) = _
    rw [substituteShift, substituteOneShiftTwice, substituteOneShiftTwice]
  exact .transitive (.congruenceFunction argument (naturalFoldToFixpoint base step))
    (.transitive (.congruenceFunction argument unfolded)
      (.transitive (.congruenceFunction argument stepContracted) argumentContracted))

/-- (λp. s (r p)) w = s (r w), for the shifted s and r that `naturalFoldApply` gives, by the β rule. -/
theorem continuationApply (step recursion argument : Term) :
    DerivableLatticeEta hypotheses
      (application (abstraction (application (shift step)
        (application (shift recursion) (boundVariable 0)))) argument)
      (application step (application recursion argument)) := by
  apply betaTo
  show application (substitute 0 argument (shift step))
    (application (substitute 0 argument (shift recursion)) argument) = _
  rw [substituteShift, substituteShift]

/-- nat_fold_filtered z s = nat_fold (filter_nat z) (compose filter_nat (compose s filter_nat)),
by the β rule twice. -/
theorem naturalFoldFilteredApply (base step : Term) :
    DerivableLatticeEta hypotheses (application (application naturalFoldFiltered base) step)
      (application (application naturalFold (application filterNatural base))
        (application (application compose filterNatural)
          (application (application compose step) filterNatural))) := by
  have first : DerivableLatticeEta hypotheses (application naturalFoldFiltered base)
      (abstraction
        (application (application naturalFold (application filterNatural (shift base)))
          (application (application compose filterNatural)
            (application (application compose (boundVariable 0)) filterNatural)))) := by
    apply betaTo
    show abstraction (application
        (application (substitute 1 (shift base) naturalFold)
          (application (substitute 1 (shift base) filterNatural) (shift base)))
        (application
          (application (substitute 1 (shift base) compose)
            (substitute 1 (shift base) filterNatural))
          (application (application (substitute 1 (shift base) compose) (boundVariable 0))
            (substitute 1 (shift base) filterNatural)))) = _
    rw [substituteNaturalFold, substituteFilterNatural, substituteCompose]
  have second : DerivableLatticeEta hypotheses
      (application (abstraction
        (application (application naturalFold (application filterNatural (shift base)))
          (application (application compose filterNatural)
            (application (application compose (boundVariable 0)) filterNatural)))) step)
      (application (application naturalFold (application filterNatural base))
        (application (application compose filterNatural)
          (application (application compose step) filterNatural))) := by
    apply betaTo
    show application
        (application (substitute 0 step naturalFold)
          (application (substitute 0 step filterNatural) (substitute 0 step (shift base))))
        (application
          (application (substitute 0 step compose) (substitute 0 step filterNatural))
          (application (application (substitute 0 step compose) step)
            (substitute 0 step filterNatural))) = _
    rw [substituteNaturalFold, substituteFilterNatural, substituteCompose, substituteShift]
  exact .transitive (.congruenceFunction step first) second

end Recursion

/-! ## The order A ≤ B, that is the equation A + B = B

A ≤ B, the converse of ⊑ as the module docstring says, and "A refines B" in the names stand for
the equation A + B = B; the theory has no such relation, only the equation. -/

section Order

variable {hypotheses : Term → Term → Prop}

/-- A ≤ B and B ≤ C give A ≤ C: section 6's lemma (iv), by (1), (3), (5), (10) and the β rule
(`DerivableLatticeEta.refinesTransitive`). -/
theorem refinesTransitive {lower middle upper : Term}
    (lowerRefinesMiddle : DerivableLatticeEta hypotheses (choice lower middle) middle)
    (middleRefinesUpper : DerivableLatticeEta hypotheses (choice middle upper) upper) :
    DerivableLatticeEta hypotheses (choice lower upper) upper :=
  DerivableLatticeEta.refinesTransitive lowerRefinesMiddle middleRefinesUpper

/-- A ≤ C and B ≤ C give A + B ≤ C: section 6's step 庚, lemma (iii), by (1), (10) and the β rule
(`FourEquations.DerivableFrom.choiceRefinesByCommutative`). -/
theorem choiceRefinesOfRefines {left right upper : Term}
    (leftRefines : DerivableLatticeEta hypotheses (choice left upper) upper)
    (rightRefines : DerivableLatticeEta hypotheses (choice right upper) upper) :
    DerivableLatticeEta hypotheses (choice (choice left right) upper) upper :=
  DerivableLatticeEta.ofDerivableFrom (FourEquations.DerivableFrom.choiceRefinesByCommutative
    (fun first second => .law (DerivableLatticeEta.equationOne first second))
    DerivableLatticeEta.equationTen (.law leftRefines) (.law rightRefines))

/-- B ≤ A + B: the second half of section 6's lemma (ii), by (1), (3), (5), (10) and the β rule
(`FourEquations.DerivableFrom.rightRefinesChoiceWithoutUnitLaw`). -/
theorem refinesChoiceRight (left right : Term) :
    DerivableLatticeEta hypotheses (choice right (choice left right)) (choice left right) :=
  DerivableLatticeEta.ofDerivableFrom (FourEquations.DerivableFrom.rightRefinesChoiceWithoutUnitLaw
    DerivableLatticeEta.equationOne DerivableLatticeEta.equationThree
    DerivableLatticeEta.equationFive DerivableLatticeEta.equationTen right left)

/-- A parallel refines its left side, (M ∥ N) + M = M, by (1) and (6), the first half of section 6's
lemma (vi) (`DerivableLatticeEta.parallelRefinesLeft`). -/
theorem parallelRefinesLeft (left right : Term) :
    DerivableLatticeEta hypotheses (choice (parallel left right) left) left :=
  DerivableLatticeEta.parallelRefinesLeft left right

/-- A ≤ B with A replaced by a term equal to it. -/
theorem refinesOfEqualLower {lower lowerEqual upper : Term}
    (equal : DerivableLatticeEta hypotheses lower lowerEqual)
    (refines : DerivableLatticeEta hypotheses (choice lowerEqual upper) upper) :
    DerivableLatticeEta hypotheses (choice lower upper) upper :=
  .transitive (.congruenceChoiceLeft upper equal) refines

/-- A ≤ B with B replaced by a term equal to it. -/
theorem refinesOfEqualUpper {lower upper upperEqual : Term}
    (refines : DerivableLatticeEta hypotheses (choice lower upper) upper)
    (equal : DerivableLatticeEta hypotheses upper upperEqual) :
    DerivableLatticeEta hypotheses (choice lower upperEqual) upperEqual :=
  .transitive (.congruenceChoiceRight lower (.symmetric equal)) (.transitive refines equal)

end Order

/-! ## Refining the type of the naturals -/

section Filters

variable {hypotheses : Term → Term → Prop}

/-- successor (x ∥ nat_type) ≤ nat_type, for every term x: x ∥ nat_type ≤ nat_type by (1), (3)
and (6), so successor (x ∥ nat_type) ≤ successor nat_type by (10) (T10's argument case); and
successor nat_type ≤ zero + successor nat_type = nat_type by (1), (2), T1 and the fixpoint
equation. -/
theorem successorFilteredRefines (argument : Term) :
    DerivableLatticeEta hypotheses
      (choice (application successor (parallel argument naturalType)) naturalType) naturalType := by
  have filteredRefines : DerivableLatticeEta hypotheses
      (choice (application successor (parallel argument naturalType))
        (application successor naturalType))
      (application successor naturalType) :=
    DerivableLatticeEta.contextMonotone (DerivableLatticeEta.parallelRefinesRight argument naturalType)
      (.applicationArgument successor .hole)
  have successorRefines : DerivableLatticeEta hypotheses
      (choice (application successor naturalType) naturalType) naturalType :=
    refinesOfEqualUpper (refinesChoiceRight zero (application successor naturalType))
      (.symmetric naturalTypeUnfold)
  exact refinesTransitive filteredRefines successorRefines

/-- The output filter is redundant when the output refines nat_type: compose filter_nat f = f
when f x ≤ nat_type for the variable x. Under the binder of λx, x is index 0 and f is
`shift function`. compose filter_nat f = λx. filter_nat (f x) by the β rule, = λx. f x ∥ nat_type by the β rule,
= λx. f x by T9, = f by the η rule. -/
theorem composeFilterNaturalOfRefines (function : Term)
    (refines : DerivableLatticeEta hypotheses
      (choice (application (shift function) (boundVariable 0)) naturalType) naturalType) :
    DerivableLatticeEta hypotheses (application (application compose filterNatural) function) function := by
  have first : DerivableLatticeEta hypotheses (application compose filterNatural)
      (abstraction (abstraction (application filterNatural
        (application (boundVariable 1) (boundVariable 0))))) :=
    betaTo rfl
  have second : DerivableLatticeEta hypotheses
      (application (abstraction (abstraction (application filterNatural
        (application (boundVariable 1) (boundVariable 0))))) function)
      (abstraction
        (application filterNatural (application (shift function) (boundVariable 0)))) := by
    apply betaTo
    show abstraction (application (substitute 1 (shift function) filterNatural)
      (application (shift function) (boundVariable 0))) = _
    rw [substituteFilterNatural]
  have filtered : DerivableLatticeEta hypotheses
      (application filterNatural (application (shift function) (boundVariable 0)))
      (application (shift function) (boundVariable 0)) :=
    .transitive (filterNaturalApply _) (DerivableLatticeEta.parallelOfRefines refines)
  exact .transitive (.congruenceFunction function first)
    (.transitive second
      (.transitive (.congruenceAbstraction filtered) (.eta function)))

/-- nat_fold_filtered z s (y ∥ nat_type) ≤ nat_type, for all terms z, s and y. With
Z′ = filter_nat z and S′ = compose filter_nat (compose s filter_nat), nat_fold_filtered z s is
nat_fold Z′ S′ by the β rule, and nat_fold Z′ S′ y = y Z′ K′ by the β rule and the fixpoint
equation, with K′ = λp. S′ (r p), r being `naturalFoldFixpoint Z′ S′`. Then
(y ∥ nat_type) Z′ K′ = (y Z′ K′) ∥ (nat_type Z′ K′) by (9) twice, which refines
nat_type Z′ K′ by (1), (3) and (6); and nat_type Z′ K′ = Z′ + S′ (r nat_type) by the fixpoint
equation, (8) twice and the β rule, where Z′ = z ∥ nat_type and S′ w = (compose s filter_nat w) ∥ nat_type
each refine nat_type. No induction. The steps above do not cite (10); the formal definition
derives the numbered equations they cite, and the order facts, from axioms that include (10)
(module `FourEquations`). -/
theorem naturalFoldFilteredRefines (base step argument : Term) :
    DerivableLatticeEta hypotheses
      (choice (application (application (application naturalFoldFiltered base) step)
        (parallel argument naturalType)) naturalType) naturalType := by
  let filteredBase := application filterNatural base
  let filteredStep := application (application compose filterNatural)
    (application (application compose step) filterNatural)
  let continuation := abstraction (application (shift filteredStep)
    (application (shift (naturalFoldFixpoint filteredBase filteredStep)) (boundVariable 0)))
  have unfolded : DerivableLatticeEta hypotheses
      (application (application (application naturalFoldFiltered base) step)
        (parallel argument naturalType))
      (application (application (parallel argument naturalType) filteredBase) continuation) :=
    .transitive (.congruenceFunction _ (naturalFoldFilteredApply base step))
      (naturalFoldApply filteredBase filteredStep _)
  have distributed : DerivableLatticeEta hypotheses
      (application (application (parallel argument naturalType) filteredBase) continuation)
      (parallel (application (application argument filteredBase) continuation)
        (application (application naturalType filteredBase) continuation)) :=
    .transitive (.congruenceFunction continuation (.parallelFunctionDistributive _ _ _))
      (.parallelFunctionDistributive _ _ _)
  have typeUnfolded : DerivableLatticeEta hypotheses
      (application (application naturalType filteredBase) continuation)
      (choice filteredBase (application filteredStep
        (application (naturalFoldFixpoint filteredBase filteredStep) naturalType))) :=
    .transitive
      (.congruenceFunction continuation (.congruenceFunction filteredBase naturalTypeUnfold))
      (.transitive (.congruenceFunction continuation (.choiceFunctionDistributive _ _ _))
        (.transitive (.choiceFunctionDistributive _ _ _)
          (DerivableLatticeEta.congruenceChoice (zeroApply _ _)
            (.transitive (successorApply _ _ _) (continuationApply _ _ _)))))
  have baseRefines : DerivableLatticeEta hypotheses (choice filteredBase naturalType) naturalType :=
    refinesOfEqualLower (filterNaturalApply base) (DerivableLatticeEta.parallelRefinesRight base naturalType)
  have stepRefines : ∀ value, DerivableLatticeEta hypotheses
      (choice (application filteredStep value) naturalType) naturalType := fun value =>
    refinesOfEqualLower
      (.transitive (composeApply _ _ value) (filterNaturalApply _))
      (DerivableLatticeEta.parallelRefinesRight _ naturalType)
  have typeRefines : DerivableLatticeEta hypotheses
      (choice (application (application naturalType filteredBase) continuation) naturalType)
      naturalType :=
    refinesOfEqualLower typeUnfolded (choiceRefinesOfRefines baseRefines (stepRefines _))
  exact refinesOfEqualLower (.transitive unfolded distributed)
    (refinesTransitive (DerivableLatticeEta.parallelRefinesRight _ _) typeRefines)

/-- The filtered step refines the step, compose filter_nat (compose s filter_nat) ≤ s: for the
variable w, (s (w ∥ nat_type)) ∥ nat_type ≤ s (w ∥ nat_type) by (1) and (6), and
s (w ∥ nat_type) ≤ s w by (10) (T10's argument case) from w ∥ nat_type ≤ w; then by the η rule and T7,
S′ + s = λw. (S′ w + s w) = λw. s w = s. -/
theorem filteredStepRefines (step : Term) :
    DerivableLatticeEta hypotheses
      (choice (application (application compose filterNatural)
        (application (application compose step) filterNatural)) step) step := by
  let filteredStep := application (application compose filterNatural)
    (application (application compose step) filterNatural)
  have pointRefines : DerivableLatticeEta hypotheses
      (choice (application (shift filteredStep) (boundVariable 0))
        (application (shift step) (boundVariable 0)))
      (application (shift step) (boundVariable 0)) := by
    show DerivableLatticeEta hypotheses
      (choice (application (application (application compose filterNatural)
          (application (application compose (shift step)) filterNatural)) (boundVariable 0))
        (application (shift step) (boundVariable 0)))
      (application (shift step) (boundVariable 0))
    have pointUnfolded : DerivableLatticeEta hypotheses
        (application (application (application compose filterNatural)
          (application (application compose (shift step)) filterNatural)) (boundVariable 0))
        (parallel (application (shift step) (parallel (boundVariable 0) naturalType)) naturalType) :=
      .transitive (composeApply _ _ _)
        (.transitive (filterNaturalApply _)
          (.congruenceParallelLeft naturalType
            (.transitive (composeApply _ _ _)
              (.congruenceArgument (shift step) (filterNaturalApply _)))))
    have argumentRefines : DerivableLatticeEta hypotheses
        (choice (application (shift step) (parallel (boundVariable 0) naturalType))
          (application (shift step) (boundVariable 0)))
        (application (shift step) (boundVariable 0)) :=
      DerivableLatticeEta.contextMonotone (parallelRefinesLeft (boundVariable 0) naturalType)
        (.applicationArgument (shift step) .hole)
    exact refinesOfEqualLower pointUnfolded
      (refinesTransitive (parallelRefinesLeft _ naturalType) argumentRefines)
  exact .transitive
    (DerivableLatticeEta.congruenceChoice (.symmetric (.eta filteredStep)) (.symmetric (.eta step)))
    (.transitive (.symmetric (DerivableLatticeEta.abstractionChoice _ _))
      (.transitive (.congruenceAbstraction pointRefines) (.eta step)))

/-- The filtered recursion refines the unfiltered one, nat_fold_filtered z s ≤ nat_fold z s:
nat_fold_filtered z s = nat_fold Z′ S′ by the β rule, with Z′ = z ∥ nat_type ≤ z by (1) and
(6), and S′ ≤ s (`filteredStepRefines`); so nat_fold Z′ S′ ≤ nat_fold z S′ ≤ nat_fold z s by T10, the
hole in the argument positions of nat_fold. -/
theorem naturalFoldFilteredRefinesUnfiltered (base step : Term) :
    DerivableLatticeEta hypotheses
      (choice (application (application naturalFoldFiltered base) step)
        (application (application naturalFold base) step))
      (application (application naturalFold base) step) := by
  have baseRefines : DerivableLatticeEta hypotheses (choice (application filterNatural base) base) base :=
    refinesOfEqualLower (filterNaturalApply base) (parallelRefinesLeft base naturalType)
  have firstArgument : DerivableLatticeEta hypotheses
      (choice
        (application (application naturalFold (application filterNatural base))
          (application (application compose filterNatural)
            (application (application compose step) filterNatural)))
        (application (application naturalFold base)
          (application (application compose filterNatural)
            (application (application compose step) filterNatural))))
      (application (application naturalFold base)
        (application (application compose filterNatural)
          (application (application compose step) filterNatural))) :=
    DerivableLatticeEta.contextMonotone baseRefines
      (.applicationFunction (.applicationArgument naturalFold .hole)
        (application (application compose filterNatural)
          (application (application compose step) filterNatural)))
  have secondArgument : DerivableLatticeEta hypotheses
      (choice
        (application (application naturalFold base)
          (application (application compose filterNatural)
            (application (application compose step) filterNatural)))
        (application (application naturalFold base) step))
      (application (application naturalFold base) step) :=
    DerivableLatticeEta.contextMonotone (filteredStepRefines step)
      (.applicationArgument (application naturalFold base) .hole)
  exact refinesOfEqualLower (naturalFoldFilteredApply base step)
    (refinesTransitive firstArgument secondArgument)

end Filters

/-! ## The lemmas of `parallel_types.pl` and `filtered_recursion_naturals.pl`

Each theorem is the lemma of the same name in
`gezi/corpora/standard_library/parallel_types.pl` or
`gezi/corpora/standard_library/filtered_recursion_naturals.pl`, its two sides written with the terms above, `@` read as `application` and a two-element list as
`choice` of its elements in order. A metavariable of the lemma is an argument of the theorem, any
term, closed or not. The proofs follow the proofs file, sections
7 and 9. -/

/-- The lemma `successor_filtered`:

    lemma(successor_filtered,
          compose @ filter_nat @ (compose @ successor @ filter_nat),
          compose @ successor @ filter_nat,
          equation, paper(set_equations, successor_filtered)).

With F = compose successor filter_nat, F x = successor (x ∥ nat_type) by the β rule, which refines
nat_type (`successorFilteredRefines`), so compose filter_nat F = F
(`composeFilterNaturalOfRefines`). -/
theorem successorFiltered :
    DerivableLatticeEta (fun _ _ => False)
      (application (application compose filterNatural)
        (application (application compose successor) filterNatural))
      (application (application compose successor) filterNatural) := by
  apply composeFilterNaturalOfRefines
  show DerivableLatticeEta _
    (choice (application (application (application compose successor) filterNatural)
      (boundVariable 0)) naturalType) naturalType
  exact refinesOfEqualLower
    (.transitive (composeApply successor filterNatural (boundVariable 0))
      (.congruenceArgument successor (filterNaturalApply (boundVariable 0))))
    (successorFilteredRefines (boundVariable 0))

/-- The lemma `successor_filtered_chained`:

    lemma(successor_filtered_chained,
          Rest^(compose @ filter_nat @ (compose @ successor @ (compose @ filter_nat @ Rest))),
          Rest^(compose @ successor @ (compose @ filter_nat @ Rest)),
          equation, paper(set_equations, successor_filtered_chained)).

As `successorFiltered`, with x replaced by Rest x: for the variable x,
compose successor (compose filter_nat Rest) x = successor ((Rest x) ∥ nat_type) by the β rule. -/
theorem successorFilteredChained (rest : Term) :
    DerivableLatticeEta (fun _ _ => False)
      (application (application compose filterNatural)
        (application (application compose successor)
          (application (application compose filterNatural) rest)))
      (application (application compose successor)
        (application (application compose filterNatural) rest)) := by
  apply composeFilterNaturalOfRefines
  show DerivableLatticeEta _
    (choice (application (application (application compose successor)
        (application (application compose filterNatural) (shift rest))) (boundVariable 0))
      naturalType) naturalType
  exact refinesOfEqualLower
    (.transitive (composeApply _ _ _)
      (.congruenceArgument successor
        (.transitive (composeApply _ _ _) (filterNaturalApply _))))
    (successorFilteredRefines _)

/-- The lemma `nat_fold_filtered_contract`:

    lemma(nat_fold_filtered_contract,
          Base^Step^(compose @ filter_nat @ (compose @ (nat_fold_filtered @ Base @ Step) @ filter_nat)),
          Base^Step^(compose @ (nat_fold_filtered @ Base @ Step) @ filter_nat),
          equation, paper(set_equations, nat_fold_filtered_contract)).

For the variable x, compose (nat_fold_filtered Base Step) filter_nat x =
nat_fold_filtered Base Step (x ∥ nat_type) by the β rule, which refines nat_type
(`naturalFoldFilteredRefines`); so the output filter is redundant
(`composeFilterNaturalOfRefines`). -/
theorem naturalFoldFilteredContract (base step : Term) :
    DerivableLatticeEta (fun _ _ => False)
      (application (application compose filterNatural)
        (application (application compose
          (application (application naturalFoldFiltered base) step)) filterNatural))
      (application (application compose
        (application (application naturalFoldFiltered base) step)) filterNatural) := by
  apply composeFilterNaturalOfRefines
  show DerivableLatticeEta _
    (choice (application (application (application compose
        (application (application naturalFoldFiltered (shift base)) (shift step))) filterNatural)
        (boundVariable 0)) naturalType) naturalType
  exact refinesOfEqualLower
    (.transitive (composeApply _ _ _) (.congruenceArgument _ (filterNaturalApply _)))
    (naturalFoldFilteredRefines _ _ _)

/-- The lemma `nat_fold_filtered_contract_chained`:

    lemma(nat_fold_filtered_contract_chained,
          Base^Step^Rest^(compose @ filter_nat @ (compose @ (nat_fold_filtered @ Base @ Step) @ (compose @ filter_nat @ Rest))),
          Base^Step^Rest^(compose @ (nat_fold_filtered @ Base @ Step) @ (compose @ filter_nat @ Rest)),
          equation, paper(set_equations, nat_fold_filtered_contract_chained)).

As `naturalFoldFilteredContract`, with x replaced by Rest x. -/
theorem naturalFoldFilteredContractChained (base step rest : Term) :
    DerivableLatticeEta (fun _ _ => False)
      (application (application compose filterNatural)
        (application (application compose
          (application (application naturalFoldFiltered base) step))
          (application (application compose filterNatural) rest)))
      (application (application compose
        (application (application naturalFoldFiltered base) step))
        (application (application compose filterNatural) rest)) := by
  apply composeFilterNaturalOfRefines
  show DerivableLatticeEta _
    (choice (application (application (application compose
        (application (application naturalFoldFiltered (shift base)) (shift step)))
        (application (application compose filterNatural) (shift rest)))
        (boundVariable 0)) naturalType) naturalType
  exact refinesOfEqualLower
    (.transitive (composeApply _ _ _)
      (.congruenceArgument _ (.transitive (composeApply _ _ _) (filterNaturalApply _))))
    (naturalFoldFilteredRefines _ _ _)

/-- The lemma `nat_fold_filtered_branch`:

    lemma(nat_fold_filtered_branch,
          Base^Step^(nat_fold @ Base @ Step),
          Base^Step^[nat_fold @ Base @ Step, nat_fold_filtered @ Base @ Step],
          equation, paper(set_equations, nat_fold_filtered_branch)).

nat_fold_filtered Base Step ≤ nat_fold Base Step (`naturalFoldFilteredRefinesUnfiltered`), and (1)
turns the equation around. -/
theorem naturalFoldFilteredBranch (base step : Term) :
    DerivableLatticeEta (fun _ _ => False)
      (application (application naturalFold base) step)
      (choice (application (application naturalFold base) step)
        (application (application naturalFoldFiltered base) step)) :=
  .symmetric (.transitive (.choiceCommutative _ _) (naturalFoldFilteredRefinesUnfiltered base step))

/-- The lemma `nat_fold_filtered_branch_in_context`:

    lemma(nat_fold_filtered_branch_in_context,
          Context^Base^Step^(Context @ (nat_fold @ Base @ Step)),
          Context^Base^Step^[Context @ (nat_fold @ Base @ Step), Context @ (nat_fold_filtered @ Base @ Step)],
          equation, paper(set_equations, nat_fold_filtered_branch_in_context)).

With A = nat_fold_filtered Base Step and B = nat_fold Base Step, A + B = B
(`naturalFoldFilteredRefinesUnfiltered`); by (10), M A + M (A + B) = M (A + B), that is
M A + M B = M B (T10's argument case); and (1) turns the equation around. -/
theorem naturalFoldFilteredBranchInContext (context base step : Term) :
    DerivableLatticeEta (fun _ _ => False)
      (application context (application (application naturalFold base) step))
      (choice (application context (application (application naturalFold base) step))
        (application context (application (application naturalFoldFiltered base) step))) :=
  .symmetric (.transitive (.choiceCommutative _ _)
    (DerivableLatticeEta.contextMonotone (naturalFoldFilteredRefinesUnfiltered base step)
      (.applicationArgument context .hole)))

/-- The lemma `natural_double_as_fold`:

    lemma(natural_double_as_fold,
          natural_double,
          nat_fold @ zero @ (compose @ successor @ successor),
          equation, paper(set_equations, natural_double_as_fold)).

nat_fold zero D = fixpoint (λself.λn. n zero (λp. D (self p))) by the β rule twice
(`naturalFoldToFixpoint`), D being compose successor successor, and
D (self p) = successor (successor (self p)) by the β rule under the binders (congruence); the result is
`naturalDouble`, de Bruijn indices making the bound variables' names irrelevant. -/
theorem naturalDoubleAsFold :
    DerivableLatticeEta (fun _ _ => False) naturalDouble
      (application (application naturalFold zero)
        (application (application compose successor) successor)) := by
  have contracted := naturalFoldToFixpoint (hypotheses := fun _ _ => False) zero
    (application (application compose successor) successor)
  have doubled := DerivableLatticeEta.congruenceFill
    (composeApply (hypotheses := fun _ _ => False) successor successor
      (application (boundVariable 2) (boundVariable 0)))
    (.applicationArgument fixpoint (.abstraction (.abstraction
      (.applicationArgument (application (boundVariable 0) zero) (.abstraction .hole)))))
  exact .symmetric (.transitive contracted doubled)

end LambdaJit.ParallelTypesTheorems
