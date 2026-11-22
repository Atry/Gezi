import LambdaJit.LatticeEtaDerivability

/-!
# A search for refinements guided by head redexes

`headRefined fuel lower upper` searches for a derivation of lower + upper = upper in
⊢_{λ-lattice-η} (`DerivableLatticeEta`, with no unit law), the equation that says that `lower`
refines `upper`: in the order of the proofs file, section 9,
`lower` ⊒ `upper`, the typed version above the untyped one. `headRefinedSound` turns what it
finds into the derivation. Its steps are the paper proof of the lemma `wren_typed_bindings`
(the proofs file, section 17) read as a procedure:

- reflexivity, M + M = M (`choiceIdempotent`);
- a parallel refines each of its sides, (M ∥ N) + M = M and (M ∥ N) + N = N
  (`parallelRefinesLeft`, `parallelRefinesRight`), joined by transitivity (`refinesTransitive`);
- an application is monotone in its argument, by (10), and in its function, by (8);
- an abstraction is monotone in its body, by T7 (`abstractionChoice`) and the congruence under λ;
- the η rule on the side that is no abstraction, when the other side is one;
- the β rule at the head of either side (`headStep`).

The congruences are tried only when both sides or neither have a head redex, and, when both have
one, their spines have one length (`congruenceFirst`, as in `headLinked` of module
`LibraryLemmaProofs`), so that a fixpoint that the two sides share is compared by congruence
rather than unfolded. Every step is a rule or a theorem of ⊢_{λ-lattice-η}, so what the search
finds holds with no unit law, and it is a contextual equivalence by
`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta` (module `LatticeEtaConsistency`).
-/

namespace LambdaJit.RefinementSearch

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

variable {hypotheses : Term → Term → Prop}

/-! ## Contraction at the head -/

/-- The contraction of the head redex: `(λx. M) N` applied to further arguments contracts to
`M[x := N]` applied to them; `none` when the head of the spine is no abstraction applied to an
argument. -/
def headStep : Term → Option Term
  | .application (.abstraction body) argument => some (instantiate body argument)
  | .application function argument =>
      (headStep function).map (fun contracted => .application contracted argument)
  | _ => none

/-- A head contraction is an equation of ⊢_{λ-lattice-η}: the β rule at the head, under the
congruence in the function of an application. -/
theorem headStepSound : ∀ {term contracted : Term},
    headStep term = some contracted → DerivableLatticeEta hypotheses term contracted := by
  intro term
  induction term with
  | application function argument functionSound _ =>
      intro contracted stepped
      cases function with
      | abstraction body =>
          simp only [headStep, Option.some.injEq] at stepped
          subst stepped
          exact .beta body argument
      | boundVariable index => simp [headStep] at stepped
      | application inner innerArgument =>
          simp only [headStep, Option.map_eq_some_iff] at stepped
          obtain ⟨functionContracted, functionStepped, rebuilt⟩ := stepped
          subst rebuilt
          exact .congruenceFunction argument (functionSound functionStepped)
      | choice left right => simp [headStep] at stepped
      | parallel left right => simp [headStep] at stepped
  | boundVariable index => intro contracted stepped; simp [headStep] at stepped
  | abstraction body _ => intro contracted stepped; simp [headStep] at stepped
  | choice left right _ _ => intro contracted stepped; simp [headStep] at stepped
  | parallel left right _ _ => intro contracted stepped; simp [headStep] at stepped

/-- Whether the term has a head redex. -/
def headIsRedex (term : Term) : Bool := (headStep term).isSome

/-- The number of arguments on the application spine of the term. -/
def spineLength : Term → Nat
  | .application function _ => spineLength function + 1
  | _ => 0

/-- Whether the term is an abstraction. -/
def isAbstraction : Term → Bool
  | .abstraction _ => true
  | _ => false

/-- Whether the search may compare the two terms by the congruence of their constructor: both or
neither have a head redex, and when both do, their spines have one length. -/
def congruenceFirst (lower upper : Term) : Bool :=
  headIsRedex lower == headIsRedex upper && (!headIsRedex lower || spineLength lower == spineLength upper)

/-! ## Refinement and its rules -/

/-- `lower` refines `upper`: lower + upper = upper in ⊢_{λ-lattice-η}. -/
def Refines (hypotheses : Term → Term → Prop) (lower upper : Term) : Prop :=
  DerivableLatticeEta hypotheses (choice lower upper) upper

theorem refinesReflexive (term : Term) : Refines hypotheses term term :=
  DerivableLatticeEta.choiceIdempotent term

theorem refinesTransitive {lower middle upper : Term} (lowerRefines : Refines hypotheses lower middle)
    (middleRefines : Refines hypotheses middle upper) : Refines hypotheses lower upper :=
  DerivableLatticeEta.refinesTransitive lowerRefines middleRefines

/-- Refinement is preserved by an equation on its lower side. -/
theorem refinesOfEqualLower {lower lowerEqual upper : Term}
    (equal : DerivableLatticeEta hypotheses lower lowerEqual)
    (refines : Refines hypotheses lowerEqual upper) : Refines hypotheses lower upper :=
  .transitive (.congruenceChoiceLeft upper equal) refines

/-- Refinement is preserved by an equation on its upper side. -/
theorem refinesOfEqualUpper {lower upper upperEqual : Term}
    (equal : DerivableLatticeEta hypotheses upper upperEqual)
    (refines : Refines hypotheses lower upperEqual) : Refines hypotheses lower upper :=
  .transitive (.congruenceChoiceRight lower equal) (.transitive refines (.symmetric equal))

theorem refinesParallelLeft {first second upper : Term} (refines : Refines hypotheses first upper) :
    Refines hypotheses (parallel first second) upper :=
  refinesTransitive (DerivableLatticeEta.parallelRefinesLeft first second) refines

theorem refinesParallelRight {first second upper : Term} (refines : Refines hypotheses second upper) :
    Refines hypotheses (parallel first second) upper :=
  refinesTransitive (DerivableLatticeEta.parallelRefinesRight first second) refines

/-- An application is monotone in its argument by (10), and in its function by (8). -/
theorem refinesApplication {lowerFunction upperFunction lowerArgument upperArgument : Term}
    (functionRefines : Refines hypotheses lowerFunction upperFunction)
    (argumentRefines : Refines hypotheses lowerArgument upperArgument) :
    Refines hypotheses (application lowerFunction lowerArgument)
      (application upperFunction upperArgument) := by
  have inArgument : Refines hypotheses (application lowerFunction lowerArgument)
      (application lowerFunction upperArgument) :=
    .transitive
      (.congruenceChoiceRight _ (.congruenceArgument lowerFunction (.symmetric argumentRefines)))
      (.transitive (.argumentMonotone lowerFunction lowerArgument upperArgument)
        (.congruenceArgument lowerFunction argumentRefines))
  have inFunction : Refines hypotheses (application lowerFunction upperArgument)
      (application upperFunction upperArgument) :=
    .transitive (.symmetric (DerivableLatticeEta.choiceFunctionDistributive _ _ _))
      (.congruenceFunction upperArgument functionRefines)
  exact refinesTransitive inArgument inFunction

/-- An abstraction is monotone in its body, by T7 and the congruence under λ. -/
theorem refinesAbstraction {lowerBody upperBody : Term}
    (refines : Refines hypotheses lowerBody upperBody) :
    Refines hypotheses (abstraction lowerBody) (abstraction upperBody) :=
  .transitive (.symmetric (DerivableLatticeEta.abstractionChoice lowerBody upperBody))
    (.congruenceAbstraction refines)

/-- An abstraction refines a term when its body refines the term's η expansion's body. -/
theorem refinesEtaUpper {lowerBody upper : Term}
    (refines : Refines hypotheses lowerBody (application (shift upper) (boundVariable 0))) :
    Refines hypotheses (abstraction lowerBody) upper :=
  refinesOfEqualUpper (.symmetric (.eta upper)) (refinesAbstraction refines)

/-- A term refines an abstraction when the term's η expansion's body refines the abstraction's
body. -/
theorem refinesEtaLower {lower upperBody : Term}
    (refines : Refines hypotheses (application (shift lower) (boundVariable 0)) upperBody) :
    Refines hypotheses lower (abstraction upperBody) :=
  refinesOfEqualLower (.symmetric (.eta lower)) (refinesAbstraction refines)

/-! ## The search -/

/-- A search for a derivation that `lower` refines `upper`, at most `fuel` levels deep: the two
terms are equal; or `lower` is a parallel one of whose sides the search finds refining `upper`;
or `congruenceFirst` holds, both are applications, and the search finds the functions and the
arguments refining, or both are abstractions and it finds the bodies refining; or exactly one is
an abstraction (and the other, when it is `lower`, has no head redex), and the search compares the
abstraction's body with the other's η expansion's body, with no other attempt; or it contracts
the head redex of `lower`, or failing one, of `upper`. -/
def headRefined : Nat → Term → Term → Bool
  | 0, lower, upper => lower == upper
  | fuel + 1, lower, upper =>
      lower == upper
      || (match lower with
          | .parallel first second => headRefined fuel first upper || headRefined fuel second upper
          | _ => false)
      || (congruenceFirst lower upper
          && match lower, upper with
            | .application lowerFunction lowerArgument, .application upperFunction upperArgument =>
                headRefined fuel lowerFunction upperFunction && headRefined fuel lowerArgument upperArgument
            | .abstraction lowerBody, .abstraction upperBody => headRefined fuel lowerBody upperBody
            | _, _ => false)
      || (match lower, upper with
          | .abstraction _, .abstraction _ => false
          | .abstraction lowerBody, _ =>
              headRefined fuel lowerBody (.application (shift upper) (.boundVariable 0))
          | _, .abstraction upperBody =>
              !headIsRedex lower
                && headRefined fuel (.application (shift lower) (.boundVariable 0)) upperBody
          | _, _ =>
              match headStep lower with
              | some contracted => headRefined fuel contracted upper
              | none =>
                  match headStep upper with
                  | some contracted => headRefined fuel lower contracted
                  | none => false)
      || (match lower, upper with
          | _, .abstraction _ =>
              headIsRedex lower
                && match headStep lower with
                  | some contracted => headRefined fuel contracted upper
                  | none => false
          | _, _ => false)

/-- What `headRefined` finds is a derivation that `lower` refines `upper` in ⊢_{λ-lattice-η}, from
any hypotheses: each of its steps is one of the rules above. -/
theorem headRefinedSound : ∀ {fuel : Nat} {lower upper : Term},
    headRefined fuel lower upper = true → Refines hypotheses lower upper := by
  intro fuel
  induction fuel with
  | zero =>
      intro lower upper equal
      simp only [headRefined, beq_iff_eq] at equal
      subst equal
      exact refinesReflexive _
  | succ remaining remainingSound =>
      intro lower upper found
      simp only [headRefined, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at found
      rcases found with (((same | inParallel) | ⟨_, congruent⟩) | expanded) | steppedLower
      · subst same
        exact refinesReflexive _
      · split at inParallel
        · simp only [Bool.or_eq_true] at inParallel
          rcases inParallel with first | second
          · exact refinesParallelLeft (remainingSound first)
          · exact refinesParallelRight (remainingSound second)
        · cases inParallel
      · split at congruent
        · simp only [Bool.and_eq_true] at congruent
          exact refinesApplication (remainingSound congruent.1) (remainingSound congruent.2)
        · exact refinesAbstraction (remainingSound congruent)
        · cases congruent
      · split at expanded
        · cases expanded
        · exact refinesEtaUpper (remainingSound expanded)
        · simp only [Bool.and_eq_true] at expanded
          exact refinesEtaLower (remainingSound expanded.2)
        · split at expanded
          · rename_i contracted contractedEqual
            exact refinesOfEqualLower (headStepSound contractedEqual) (remainingSound expanded)
          · split at expanded
            · rename_i contracted contractedEqual
              exact refinesOfEqualUpper (headStepSound contractedEqual) (remainingSound expanded)
            · cases expanded
      · split at steppedLower
        · simp only [Bool.and_eq_true] at steppedLower
          obtain ⟨_, stepped⟩ := steppedLower
          split at stepped
          · rename_i contracted contractedEqual
            exact refinesOfEqualLower (headStepSound contractedEqual) (remainingSound stepped)
          · cases stepped
        · cases steppedLower

/-! ## An equation that a refinement chosen beside the term absorbs -/

/-- The body under `count` abstractions; `none` when the term has fewer. -/
def underAbstractions : Nat → Term → Option Term
  | 0, term => some term
  | count + 1, .abstraction body => underAbstractions count body
  | _ + 1, _ => none

/-- Two terms under `count` abstractions each are equal when their bodies are, by the congruence
under λ. -/
theorem underAbstractionsCongruence : ∀ {count : Nat} {left right leftBody rightBody : Term},
    underAbstractions count left = some leftBody → underAbstractions count right = some rightBody →
    DerivableLatticeEta hypotheses leftBody rightBody → DerivableLatticeEta hypotheses left right := by
  intro count
  induction count with
  | zero =>
      intro left right leftBody rightBody leftUnder rightUnder equal
      simp only [underAbstractions, Option.some.injEq] at leftUnder rightUnder
      subst leftUnder rightUnder
      exact equal
  | succ remaining remainingCongruence =>
      intro left right leftBody rightBody leftUnder rightUnder equal
      cases left <;> cases right <;> simp only [underAbstractions, reduceCtorEq] at leftUnder rightUnder
      exact .congruenceAbstraction (remainingCongruence leftUnder rightUnder equal)

/-- `steps` contractions of the head redex in a row (`headStep`); `none` when one of them finds no
head redex. -/
def headSteps : Nat → Term → Option Term
  | 0, term => some term
  | steps + 1, term => (headStep term).bind (headSteps steps)

theorem headStepsSound : ∀ {steps : Nat} {term contracted : Term},
    headSteps steps term = some contracted → DerivableLatticeEta hypotheses term contracted := by
  intro steps
  induction steps with
  | zero =>
      intro term contracted stepped
      simp only [headSteps, Option.some.injEq] at stepped
      subst stepped
      exact .reflexive term
  | succ remaining remainingSound =>
      intro term contracted stepped
      simp only [headSteps, Option.bind_eq_some_iff] at stepped
      obtain ⟨middle, first, rest⟩ := stepped
      exact .transitive (headStepSound first) (remainingSound rest)

/-- Whether the equation `left` = `right` is M = M + N with N refining M, under `count`
abstractions on both sides: the body of `right` contracts at its head, in `steps` steps, to a
choice whose first member is the body of `left` and whose second member `headRefined` finds to
refine it. -/
def absorbs (count steps fuel : Nat) (left right : Term) : Bool :=
  match underAbstractions count left, underAbstractions count right with
  | some leftBody, some rightBody =>
      match headSteps steps rightBody with
      | some (.choice first second) => first == leftBody && headRefined fuel second leftBody
      | _ => false
  | _, _ => false

/-- What `absorbs` finds is a derivation in ⊢_{λ-lattice-η}: the body of `right` is M + N by the β
rule, N + M by (1), and M since N refines M; the congruence under λ carries the equation to the
two sides. -/
theorem absorbsSound {count steps fuel : Nat} {left right : Term}
    (found : absorbs count steps fuel left right = true) : DerivableLatticeEta hypotheses left right := by
  unfold absorbs at found
  split at found
  · rename_i leftBody rightBody leftUnder rightUnder
    split at found
    · rename_i first second stepped
      simp only [Bool.and_eq_true, beq_iff_eq] at found
      obtain ⟨same, refined⟩ := found
      subst same
      exact underAbstractionsCongruence leftUnder rightUnder
        (.symmetric (.transitive (headStepsSound stepped)
          (.transitive (.choiceCommutative first second) (headRefinedSound refined))))
    · cases found
  · cases found

/-- Whether `term`, under `count` abstractions, is M + N with M the body of `target` under as many
abstractions and N refining M (`headRefined`). -/
def absorbedInto (count fuel : Nat) (term target : Term) : Bool :=
  match underAbstractions count term, underAbstractions count target with
  | some (.choice first second), some targetBody => first == targetBody && headRefined fuel second targetBody
  | _, _ => false

/-- What `absorbedInto` finds is a derivation of `term` = `target` in ⊢_{λ-lattice-η}: M + N is
N + M by (1), and M since N refines M. -/
theorem absorbedIntoSound {count fuel : Nat} {term target : Term}
    (found : absorbedInto count fuel term target = true) : DerivableLatticeEta hypotheses term target := by
  unfold absorbedInto at found
  split at found
  · rename_i first second targetBody termUnder targetUnder
    simp only [Bool.and_eq_true, beq_iff_eq] at found
    obtain ⟨same, refined⟩ := found
    subst same
    exact underAbstractionsCongruence termUnder targetUnder
      (.transitive (.choiceCommutative first second) (headRefinedSound refined))
  · cases found

/-- One development (`StatementNormalisation.developed`, which this module does not import, is the
same function) is a derivation in ⊢_{λ-lattice-η}: the β rule under the congruences. -/
def developed : Term → Term
  | .application function argument =>
      match developed function with
      | .abstraction body => Term.instantiate body (developed argument)
      | developedFunction => .application developedFunction (developed argument)
  | .abstraction body => .abstraction (developed body)
  | .choice left right => .choice (developed left) (developed right)
  | .parallel left right => .parallel (developed left) (developed right)
  | other => other

theorem developedSound : ∀ term : Term, DerivableLatticeEta hypotheses term (developed term)
  | .application function argument => by
      have both : DerivableLatticeEta hypotheses (.application function argument)
          (.application (developed function) (developed argument)) :=
        .transitive (DerivableLatticeEta.congruenceFunction argument (developedSound function))
          (.congruenceArgument (developed function) (developedSound argument))
      simp only [developed]
      split
      · rename_i body developedAbstraction
        rw [developedAbstraction] at both
        exact .transitive both (.beta body (developed argument))
      · exact both
  | .abstraction body => by
      simp only [developed]
      exact .congruenceAbstraction (developedSound body)
  | .choice left right => by
      simp only [developed]
      exact DerivableLatticeEta.congruenceChoice (developedSound left) (developedSound right)
  | .parallel left right => by
      simp only [developed]
      exact .transitive (DerivableLatticeEta.congruenceParallelLeft right (developedSound left))
        (DerivableLatticeEta.congruenceParallelRight (developed left) (developedSound right))
  | .boundVariable _ => by simp only [developed]; exact DerivableLatticeEta.reflexive _

end LambdaJit.RefinementSearch
