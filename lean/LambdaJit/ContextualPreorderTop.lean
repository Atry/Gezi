import LambdaJit.LatticeEtaConsistency

/-!
# The greatest terms of ⊑_O, and `top` among them

This module proves, for DdLP96's contextual preorder ⊑_O of module `ContextualPreorder` (their
Definition 14; the contextual preorder record), facts
about the terms above every term, and applies them to `top` = Y (λz. λx. z ∥ x) of
the proofs file, section 3. `top` takes, in proofs, the place a term with no answer had: the language of terms
has no 0, and every lemma holds by Definition 14.
(L), (CA′) and theorem 4.1 ⇐ of module `ContextualPreorderAdequacy` use `top` as their closed argument,
and theorem 6.1 for ⊢_{λ-lattice-η} (module `LatticeEtaConsistency`) does not go through the unit
law.

- `ContextualTop X`: M ⊑_O X for every term M, open ones included.
- The criterion, `contextualTopIff` and `contextualTopIffClosed`, in Wadsworth's D∞ with no
  hypothesis (`DdLP96Model.contextualTopIffClosed` given a model): a closed X is a top if and only if
  X P₁ … Pₖ ∈ SOL for every k ≥ 0 and all terms P⃗, and it is enough to ask it for closed P⃗. This is
  the criterion of the proofs file, section 3, with "above every term" in the place of
  "≃_O-equal to 0".
- Direction ⇒ is the context □ P⃗ filled with a variable x, for which x P⃗ is a stuck spine, so it is
  solvable.
- Direction ⇐ is `DdLP96Model.contextualPreorderOfSolvableApplications`: let C[M] ∈ SOL; theorem 4.1
  of the record gives [[C[M]]]ρ_⊤ ≠ ⊥, so a compact d ≠ ⊥ below it; the record's basic lemma 4.3,
  generalised to a term in which some subterms are replaced by X (`SubtermsReplaced`,
  `DdLP96Model.basicLemmaSubtermsReplaced`), puts the closing instance of C[X] in 𝒮(d); (CA′) makes
  it solvable, and so is C[X]. The generalisation adds two cases to the record's lemma: a subterm
  kept as it is, which is the lemma itself (`DdLP96Model.basicLemma`), and a subterm replaced by X,
  where X ∈ 𝒮₀(⊤) ⊆ 𝒮(d) by (D), since d ⊑ ⊤. The free indices of C[M] are closed by X itself, which
  is in 𝒮₀(⊤) by the hypothesis.
- `contextualTop`: M ⊑_O `top` for every M, by the criterion and `solvableApplicationsTop`; likewise
  `contextualTopXi` for Ξ = Y (λe. Ŝ ∥ (K ∥ e e)), by `solvableApplicationsXi`.
- For every top X and every term M: X + M ≃_O M and M + X ≃_O M (`contextualEquivalenceTopChoiceOfContextualTop`,
  `contextualEquivalenceChoiceTopOfContextualTop`), and X ∥ M ≃_O X and M ∥ X ≃_O X
  (`contextualEquivalenceTopParallelOfContextualTop`, `contextualEquivalenceParallelTopOfContextualTop`). M ⊑_O X + M because
  M ≃_O M + M (M + M = M is derivable with no unit law, `DerivableLatticeEta.choiceIdempotent`) and
  ⊑_O is a precongruence; X + M ⊑_O M and X ⊑_O X ∥ M because DdLP96 read + as the meet and ∥ as the
  join of D∞ (corollary 4.2 of the record, `DdLP96Model.contextualPreorderOfInterpretBelow`); the
  other sides by the commutativity axioms (1) and (3). The instances at `top` are
  `contextualEquivalenceTopChoice`, `contextualEquivalenceChoiceTop`, `contextualEquivalenceTopParallel`
  and `contextualEquivalenceParallelTop`.
- `contextualEquivalenceTopApplication`: `top` M ≃_O `top`. `top` M = `top` ∥ M is derivable with no hypothesis by β
  alone (`derivableTopApplication`): `top` reduces in three β steps to λx. `top′` ∥ x, where `top′` is the
  self-application `top` reduces to, and `top′` = `top` by the first of them. Then `top` ∥ M ≃_O `top`.
- `contextualEquivalenceOfDerivableLatticeEtaHypotheses`: the record's theorem 6.1 for
  ⊢_{λ-lattice-η} with hypotheses: if every hypothesis is a contextual equivalence, every equation
  E ⊢_{λ-lattice-η} derives is one. By induction on the derivation: the closure rules hold of ≃_O,
  which is an equivalence and a congruence, and each instance of the β rule, the η rule and the axioms
  (1), (3), (5) and (10) is derivable with no hypothesis (`contextualEquivalenceOfDerivableLatticeEta`).
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.DInfinity (wadsworthModel)

/-- X is above every term in ⊑_O: M ⊑_O X for every term M, open ones included. -/
def ContextualTop (top : Term) : Prop := ∀ term : Term, ContextualPreorder term top

/-! ## ≃_O is an equivalence

Reflexivity and symmetry are `ContextualEquivalence.reflexive` and `ContextualEquivalence.symmetric`
of module `ContextualPreorder`. -/

/-- ≃_O is transitive. -/
private theorem equivalenceTransitive {left middle right : Term}
    (leftMiddle : ContextualEquivalence left middle) (middleRight : ContextualEquivalence middle right) :
    ContextualEquivalence left right :=
  ⟨ContextualPreorder.transitive leftMiddle.1 middleRight.1,
    ContextualPreorder.transitive middleRight.2 leftMiddle.2⟩

/-! ## Replacing subterms by a closed term -/

/-- `SubtermsReplaced replacement term result`: `result` is `term` with some (possibly none, possibly
all) of its subterms, whatever they are, replaced by `replacement`. -/
inductive SubtermsReplaced (replacement : Term) : Term → Term → Prop where
  /-- A subterm is kept as it is. -/
  | kept (term : Term) : SubtermsReplaced replacement term term
  /-- A subterm is replaced. -/
  | replaced (term : Term) : SubtermsReplaced replacement term replacement
  /-- λx. M. -/
  | abstraction {body result : Term} :
      SubtermsReplaced replacement body result →
        SubtermsReplaced replacement (.abstraction body) (.abstraction result)
  /-- M N. -/
  | application {function functionResult argument argumentResult : Term} :
      SubtermsReplaced replacement function functionResult →
        SubtermsReplaced replacement argument argumentResult →
          SubtermsReplaced replacement (.application function argument)
            (.application functionResult argumentResult)
  /-- M + N. -/
  | choice {left leftResult right rightResult : Term} :
      SubtermsReplaced replacement left leftResult →
        SubtermsReplaced replacement right rightResult →
          SubtermsReplaced replacement (.choice left right) (.choice leftResult rightResult)
  /-- M ∥ N. -/
  | parallel {left leftResult right rightResult : Term} :
      SubtermsReplaced replacement left leftResult →
        SubtermsReplaced replacement right rightResult →
          SubtermsReplaced replacement (.parallel left right) (.parallel leftResult rightResult)

namespace SubtermsReplaced

/-- C[X] is C[M] with the M in the hole replaced by X. -/
theorem fill (replacement term : Term) : ∀ context : Context,
    SubtermsReplaced replacement (context.fill term) (context.fill replacement)
  | .hole => .replaced term
  | .abstraction body => .abstraction (fill replacement term body)
  | .applicationFunction function argument =>
      .application (fill replacement term function) (.kept argument)
  | .applicationArgument function argument =>
      .application (.kept function) (fill replacement term argument)
  | .choiceLeft left right => .choice (fill replacement term left) (.kept right)
  | .choiceRight left right => .choice (.kept left) (fill replacement term right)
  | .parallelLeft left right => .parallel (fill replacement term left) (.kept right)
  | .parallelRight left right => .parallel (.kept left) (fill replacement term right)

/-- Replacing subterms by a closed term adds no free index. -/
theorem occursFree {replacement : Term} (closed : Closed replacement) {term result : Term}
    (replaced : SubtermsReplaced replacement term result) :
    ∀ index, OccursFree index result → OccursFree index term := by
  induction replaced with
  | kept _ => exact fun _ occurs => occurs
  | replaced _ => exact fun index occurs => absurd occurs (closed index)
  | abstraction _ inner => exact fun index => inner (index + 1)
  | application _ _ functionInner argumentInner =>
      exact fun index occurs => occurs.imp (functionInner index) (argumentInner index)
  | choice _ _ leftInner rightInner =>
      exact fun index occurs => occurs.imp (leftInner index) (rightInner index)
  | parallel _ _ leftInner rightInner =>
      exact fun index occurs => occurs.imp (leftInner index) (rightInner index)

end SubtermsReplaced

namespace DdLP96Model

variable (model : DdLP96Model)

/-- The record's basic lemma 4.3, generalised to replaced subterms: if `result` is `term` with some
subterms replaced by a closed X with X P⃗ ∈ SOL for every closed P⃗ (X ∈ 𝒮₀(⊤)), FV(`term`) is below the
length of a list of closed replacements Nᵢ ∈ 𝒮(ρ(i)) with ρ(i) compact, and d is compact with
d ⊑ [[`term`]]ρ, then `result`[i := Nᵢ] ∈ 𝒮(d). The proof is that of `DdLP96Model.basicLemma` of
module `ContextualPreorderAdequacy`, case by case, with two new cases: a kept subterm is that lemma
itself, and a replaced subterm becomes X, which the closing substitution leaves unchanged, with
X ∈ 𝒮₀(⊤) ⊆ 𝒮(d) by (D), since d ⊑ ⊤. -/
theorem basicLemmaSubtermsReplaced {replacement : Term} (replacementClosed : Closed replacement)
    (replacementComputable : model.Computable 0 model.top replacement) {term result : Term}
    (replaced : SubtermsReplaced replacement term result) :
    ∀ {replacements : List Term} {environment : Nat → model.Value},
      FreeBelow replacements.length term → model.ReplacementsComputable replacements environment →
        ∀ {level : Nat} {value : model.Value}, model.Compact level value →
          model.below value (model.interpret term environment) →
            model.Computable level value (closeAll 0 replacements result) := by
  induction replaced with
  | kept term =>
      intro replacements environment free computable level value compact below
      exact model.basicLemma term free computable compact below
  | replaced _ =>
      intro replacements _ _ _ level value compact _
      rw [closeAllClosed replacements 0 replacementClosed]
      exact model.computableBelow compact (model.compactTop 0) (model.topGreatest value)
        replacementComputable
  | @choice left leftResult right rightResult leftReplaced rightReplaced leftInner rightInner =>
      intro replacements environment free computable level value compact below
      rw [closeAllChoice]
      rw [model.interpretChoice] at below
      exact model.computableChoice level
        (leftInner (fun index occurs => free index (.inl occurs)) computable compact
          (model.orderTransitive below (model.meetBelowLeft _ _)))
        (rightInner (fun index occurs => free index (.inr occurs)) computable compact
          (model.orderTransitive below (model.meetBelowRight _ _)))
  | @parallel left leftResult right rightResult leftReplaced rightReplaced leftInner rightInner =>
      intro replacements environment free computable level value compact below
      rw [closeAllParallel]
      rw [model.interpretParallel] at below
      -- m₁ ⊔ m₂ is the least upper bound of the chain Pₖ m₁ ⊔ Pₖ m₂, so the compact d is below one
      -- member of it.
      obtain ⟨index, chainBelow⟩ := model.compact level value
        (fun index => model.join (model.project index (model.interpret left environment))
          (model.project index (model.interpret right environment)))
        (model.join (model.interpret left environment) (model.interpret right environment))
        compact
        (fun index => model.joinMonotone (model.projectIncreasing _ _) (model.projectIncreasing _ _))
        (fun upper bounds => model.joinLeast
          (model.projectLeast _ upper fun index =>
            model.orderTransitive (model.joinAboveLeft _ _) (bounds index))
          (model.projectLeast _ upper fun index =>
            model.orderTransitive (model.joinAboveRight _ _) (bounds index)))
        below
      have valueCompact := model.compactRaiseBy compact index
      have leftProjected := model.compactRaiseBy
        (model.compactProject index (model.interpret left environment)) level
      have rightProjected := model.compactRaiseBy
        (model.compactProject index (model.interpret right environment)) level
      rw [Nat.add_comm] at leftProjected rightProjected
      have leftPartCompact := model.compactMeet valueCompact leftProjected
      have rightPartCompact := model.compactMeet valueCompact rightProjected
      have leftComputable := leftInner (fun index occurs => free index (.inl occurs))
        computable leftPartCompact
        (model.orderTransitive (model.meetBelowRight _ _) (model.projectBelow _ _))
      have rightComputable := rightInner (fun index occurs => free index (.inr occurs))
        computable rightPartCompact
        (model.orderTransitive (model.meetBelowRight _ _) (model.projectBelow _ _))
      have joined := model.computableParallel (level + index) leftPartCompact rightPartCompact
        leftComputable rightComputable
      -- d = d ⊓ (Pₖ m₁ ⊔ Pₖ m₂) ⊑ (d ⊓ Pₖ m₁) ⊔ (d ⊓ Pₖ m₂), by distributivity (E1).
      have valueBelow := model.orderTransitive
        (model.meetGreatest (model.orderReflexive value) chainBelow)
        (model.distributive value _ _)
      exact model.computableBelow compact (model.compactJoin leftPartCompact rightPartCompact)
        valueBelow joined
  | @application function functionResult argument argumentResult functionReplaced argumentReplaced
      functionInner argumentInner =>
      intro replacements environment free computable level value compact below
      rw [closeAllApplication]
      rw [model.interpretApplication] at below
      -- x(y) is the least upper bound of the chain x_{n+1}(yₙ) (P7), so the compact d is below one
      -- member of it.
      obtain ⟨index, chainBelow⟩ := model.compact level value
        (fun index => model.apply (model.project (index + 1) (model.interpret function environment))
          (model.project index (model.interpret argument environment)))
        (model.apply (model.interpret function environment) (model.interpret argument environment))
        compact
        (fun index => model.orderTransitive
          (model.applyMonotoneFunction (model.projectIncreasing _ _) _)
          (model.applyMonotoneArgument _ (model.projectIncreasing _ _)))
        (model.applyLeast _ _)
        below
      have functionComputable := functionInner (fun index occurs => free index (.inl occurs))
        computable (model.compactProject (index + 1) _) (model.projectBelow _ _)
      have argumentComputable := argumentInner (fun index occurs => free index (.inr occurs))
        computable (model.compactProject index _) (model.projectBelow _ _)
      have argumentClosed := closeAllClosesTerm computable.allClosed
        (fun index occurs =>
          free index (.inr (argumentReplaced.occursFree replacementClosed index occurs)))
      have applied := functionComputable _ _ (model.compactProject index _) argumentClosed
        argumentComputable
      exact model.computableBelow compact
        (model.compactApply (model.compactProject (index + 1) _) _) chainBelow applied
  | @abstraction body bodyResult bodyReplaced bodyInner =>
      intro replacements environment free computable level value compact below
      rw [closeAllAbstraction computable.allClosed]
      apply model.computableAtLevel compact (model.compactRaise compact)
      intro argumentValue argument argumentCompact closed argumentComputable
      have bodyBelow : model.below (model.apply value argumentValue)
          (model.interpret body (extendEnvironment argumentValue environment)) := by
        rw [← model.interpretAbstraction]
        exact model.applyMonotoneFunction below argumentValue
      have bodyFree : FreeBelow (argument :: replacements).length body := by
        intro index occurs
        cases index with
        | zero => simp
        | succ index =>
            have inner := free index occurs
            simp only [List.length_cons]
            omega
      have bodyComputable := bodyInner bodyFree
        (ReplacementsComputable.extend model computable closed argumentCompact argumentComputable)
        (model.compactApply (model.compactRaise compact) argumentValue) bodyBelow
      rw [← instantiateCloseAll computable.allClosed closed] at bodyComputable
      exact (model.computableExpands level (expandsBeta _ _)).mpr bodyComputable

/-- M ⊑_O X for every term M and every closed X with X P⃗ ∈ SOL for every list of closed P⃗, given a
model satisfying the fields of `DdLP96Model`. Let C[M] ∈ SOL; then [[C[M]]]ρ_⊤ ≠ ⊥ (theorem 4.1 ⇒),
so some Pₙ([[C[M]]]ρ_⊤) ≠ ⊥ (P3); `basicLemmaSubtermsReplaced`, with X for every free index and the
hole's M replaced by X, puts the closing instance of C[X] in 𝒮ₙ(Pₙ([[C[M]]]ρ_⊤)); (CA′) makes it
solvable, and so is C[X]. -/
theorem contextualPreorderOfSolvableApplications (model : DdLP96Model) {top : Term}
    (closed : Closed top)
    (solvable : ∀ arguments, AllClosed arguments → Solvable (applyAll top arguments)) :
    ContextualTop top := by
  intro term context filledSolvable
  have notBottom := model.interpretNotBottomOfSolvable filledSolvable
  obtain ⟨bound, free⟩ := freeBound (context.fill term)
  have someLevel : ∃ level, model.project level
      (model.interpret (context.fill term) model.topEnvironment) ≠ model.bottom := by
    refine Classical.byContradiction fun none => notBottom ?_
    apply model.bottomOfBelowBottom
    apply model.projectLeast
    intro level
    have isBottom : model.project level
        (model.interpret (context.fill term) model.topEnvironment) = model.bottom :=
      Classical.byContradiction fun notEqual => none ⟨level, notEqual⟩
    rw [isBottom]
    exact model.orderReflexive _
  obtain ⟨level, projectedNotBottom⟩ := someLevel
  have topComputable : model.Computable 0 model.top top := .inr solvable
  have replacementsComputable :
      model.ReplacementsComputable (List.replicate bound top) model.topEnvironment := by
    intro index found foundEqual
    rw [List.getElem?_replicate] at foundEqual
    split at foundEqual
    · simp only [Option.some.injEq] at foundEqual
      subst foundEqual
      exact ⟨closed, 0, model.compactTop 0, topComputable⟩
    · exact absurd foundEqual (by simp)
  have computable := model.basicLemmaSubtermsReplaced closed topComputable
    (SubtermsReplaced.fill top term context)
    (by rw [List.length_replicate]; exact free)
    replacementsComputable (model.compactProject level _) (model.projectBelow _ _)
  exact solvableOfCloseAll _ 0
    (model.solvableOfComputable level (model.compactProject level _) projectedNotBottom computable)

end DdLP96Model

/-! ## The criterion -/

/-- Direction ⇒ of the criterion, for every term X: a top has X P₁ … Pₖ ∈ SOL for every k ≥ 0 and all
terms P⃗. The context □ P⃗ filled with the variable x gives x P⃗, a stuck spine, so it is solvable. -/
theorem solvableApplicationsOfContextualTop {top : Term} (greatest : ContextualTop top)
    (arguments : List Term) : Solvable (applyAll top arguments) := by
  have filled := greatest (.boundVariable 0) (applicationContext .hole arguments)
  rw [applicationContextFill, applicationContextFill] at filled
  exact filled (solvableOfStuckSpine (StuckSpine.applyAll arguments (.boundVariable 0)))

namespace DdLP96Model

/-- The criterion, given a model satisfying the fields of `DdLP96Model`, with closed arguments: a
closed X is above every term in ⊑_O if and only if X P⃗ ∈ SOL for every list P⃗ of closed terms. -/
theorem contextualTopIffClosed (model : DdLP96Model) {top : Term} (closed : Closed top) :
    ContextualTop top ↔ ∀ arguments, AllClosed arguments → Solvable (applyAll top arguments) :=
  ⟨fun greatest arguments _ => solvableApplicationsOfContextualTop greatest arguments,
    model.contextualPreorderOfSolvableApplications closed⟩

/-- The criterion, given a model satisfying the fields of `DdLP96Model`: a closed X is above every
term in ⊑_O if and only if X P₁ … Pₖ ∈ SOL for every k ≥ 0 and all terms P⃗. -/
theorem contextualTopIff (model : DdLP96Model) {top : Term} (closed : Closed top) :
    ContextualTop top ↔ ∀ arguments, Solvable (applyAll top arguments) :=
  ⟨solvableApplicationsOfContextualTop,
    fun solvable => (model.contextualTopIffClosed closed).mpr fun arguments _ => solvable arguments⟩

end DdLP96Model

/-- The criterion in Wadsworth's D∞, with no hypothesis: a closed X is above every term in ⊑_O if
and only if X P₁ … Pₖ ∈ SOL for every k ≥ 0 and all terms P⃗. -/
theorem contextualTopIff {top : Term} (closed : Closed top) :
    ContextualTop top ↔ ∀ arguments, Solvable (applyAll top arguments) :=
  wadsworthModel.contextualTopIff closed

/-- The criterion in Wadsworth's D∞ with closed arguments: a closed X is above every term in ⊑_O if
and only if X P⃗ ∈ SOL for every list P⃗ of closed terms. -/
theorem contextualTopIffClosed {top : Term} (closed : Closed top) :
    ContextualTop top ↔ ∀ arguments, AllClosed arguments → Solvable (applyAll top arguments) :=
  wadsworthModel.contextualTopIffClosed closed

/-- `top` is above every term: M ⊑_O `top` for every term M, open ones included. -/
theorem contextualTop : ContextualTop top :=
  (contextualTopIffClosed closedTop).mpr solvableApplicationsTop

/-- Ξ is above every term: M ⊑_O Ξ for every term M, open ones included, by the criterion and
`solvableApplicationsXi`. So the facts below about a top hold of Ξ as of `top`. -/
theorem contextualTopXi : ContextualTop fixedPointOfXi :=
  (contextualTopIffClosed closedFixedPointOfXi).mpr solvableApplicationsXi

/-! ## The record's theorem 6.1 for ⊢_{λ-lattice-η} with hypotheses -/

/-- The record's theorem 6.1 for ⊢_{λ-lattice-η} with hypotheses: if every hypothesis (a, b) satisfies
a ≃_O b, then E ⊢_{λ-lattice-η} M = M′ gives M ≃_O M′. By induction on the derivation: symmetry and
transitivity hold of ≃_O, the two congruences are `ContextualEquivalence.fill`, and each instance of
the β rule, the η rule and the axioms (1), (3), (5) and (10) is derivable with no hypothesis, so it
is a contextual equivalence by `contextualEquivalenceOfDerivableLatticeEta`. -/
theorem contextualEquivalenceOfDerivableLatticeEtaHypotheses {hypotheses : Term → Term → Prop}
    (hypothesesHold : ∀ left right, hypotheses left right → ContextualEquivalence left right)
    {left right : Term} (derivation : DerivableLatticeEta hypotheses left right) :
    ContextualEquivalence left right := by
  induction derivation with
  | hypothesis isHypothesis => exact hypothesesHold _ _ isHypothesis
  | symmetric _ inner => exact inner.symmetric
  | transitive _ _ leftEquivalence rightEquivalence =>
      exact equivalenceTransitive leftEquivalence rightEquivalence
  | congruenceArgument function _ inner => exact inner.fill (.applicationArgument function .hole)
  | congruenceAbstraction _ inner => exact inner.fill (.abstraction .hole)
  | beta body argument => exact contextualEquivalenceOfDerivableLatticeEta (.beta body argument)
  | eta function => exact contextualEquivalenceOfDerivableLatticeEta (.eta function)
  | choiceCommutative left right =>
      exact contextualEquivalenceOfDerivableLatticeEta (.choiceCommutative left right)
  | parallelCommutative left right =>
      exact contextualEquivalenceOfDerivableLatticeEta (.parallelCommutative left right)
  | parallelAbsorption kept other =>
      exact contextualEquivalenceOfDerivableLatticeEta (.parallelAbsorption kept other)
  | argumentMonotone function argument addition =>
      exact contextualEquivalenceOfDerivableLatticeEta (.argumentMonotone function argument addition)

/-! ## A top is the unit of the choice and absorbs the parallel -/

/-- X + M ≃_O M for every top X and every term M. M ≃_O M + M (T1, M + M = M, derivable with no unit
law) and M + M ⊑_O X + M by M ⊑_O X in the context □ + M; X + M ⊑_O M because + reads as the meet. -/
theorem contextualEquivalenceTopChoiceOfContextualTop {top : Term} (greatest : ContextualTop top) (term : Term) :
    ContextualEquivalence (.choice top term) term :=
  ⟨wadsworthModel.contextualPreorderOfInterpretBelow fun environment => by
      rw [wadsworthModel.interpretChoice]
      exact wadsworthModel.meetBelowRight _ _,
    ContextualPreorder.transitive
      (contextualEquivalenceOfDerivableLatticeEta (DerivableLatticeEta.choiceIdempotent term)).2
      ((greatest term).fill (.choiceLeft .hole term))⟩

/-- M + X ≃_O M for every top X and every term M, by (1) and `contextualEquivalenceTopChoiceOfContextualTop`. -/
theorem contextualEquivalenceChoiceTopOfContextualTop {top : Term} (greatest : ContextualTop top) (term : Term) :
    ContextualEquivalence (.choice term top) term :=
  equivalenceTransitive
    (contextualEquivalenceOfDerivableLatticeEta (.choiceCommutative term top))
    (contextualEquivalenceTopChoiceOfContextualTop greatest term)

/-- X ∥ M ≃_O X for every top X and every term M: X ∥ M ⊑_O X since X is a top, and X ⊑_O X ∥ M
because ∥ reads as the join. -/
theorem contextualEquivalenceTopParallelOfContextualTop {top : Term} (greatest : ContextualTop top) (term : Term) :
    ContextualEquivalence (.parallel top term) top :=
  ⟨greatest _,
    wadsworthModel.contextualPreorderOfInterpretBelow fun environment => by
      rw [wadsworthModel.interpretParallel]
      exact wadsworthModel.joinAboveLeft _ _⟩

/-- M ∥ X ≃_O X for every top X and every term M, by (3) and `contextualEquivalenceTopParallelOfContextualTop`. -/
theorem contextualEquivalenceParallelTopOfContextualTop {top : Term} (greatest : ContextualTop top) (term : Term) :
    ContextualEquivalence (.parallel term top) top :=
  equivalenceTransitive
    (contextualEquivalenceOfDerivableLatticeEta (.parallelCommutative term top))
    (contextualEquivalenceTopParallelOfContextualTop greatest term)

/-! ## `top` -/

/-- `top` + M ≃_O M for every term M. -/
theorem contextualEquivalenceTopChoice (term : Term) :
    ContextualEquivalence (.choice top term) term :=
  contextualEquivalenceTopChoiceOfContextualTop contextualTop term

/-- M + `top` ≃_O M for every term M. -/
theorem contextualEquivalenceChoiceTop (term : Term) :
    ContextualEquivalence (.choice term top) term :=
  contextualEquivalenceChoiceTopOfContextualTop contextualTop term

/-- `top` ∥ M ≃_O `top` for every term M. -/
theorem contextualEquivalenceTopParallel (term : Term) :
    ContextualEquivalence (.parallel top term) top :=
  contextualEquivalenceTopParallelOfContextualTop contextualTop term

/-- M ∥ `top` ≃_O `top` for every term M. -/
theorem contextualEquivalenceParallelTop (term : Term) :
    ContextualEquivalence (.parallel term top) top :=
  contextualEquivalenceParallelTopOfContextualTop contextualTop term

/-- A β step whose contractum is given by an equation. -/
private theorem derivableBetaTo {hypotheses : Term → Term → Prop} {body argument result : Term}
    (contractum : instantiate body argument = result) :
    DerivableLatticeEta hypotheses (.application (.abstraction body) argument) result :=
  contractum ▸ .beta body argument

/-- `top` = `top′`, where `top′` = (λx. F (x x)) (λx. F (x x)) with F = λz. λx. z ∥ x: one β step. -/
theorem derivableTopUnfolded {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses top (selfApplicationFixedPoint functionalOfTop) :=
  derivableBetaTo (by
    simp [instantiate, substitute, shiftClosed closedFunctionalOfTop, selfApplicationFixedPoint,
      selfApplicationOf])

/-- `top′` = λx. `top′` ∥ x, by two β steps: `top′` = F `top′` = λx. `top′` ∥ x. -/
theorem derivableUnfoldedTopAbstraction {hypotheses : Term → Term → Prop} :
    DerivableLatticeEta hypotheses (selfApplicationFixedPoint functionalOfTop)
      (.abstraction (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0))) := by
  have unfoldedClosed := closedSelfApplicationFixedPoint closedFunctionalOfTop
  have selfApplied : DerivableLatticeEta hypotheses (selfApplicationFixedPoint functionalOfTop)
      (.application functionalOfTop (selfApplicationFixedPoint functionalOfTop)) :=
    derivableBetaTo (by
      simp [instantiate, substitute, substituteClosed closedFunctionalOfTop, selfApplicationFixedPoint])
  have functionalApplied : DerivableLatticeEta hypotheses
      (.application functionalOfTop (selfApplicationFixedPoint functionalOfTop))
      (.abstraction (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0))) :=
    derivableBetaTo (by simp [instantiate, substitute, shiftClosed unfoldedClosed])
  exact .transitive selfApplied functionalApplied

/-- `top` M = `top` ∥ M for every term M, with no hypothesis beyond those given, by β alone: `top` = `top′` and
`top′` = λx. `top′` ∥ x, so `top` M = `top′` ∥ M = `top` ∥ M. -/
theorem derivableTopApplication {hypotheses : Term → Term → Prop} (term : Term) :
    DerivableLatticeEta hypotheses (.application top term) (.parallel top term) := by
  have unfoldedClosed := closedSelfApplicationFixedPoint closedFunctionalOfTop
  have applied : DerivableLatticeEta hypotheses
      (.application (.abstraction (.parallel (selfApplicationFixedPoint functionalOfTop) (.boundVariable 0)))
        term)
      (.parallel (selfApplicationFixedPoint functionalOfTop) term) :=
    derivableBetaTo (by simp [instantiate, substitute, substituteClosed unfoldedClosed])
  exact .transitive
    (DerivableLatticeEta.congruenceFunction term
      (.transitive derivableTopUnfolded derivableUnfoldedTopAbstraction))
    (.transitive applied
      (DerivableLatticeEta.congruenceParallelLeft term (.symmetric derivableTopUnfolded)))

/-- `top` M ≃_O `top` for every term M: `top` M ≃_O `top` ∥ M (`derivableTopApplication`) and `top` ∥ M ≃_O `top`. -/
theorem contextualEquivalenceTopApplication (term : Term) :
    ContextualEquivalence (.application top term) top :=
  equivalenceTransitive (contextualEquivalenceOfDerivableLatticeEta (derivableTopApplication term))
    (contextualEquivalenceTopParallel term)

end LambdaJit.ContextualPreorder
