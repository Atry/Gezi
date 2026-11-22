import LambdaJit.ContextualPreorderUnconditional
import LambdaJit.LatticeEtaBridge

/-!
# Two terms with the same normal forms above them in every context are contextually equivalent

With DdLP96's Definition 14, the contextual preorder ⊑_O of module `ContextualPreorder`, as the
primary definition, this module proves that ≃_O is exactly the equality of the sets
{ N ∈ NF_βη | C[M] ⊑_O N } (`ContextualNormalForm`) in every context C:

- Lemma A, `notSolvableIffContextualPreorderNormalForms`: a closed T is unsolvable if and only if
  T ⊑_O N for every closed βη normal form N. Direction ⇒: an unsolvable T reads as ⊥ in ρ_⊤
  (theorem 4.1 of the contextual preorder record), which is below the
  reading of every N, so T ⊑_O N by the record's corollary 4.2.
  Direction ⇐: a solvable T reduces to a head normal form H with the same reading, so T ≃_O H by
  corollary 4.2. Take k the number of leading abstractions of H (`leadingAbstractions`), the
  normal form N_k = λx₁ … λx_{k+1}. x_{k+1} (`selectLastArgument`) and the context □ `top` … `top` Ω with k
  occurrences of `top` = Y (λz. λx. z ∥ x) (`lastArgumentContext`). H `top` … `top` Ω is solvable: its β steps
  put `top` at the head of every spine whose head the abstractions of H bind, and `top` applied to anything
  is solvable (`solvableApplyAllTops`); so T `top` … `top` Ω is solvable, while N_k `top` … `top` Ω reduces to Ω and
  is not (`notSolvableSelectLastArgument`); so T ⋢_O N_k.
- The converse, `contextualEquivalenceOfSameContextualNormalForms`: if C[L] and C[R] have the same
  such normal forms for every context C, then L ≃_O R. For a context C, close C[L] and C[R] with b
  abstractions, b a bound on the free indices of both (`abstractionsContext`); Lemma A gives that
  the two closed terms are solvable together, and λx. M is solvable exactly when M is
  (`solvableAbstractAllIff`). `contextualEquivalenceOfSameContextualNormalFormsInClosingContexts`
  asks the hypothesis only of the contexts that close both terms.
  `contextualEquivalenceOfSameConsistentNormalForms` and its variant for closing contexts state the
  converse for the consistent normal forms NF◇_{λ-lattice-η} (`ConsistentNormalFormLatticeEta`), which
  are the same set for a closed term (`consistentNormalFormLatticeEtaIffContextualNormalForm`).
- The companion, `sameContextualNormalFormsOfContextualEquivalence`: ≃_O is a congruence and ⊑_O is
  transitive, so L ≃_O R gives the same sets in every context. The two directions together are
  `contextualEquivalenceIffSameContextualNormalForms`.

Every theorem that needs the reading takes a `DdLP96Model` and is instantiated, with no hypothesis,
at `wadsworthModel` of module `DInfinityModel`.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.DInfinity (wadsworthModel)

/-! ## Solvability under abstractions, and the contexts that close a term -/

/-- A bound of λx. M bounds M: every →hsa step of M is one of λx. M by (ξ). -/
theorem HeadReductionsAtMost.ofAbstraction : ∀ {steps : Nat} {body : Term},
    HeadReductionsAtMost steps (.abstraction body) → HeadReductionsAtMost steps body
  | 0, _, normal => fun _ step => normal _ (.abstraction step)
  | _ + 1, _, bounded => fun _ step => ofAbstraction (bounded _ (.abstraction step))

/-- λx₁ … λxₙ. M is solvable if and only if M is. -/
theorem solvableAbstractAllIff : ∀ (count : Nat) (body : Term),
    Solvable (abstractAll count body) ↔ Solvable body
  | 0, _ => Iff.rfl
  | count + 1, body => by
      show Solvable (.abstraction (abstractAll count body)) ↔ _
      rw [← solvableAbstractAllIff count body]
      exact ⟨fun ⟨steps, bounded⟩ => ⟨steps, bounded.ofAbstraction⟩,
        fun ⟨steps, bounded⟩ => ⟨steps, HeadReductionsAtMost.abstraction bounded⟩⟩

/-- The context λx₁ … λxₙ. C. -/
def abstractionsContext : Nat → Context → Context
  | 0, context => context
  | count + 1, context => .abstraction (abstractionsContext count context)

/-- (λx₁ … λxₙ. C)[M] = λx₁ … λxₙ. C[M]. -/
theorem abstractionsContextFill (term : Term) : ∀ (count : Nat) (context : Context),
    (abstractionsContext count context).fill term = abstractAll count (context.fill term)
  | 0, _ => rfl
  | count + 1, context => by
      simp only [abstractionsContext, Context.fill, abstractionsContextFill term count context,
        abstractAll]

/-- A bound on the free indices may be raised. -/
theorem FreeBelow.raise {bound larger : Nat} {term : Term} (free : FreeBelow bound term)
    (atMost : bound ≤ larger) : FreeBelow larger term :=
  fun index occurs => Nat.lt_of_lt_of_le (free index occurs) atMost

/-- n abstractions close a term whose free indices are below n. -/
theorem closedAbstractAllOfFreeBelow {bound : Nat} {body : Term} (free : FreeBelow bound body) :
    Closed (abstractAll bound body) := by
  have closing : FreeBelow 0 (abstractAll bound body) :=
    freeBelowOfAbstractAll (by rw [Nat.zero_add]; exact free)
  exact fun index occurs => Nat.not_lt_zero _ (closing index occurs)

/-! ## The normal forms N_k = λx₁ … λx_{k+1}. x_{k+1} -/

/-- N_k = λx₁ … λx_{k+1}. x_{k+1}, the closed normal form that returns the last of its k + 1
arguments. -/
def selectLastArgument (count : Nat) : Term :=
  abstractAll count (.abstraction (.boundVariable 0))

/-- N_k is an abstraction, so it is not an application. -/
theorem selectLastArgumentNotApplication (count : Nat) (function argument : Term) :
    selectLastArgument count ≠ .application function argument := by
  intro equal
  cases count <;> simp [selectLastArgument, abstractAll] at equal

/-- An abstraction whose body is not an application is neither a β redex nor an η redex. -/
theorem noRedexAbstraction {inner : Term}
    (notApplication : ∀ function argument, inner ≠ .application function argument) :
    ¬ BetaRedex (.abstraction inner) ∧ ¬ EtaRedex (.abstraction inner) := by
  refine ⟨fun beta => ?_, fun eta => ?_⟩
  · obtain ⟨_, _, equal⟩ := beta
    cases equal
  · obtain ⟨function, equal, _⟩ := eta
    exact notApplication function _ (Term.abstraction.inj equal)

/-- N_k has no β redex and no η redex. -/
theorem everySubtermSelectLastArgument : ∀ count : Nat,
    EverySubterm (fun subterm => ¬ BetaRedex subterm ∧ ¬ EtaRedex subterm) (selectLastArgument count)
  | 0 => by simp [selectLastArgument, abstractAll, EverySubterm, BetaRedex, EtaRedex]
  | count + 1 =>
      And.intro (noRedexAbstraction (selectLastArgumentNotApplication count))
        (everySubtermSelectLastArgument count)

/-- N_k is pure. -/
theorem pureSelectLastArgument : ∀ count : Nat, Pure (selectLastArgument count)
  | 0 => trivial
  | count + 1 => pureSelectLastArgument count

/-- N_k is a closed βη normal form. -/
theorem normalFormSelectLastArgument (count : Nat) : NormalForm (selectLastArgument count) :=
  ⟨closedAbstractAllOfFreeBelow (bound := count) fun index occurs => by
      simp only [OccursFree] at occurs
      omega,
    pureSelectLastArgument count, everySubtermSelectLastArgument count⟩

/-! ## The context □ `top` … `top` Ω

Lemma A ⇐ separates a solvable T from N_k with the context □ `top` … `top` Ω, k occurrences of
`top` = Y (λz. λx. z ∥ x): N_k `top` … `top` Ω reduces to Ω, which is not solvable, while T `top` … `top` Ω is
solvable for k large enough. The latter is read on a head normal form H of T: the β steps of
H `top` … `top` put `top` at the head of every stuck spine whose head the abstractions of H bind, and `top` applied
to any terms is solvable, `top` being above every term in ⊑_O (`contextualTop`). -/

/-- The number of abstractions at the root of a term, through choices and parallels: one more
than the body's for λx. M, the larger of the two sides' for a choice and a parallel, and 0
otherwise. -/
def leadingAbstractions : Term → Nat
  | .abstraction body => leadingAbstractions body + 1
  | .choice left right => max (leadingAbstractions left) (leadingAbstractions right)
  | .parallel left right => max (leadingAbstractions left) (leadingAbstractions right)
  | _ => 0

/-- Substituting `top` for a variable keeps the leading abstractions: `top` and a variable have none. -/
theorem leadingAbstractionsSubstituteTop : ∀ (term : Term) (depth : Nat),
    leadingAbstractions (substitute depth top term) = leadingAbstractions term
  | .boundVariable index, depth => by
      unfold substitute
      split
      · rfl
      · split
        · rfl
        · rfl
  | .abstraction body, depth => by
      simp only [substitute, shiftClosed closedTop, leadingAbstractions,
        leadingAbstractionsSubstituteTop body (depth + 1)]
  | .application _ _, _ => rfl
  | .choice left right, depth => by
      simp only [substitute, leadingAbstractions, leadingAbstractionsSubstituteTop left depth,
        leadingAbstractionsSubstituteTop right depth]
  | .parallel left right, depth => by
      simp only [substitute, leadingAbstractions, leadingAbstractionsSubstituteTop left depth,
        leadingAbstractionsSubstituteTop right depth]

/-- DdLP96's head normal forms (`HeadNormalForm`) with `top` allowed at the head of a spine: x M⃗ and
`top` M⃗, closed under λx. H, H₁ + H₂, H ∥ M and M ∥ H. -/
inductive HeadNormalFormWithTop : Term → Prop where
  /-- x M⃗. -/
  | stuck {term : Term} : StuckSpine term → HeadNormalFormWithTop term
  /-- `top` M⃗. -/
  | topApplication (arguments : List Term) : HeadNormalFormWithTop (applyAll top arguments)
  /-- λx. H. -/
  | abstraction {body : Term} : HeadNormalFormWithTop body → HeadNormalFormWithTop (.abstraction body)
  /-- H₁ + H₂. -/
  | choice {left right : Term} :
      HeadNormalFormWithTop left → HeadNormalFormWithTop right → HeadNormalFormWithTop (.choice left right)
  /-- H ∥ M. -/
  | parallelLeft {left : Term} (right : Term) :
      HeadNormalFormWithTop left → HeadNormalFormWithTop (.parallel left right)
  /-- M ∥ H. -/
  | parallelRight (left : Term) {right : Term} :
      HeadNormalFormWithTop right → HeadNormalFormWithTop (.parallel left right)

/-- A head normal form is one with `top` allowed at the head. -/
theorem headNormalFormWithTopOfHeadNormalForm {term : Term} (normal : HeadNormalForm term) :
    HeadNormalFormWithTop term := by
  induction normal with
  | stuck stuck => exact .stuck stuck
  | abstraction _ inner => exact .abstraction inner
  | choice _ _ leftInner rightInner => exact .choice leftInner rightInner
  | parallelLeft right _ inner => exact .parallelLeft right inner
  | parallelRight left _ inner => exact .parallelRight left inner

/-- `top` substituted for a variable of x M⃗ gives a stuck spine again, or `top` applied to arguments when
x is the variable. -/
theorem stuckSpineSubstituteTop {term : Term} (stuck : StuckSpine term) (depth : Nat) :
    StuckSpine (substitute depth top term) ∨
      ∃ arguments, substitute depth top term = applyAll top arguments := by
  induction stuck with
  | boundVariable index =>
      unfold substitute
      split
      · exact .inl (.boundVariable index)
      · split
        · exact .inr ⟨[], rfl⟩
        · exact .inl (.boundVariable _)
  | application argument _ inner =>
      simp only [substitute]
      rcases inner with innerStuck | ⟨arguments, equal⟩
      · exact .inl (.application _ innerStuck)
      · refine .inr ⟨arguments ++ [substitute depth top argument], ?_⟩
        rw [equal, applyAllAppend]

/-- `top` substituted for a variable keeps a head normal form with `top` allowed at the head. -/
theorem HeadNormalFormWithTop.substituteTop {term : Term} (normal : HeadNormalFormWithTop term) :
    ∀ depth, HeadNormalFormWithTop (substitute depth top term) := by
  induction normal with
  | stuck stuck =>
      intro depth
      rcases stuckSpineSubstituteTop stuck depth with substitutedStuck | ⟨arguments, equal⟩
      · exact .stuck substitutedStuck
      · rw [equal]
        exact .topApplication arguments
  | topApplication arguments =>
      intro depth
      rw [substituteApplyAll, substituteClosed closedTop]
      exact .topApplication _
  | abstraction _ inner =>
      intro depth
      simp only [substitute, shiftClosed closedTop]
      exact .abstraction (inner (depth + 1))
  | choice _ _ leftInner rightInner =>
      intro depth
      simp only [substitute]
      exact .choice (leftInner depth) (rightInner depth)
  | parallelLeft right _ inner =>
      intro depth
      simp only [substitute]
      exact .parallelLeft _ (inner depth)
  | parallelRight left _ inner =>
      intro depth
      simp only [substitute]
      exact .parallelRight _ (inner depth)

/-- H `top` … `top` P⃗, with `count` arguments `top`, is solvable for every P⃗ when H is a head normal form with
`top` allowed at the head and with at most `count` leading abstractions, given the case of an
abstraction: a stuck spine applied to anything is stuck, `top` applied to anything is solvable
(`contextualTop`), and a choice is solvable when both sides are, a parallel when one is
((S1), (S3)). -/
theorem solvableApplyAllTopsOf {count : Nat}
    (abstractionCase : ∀ {body : Term}, HeadNormalFormWithTop body →
      leadingAbstractions body + 1 ≤ count → ∀ arguments : List Term,
        Solvable (applyAll (.abstraction body) (List.replicate count top ++ arguments))) :
    ∀ {term : Term}, HeadNormalFormWithTop term → leadingAbstractions term ≤ count →
      ∀ arguments : List Term,
        Solvable (applyAll term (List.replicate count top ++ arguments)) := by
  intro term normal
  induction normal with
  | stuck stuck =>
      intro _ arguments
      exact solvableOfStuckSpine (StuckSpine.applyAll _ stuck)
  | topApplication topArguments =>
      intro _ arguments
      rw [← applyAllAppendAll]
      exact solvableApplicationsOfContextualTop contextualTop _
  | abstraction bodyNormal _ =>
      intro atMost arguments
      exact abstractionCase bodyNormal atMost arguments
  | choice _ _ leftInner rightInner =>
      intro atMost arguments
      rw [solvableChoiceSpine]
      exact ⟨leftInner (Nat.le_trans (Nat.le_max_left _ _) atMost) arguments,
        rightInner (Nat.le_trans (Nat.le_max_right _ _) atMost) arguments⟩
  | parallelLeft right _ inner =>
      intro atMost arguments
      rw [solvableParallelSpine]
      exact .inl (inner (Nat.le_trans (Nat.le_max_left _ _) atMost) arguments)
  | parallelRight left _ inner =>
      intro atMost arguments
      rw [solvableParallelSpine]
      exact .inr (inner (Nat.le_trans (Nat.le_max_right _ _) atMost) arguments)

/-- H `top` … `top` P⃗, with `count` arguments `top`, is solvable for every P⃗ when H is a head normal form with
`top` allowed at the head and with at most `count` leading abstractions. By induction on `count`: at an
abstraction λx. H′, the first `top` is a β step to H′[x := `top`] (`solvableBetaSpine`), again such a form
with the same leading abstractions (`HeadNormalFormWithTop.substituteTop`). -/
theorem solvableApplyAllTops (count : Nat) :
    ∀ {term : Term}, HeadNormalFormWithTop term → leadingAbstractions term ≤ count →
      ∀ arguments : List Term,
        Solvable (applyAll term (List.replicate count top ++ arguments)) := by
  induction count with
  | zero =>
      exact solvableApplyAllTopsOf fun _ atMost _ => absurd atMost (Nat.not_succ_le_zero _)
  | succ count outer =>
      refine solvableApplyAllTopsOf fun {body} bodyNormal atMost arguments => ?_
      show Solvable (applyAll (.application (.abstraction body) top)
        (List.replicate count top ++ arguments))
      rw [solvableBetaSpine]
      exact outer (bodyNormal.substituteTop 0)
        (by rw [leadingAbstractionsSubstituteTop]; omega) arguments

/-- The context □ `top` … `top` Ω, with `count` occurrences of `top`. -/
def lastArgumentContext (count : Nat) : Context :=
  .applicationFunction (applicationContext .hole (List.replicate count top)) Omega

/-- Filling □ `top` … `top` Ω applies the term to the arguments `top` … `top` Ω. -/
theorem lastArgumentContextFill (count : Nat) (term : Term) :
    (lastArgumentContext count).fill term =
      applyAll term (List.replicate count top ++ [Omega]) := by
  simp only [lastArgumentContext, Context.fill, applicationContextFill, applyAllAppend]

/-- N_k `top` … `top` Ω, with k occurrences of `top`, is not solvable: k β steps leave λx. x Ω, one more Ω,
and Ω is not solvable (`notSolvableOmega`). N_k is closed, so each `top` substituted into it leaves it
unchanged. -/
theorem notSolvableSelectLastArgument : ∀ count : Nat,
    ¬ Solvable (applyAll (selectLastArgument count) (List.replicate count top ++ [Omega]))
  | 0 => fun solvable => by
      have contracted := (solvableBetaSpine (.boundVariable 0) Omega []).mp solvable
      exact notSolvableOmega (by simpa [applyAll, instantiate, substitute] using contracted)
  | count + 1 => fun solvable => by
      have contracted := (solvableBetaSpine (selectLastArgument count) top
        (List.replicate count top ++ [Omega])).mp solvable
      rw [instantiate, substituteClosed (normalFormSelectLastArgument count).1] at contracted
      exact notSolvableSelectLastArgument count contracted

/-! ## Lemma A -/

namespace DdLP96Model

variable (model : DdLP96Model)

/-- Lemma A, given a model satisfying the fields of `DdLP96Model`: a closed T is unsolvable if and
only if T ⊑_O N for every closed βη normal form N. ⇒: [[T]]ρ_⊤ = ⊥ (theorem 4.1) is below [[N]]ρ_⊤,
and both terms are closed, so T ⊑_O N by corollary 4.2. ⇐: a solvable T reads as a head normal
form H in every environment (`reducesToHeadNormalForm`), so T ≃_O H by corollary 4.2. With k the
leading abstractions of H, H `top` … `top` Ω (k occurrences of `top`) is solvable (`solvableApplyAllTops`), and
so is T `top` … `top` Ω, while N_k `top` … `top` Ω is not (`notSolvableSelectLastArgument`), for
N_k = λx₁ … λx_{k+1}. x_{k+1}; T ⊑_O N_k would make it so. -/
theorem notSolvableIffContextualPreorderNormalForms (model : DdLP96Model) {term : Term}
    (closed : Closed term) :
    ¬ Solvable term ↔ ∀ candidate, NormalForm candidate → ContextualPreorder term candidate := by
  constructor
  · intro notSolvable candidate normal
    apply model.contextualPreorderOfInterpretBelow
    intro environment
    rw [model.interpretClosed closed environment, model.interpretClosed normal.1 environment]
    have isBottom : model.interpret term model.topEnvironment = model.bottom :=
      Classical.byContradiction fun notBottom =>
        notSolvable (model.solvableOfInterpretNotBottom notBottom)
    rw [isBottom]
    exact model.bottomLeast _
  · intro above solvable
    obtain ⟨steps, bounded⟩ := solvable
    obtain ⟨normal, isNormal, same⟩ := model.reducesToHeadNormalForm steps bounded
    have equivalence : ContextualEquivalence term normal :=
      model.contextualEquivalenceOfInterpretEqual same
    have normalSolvable :
        Solvable ((lastArgumentContext (leadingAbstractions normal)).fill normal) := by
      rw [lastArgumentContextFill]
      exact solvableApplyAllTops _ (headNormalFormWithTopOfHeadNormalForm isNormal) (Nat.le_refl _)
        [Omega]
    have termSolvable := equivalence.2 _ normalSolvable
    have candidateSolvable := above _ (normalFormSelectLastArgument (leadingAbstractions normal)) _
      termSolvable
    rw [lastArgumentContextFill] at candidateSolvable
    exact notSolvableSelectLastArgument _ candidateSolvable

end DdLP96Model

/-- Lemma A, with no hypothesis: a closed T is unsolvable if and only if T ⊑_O N for every closed
βη normal form N. `DdLP96Model.notSolvableIffContextualPreorderNormalForms` at Wadsworth's D∞. -/
theorem notSolvableIffContextualPreorderNormalForms {term : Term} (closed : Closed term) :
    ¬ Solvable term ↔ ∀ candidate, NormalForm candidate → ContextualPreorder term candidate :=
  wadsworthModel.notSolvableIffContextualPreorderNormalForms closed

/-! ## The converse and its companion -/

/-- Two closed terms with the same normal forms above them in ⊑_O are solvable together: by
Lemma A, each is unsolvable exactly when every closed βη normal form is above it. -/
theorem solvableIffOfSameContextualNormalForms {left right : Term} (leftClosed : Closed left)
    (rightClosed : Closed right)
    (same : ∀ candidate, ContextualNormalForm left candidate ↔ ContextualNormalForm right candidate) :
    Solvable left ↔ Solvable right := by
  have allAbove : (∀ candidate, NormalForm candidate → ContextualPreorder left candidate) ↔
      (∀ candidate, NormalForm candidate → ContextualPreorder right candidate) :=
    ⟨fun above candidate normal => ((same candidate).mp ⟨normal, above candidate normal⟩).2,
      fun above candidate normal => ((same candidate).mpr ⟨normal, above candidate normal⟩).2⟩
  have notIff := ((notSolvableIffContextualPreorderNormalForms leftClosed).trans allAbove).trans
    (notSolvableIffContextualPreorderNormalForms rightClosed).symm
  exact ⟨fun solvable => Classical.byContradiction fun notSolvable => notIff.mpr notSolvable solvable,
    fun solvable => Classical.byContradiction fun notSolvable => notIff.mp notSolvable solvable⟩

/-- The converse with its hypothesis asked of the closing contexts only: if C[L] and C[R] have the
same closed βη normal forms above them in ⊑_O for every context C that closes both, then L ≃_O R.
For any context C, b abstractions around C close both C[L] and C[R] (b bounding the free indices of
both); the two closed terms are solvable together by Lemma A, and λx. M is solvable exactly when M
is. -/
theorem contextualEquivalenceOfSameContextualNormalFormsInClosingContexts {left right : Term}
    (same : ∀ context : Context, Closed (context.fill left) → Closed (context.fill right) →
      ∀ candidate, ContextualNormalForm (context.fill left) candidate ↔
        ContextualNormalForm (context.fill right) candidate) :
    ContextualEquivalence left right := by
  have solvableIff : ∀ context : Context,
      Solvable (context.fill left) ↔ Solvable (context.fill right) := by
    intro context
    obtain ⟨leftBound, leftFree⟩ := freeBound (context.fill left)
    obtain ⟨rightBound, rightFree⟩ := freeBound (context.fill right)
    have leftClosed : Closed ((abstractionsContext (leftBound + rightBound) context).fill left) := by
      rw [abstractionsContextFill]
      exact closedAbstractAllOfFreeBelow (leftFree.raise (Nat.le_add_right _ _))
    have rightClosed : Closed ((abstractionsContext (leftBound + rightBound) context).fill right) := by
      rw [abstractionsContextFill]
      exact closedAbstractAllOfFreeBelow (rightFree.raise (Nat.le_add_left _ _))
    have closedIff := solvableIffOfSameContextualNormalForms leftClosed rightClosed
      (same _ leftClosed rightClosed)
    rw [abstractionsContextFill, abstractionsContextFill, solvableAbstractAllIff,
      solvableAbstractAllIff] at closedIff
    exact closedIff
  exact ⟨fun context solvable => (solvableIff context).mp solvable,
    fun context solvable => (solvableIff context).mpr solvable⟩

/-- The converse: if C[L] and C[R] have the same closed βη normal forms above them in ⊑_O for every
context C, then L ≃_O R. It is
`contextualEquivalenceOfSameContextualNormalFormsInClosingContexts`, whose hypothesis is this one's
asked of fewer contexts. -/
theorem contextualEquivalenceOfSameContextualNormalForms {left right : Term}
    (same : ∀ (context : Context) (candidate : Term),
      ContextualNormalForm (context.fill left) candidate ↔
        ContextualNormalForm (context.fill right) candidate) :
    ContextualEquivalence left right :=
  contextualEquivalenceOfSameContextualNormalFormsInClosingContexts
    fun context _ _ candidate => same context candidate

/-- The converse for the consistent normal forms NF◇_{λ-lattice-η} (`ConsistentNormalFormLatticeEta`),
with the hypothesis asked of the closing contexts only: if C[L] and C[R] have the same consistent
normal forms for every context C that closes both, then L ≃_O R. For a closed term the consistent
normal forms are the closed βη normal forms above it in ⊑_O
(`consistentNormalFormLatticeEtaIffContextualNormalForm`, module `LatticeEtaBridge`), so this is
`contextualEquivalenceOfSameContextualNormalFormsInClosingContexts`. -/
theorem contextualEquivalenceOfSameConsistentNormalFormsInClosingContexts {left right : Term}
    (same : ∀ context : Context, Closed (context.fill left) → Closed (context.fill right) →
      ∀ candidate, ConsistentNormalFormLatticeEta (context.fill left) candidate ↔
        ConsistentNormalFormLatticeEta (context.fill right) candidate) :
    ContextualEquivalence left right :=
  contextualEquivalenceOfSameContextualNormalFormsInClosingContexts
    fun context leftClosed rightClosed candidate =>
      (consistentNormalFormLatticeEtaIffContextualNormalForm leftClosed).symm.trans
        ((same context leftClosed rightClosed candidate).trans
          (consistentNormalFormLatticeEtaIffContextualNormalForm rightClosed))

/-- The converse for the consistent normal forms: if C[L] and C[R] have the same consistent normal
forms NF◇_{λ-lattice-η} for every context C, then L ≃_O R, by
`contextualEquivalenceOfSameConsistentNormalFormsInClosingContexts`. -/
theorem contextualEquivalenceOfSameConsistentNormalForms {left right : Term}
    (same : ∀ (context : Context) (candidate : Term),
      ConsistentNormalFormLatticeEta (context.fill left) candidate ↔
        ConsistentNormalFormLatticeEta (context.fill right) candidate) :
    ContextualEquivalence left right :=
  contextualEquivalenceOfSameConsistentNormalFormsInClosingContexts
    fun context _ _ candidate => same context candidate

/-- The companion: L ≃_O R gives C[L] and C[R] the same closed βη normal forms above them in ⊑_O, for
every context C, since ≃_O is a congruence (`ContextualEquivalence.fill`) and ⊑_O is transitive. -/
theorem sameContextualNormalFormsOfContextualEquivalence {left right : Term}
    (equivalence : ContextualEquivalence left right) :
    ∀ (context : Context) (candidate : Term),
      ContextualNormalForm (context.fill left) candidate ↔
        ContextualNormalForm (context.fill right) candidate := by
  intro context candidate
  have filled := equivalence.fill context
  exact ⟨fun ⟨normal, preorder⟩ => ⟨normal, ContextualPreorder.transitive filled.2 preorder⟩,
    fun ⟨normal, preorder⟩ => ⟨normal, ContextualPreorder.transitive filled.1 preorder⟩⟩

/-- L ≃_O R if and only if C[L] and C[R] have the same closed βη normal forms above them in ⊑_O for
every context C: `sameContextualNormalFormsOfContextualEquivalence` and
`contextualEquivalenceOfSameContextualNormalForms`. -/
theorem contextualEquivalenceIffSameContextualNormalForms {left right : Term} :
    ContextualEquivalence left right ↔
      ∀ (context : Context) (candidate : Term),
        ContextualNormalForm (context.fill left) candidate ↔
          ContextualNormalForm (context.fill right) candidate :=
  ⟨sameContextualNormalFormsOfContextualEquivalence, contextualEquivalenceOfSameContextualNormalForms⟩

end LambdaJit.ContextualPreorder
