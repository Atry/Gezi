import LambdaJit.ContextualPreorderAdequacy

/-!
# Approximants, conflict and separation: the syntax of the proofs file's section 20

The syntactic definitions of the proofs file, sections 14.1, 20.2, 20.3 and 20.4, on the terms of module `Terms`. Modules
`ContextualPreorderSeparationProof` and `ContextualPreorderCompleteness` build the combinators of
the separation and lemma C on them, and module `LatticeEtaSeparation` proves theorem S and the
completeness for ⊢_{λ-lattice-η}.

Formulation choices the proofs file leaves open:

- The proofs file adds a constant ⋄, read as ⊥, for a truncated subterm. Here ⋄ is Ω: a truncation
  replaces subterm occurrences by Ω (`Truncates`), and Ω reads as ⊥ in DdLP96's reading
  (module `ContextualPreorderCompleteness`). Ω is not a choice, a parallel or a head node, so,
  as for ⋄, no rule of the conflict relation applies to it.
- A head node λx₁ … xₙ. y H₁ … Hₘ is `headNode n y [H₁, …, Hₘ]`, with y a de Bruijn index under
  the n abstractions. The η-expansion alignment of section 14.1 expands both sides to
  p = max(n, n′) abstractions by inserting the new binders innermost: the head index is raised by
  p − n, every argument is shifted p − n times, and the new variables are appended as arguments
  (`paddedArguments`). Both sides then live under the same p binders, so the conflict relation
  compares de Bruijn indices directly; the proofs file names the binders of the two sides alike.
- βη normal forms that may be open are `BetaNormal`: λx⃗. y B⃗ with every Bᵢ again such a form.
  Lemma C needs only this shape (no β redex), not the absence of η redexes.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Head nodes and their alignment -/

/-- λx₁ … λxₙ. body. -/
def abstractAll : Nat → Term → Term
  | 0, body => body
  | count + 1, body => .abstraction (abstractAll count body)

/-- λx₁ … xₙ. y A₁ … Aₘ: `abstractions` abstractions over the variable of de Bruijn index `head`
applied to `arguments`. -/
def headNode (abstractions head : Nat) (arguments : List Term) : Term :=
  abstractAll abstractions (applyAll (.boundVariable head) arguments)

/-- The term shifted `count` times: placed under `count` more abstractions, inserted innermost. -/
def shiftTimes : Nat → Term → Term
  | 0, term => term
  | count + 1, term => shift (shiftTimes count term)

/-- The variables bound by `count` new innermost abstractions, outermost first: the indices
count − 1, …, 1, 0. -/
def trailingVariables : Nat → List Term
  | 0 => []
  | count + 1 => .boundVariable count :: trailingVariables count

/-- The arguments of a head node η-expanded by `extra` abstractions (section 14.1's A⁺): the
arguments shifted under the new abstractions, then the new variables. -/
def paddedArguments (extra : Nat) (arguments : List Term) : List Term :=
  arguments.map (shiftTimes extra) ++ trailingVariables extra

/-- Section 14.1's agreement at the root of λx₁ … xₙ. y A₁ … Aₘ and λx₁ … xₙ′. y′ B₁ … Bₘ′, both
η-expanded to p = max(n, n′) abstractions: the same head variable and the same number of
arguments, a = m + p − n = m′ + p − n′ = b. -/
def RootAgree (abstractions head argumentCount candidateAbstractions candidateHead
    candidateArgumentCount : Nat) : Prop :=
  head + (max abstractions candidateAbstractions - abstractions) =
      candidateHead + (max abstractions candidateAbstractions - candidateAbstractions) ∧
    argumentCount + (max abstractions candidateAbstractions - abstractions) =
      candidateArgumentCount + (max abstractions candidateAbstractions - candidateAbstractions)

/-! ## Stratified approximants, truncation, normal forms -/

/-- The proofs file's stratified approximate normal forms (section 20.3, without its clause for 0):
H ::= ⋄ | H + H | H ∥ H | λx₁ … xₙ. y H₁ … Hₘ, with ⋄ written Ω. -/
inductive Stratified : Term → Prop where
  /-- ⋄, written Ω. -/
  | truncated : Stratified Omega
  /-- H + H. -/
  | choice {left right : Term} : Stratified left → Stratified right → Stratified (.choice left right)
  /-- H ∥ H. -/
  | parallel {left right : Term} :
      Stratified left → Stratified right → Stratified (.parallel left right)
  /-- A head node λx₁ … xₙ. y H₁ … Hₘ. -/
  | headNode (abstractions head : Nat) (arguments : List Term) :
      (∀ argument ∈ arguments, Stratified argument) →
        Stratified (headNode abstractions head arguments)

/-- `Truncates approximant term`: the approximant is the term with some subterm occurrences
replaced by ⋄, written Ω (the proofs file's section 20.2, "A 是 T′ 的截断"). -/
inductive Truncates : Term → Term → Prop where
  /-- A subterm replaced by ⋄. -/
  | truncated (term : Term) : Truncates Omega term
  /-- A variable kept. -/
  | boundVariable (index : Nat) : Truncates (.boundVariable index) (.boundVariable index)
  /-- An abstraction kept. -/
  | abstraction {approximant term : Term} :
      Truncates approximant term → Truncates (.abstraction approximant) (.abstraction term)
  /-- An application kept. -/
  | application {function argument functionTerm argumentTerm : Term} :
      Truncates function functionTerm → Truncates argument argumentTerm →
        Truncates (.application function argument) (.application functionTerm argumentTerm)
  /-- A choice kept. -/
  | choice {left right leftTerm rightTerm : Term} :
      Truncates left leftTerm → Truncates right rightTerm →
        Truncates (.choice left right) (.choice leftTerm rightTerm)
  /-- A parallel kept. -/
  | parallel {left right leftTerm rightTerm : Term} :
      Truncates left leftTerm → Truncates right rightTerm →
        Truncates (.parallel left right) (.parallel leftTerm rightTerm)

/-- A β normal pure term, possibly open: λx₁ … xₙ. y B₁ … Bₘ with every Bᵢ such a term. -/
inductive BetaNormal : Term → Prop where
  /-- λx₁ … xₙ. y B₁ … Bₘ. -/
  | headNode (abstractions head : Nat) (arguments : List Term) :
      (∀ argument ∈ arguments, BetaNormal argument) →
        BetaNormal (headNode abstractions head arguments)

/-! ## Conflict -/

/-- The proofs file's conflict A ⋪ N of a stratified approximant A with a βη normal form N
(section 20.3, its rules (R1) and (R2) from section 14.1, without its rule (Z) for 0): the least
relation with (P) A₁ ∥ A₂ ⋪ N when A₁ ⋪ N or A₂ ⋪ N; (C) A₁ + A₂ ⋪ N
when A₁ ⋪ N and A₂ ⋪ N; (R1) two head nodes that disagree at the root; (R2) two head nodes that
agree at the root, with some position i at which the padded arguments conflict, A⁺ᵢ ⋪ B⁺ᵢ. -/
inductive Conflicts : Term → Term → Prop where
  /-- (P), the left side. -/
  | parallelLeft {left : Term} (right : Term) {candidate : Term} :
      Conflicts left candidate → Conflicts (.parallel left right) candidate
  /-- (P), the right side. -/
  | parallelRight (left : Term) {right candidate : Term} :
      Conflicts right candidate → Conflicts (.parallel left right) candidate
  /-- (C). -/
  | choice {left right candidate : Term} :
      Conflicts left candidate → Conflicts right candidate → Conflicts (.choice left right) candidate
  /-- (R1). -/
  | rootDisagree (abstractions head : Nat) (arguments : List Term)
      (candidateAbstractions candidateHead : Nat) (candidateArguments : List Term) :
      ¬ RootAgree abstractions head arguments.length candidateAbstractions candidateHead
        candidateArguments.length →
      Conflicts (headNode abstractions head arguments)
        (headNode candidateAbstractions candidateHead candidateArguments)
  /-- (R2). -/
  | argument (abstractions head : Nat) (arguments : List Term)
      (candidateAbstractions candidateHead : Nat) (candidateArguments : List Term)
      (position : Nat) {approximantArgument candidateArgument : Term} :
      RootAgree abstractions head arguments.length candidateAbstractions candidateHead
        candidateArguments.length →
      (paddedArguments (max abstractions candidateAbstractions - abstractions) arguments)[position]? =
        some approximantArgument →
      (paddedArguments (max abstractions candidateAbstractions - candidateAbstractions)
        candidateArguments)[position]? = some candidateArgument →
      Conflicts approximantArgument candidateArgument →
      Conflicts (headNode abstractions head arguments)
        (headNode candidateAbstractions candidateHead candidateArguments)

/-! ## Shifting head nodes -/

/-- Shifting an application spine shifts its head and its arguments. -/
theorem shiftFromApplyAll (cutoff : Nat) : ∀ (head : Term) (arguments : List Term),
    shiftFrom cutoff (applyAll head arguments) =
      applyAll (shiftFrom cutoff head) (arguments.map (shiftFrom cutoff))
  | _, [] => rfl
  | head, argument :: rest => shiftFromApplyAll cutoff (.application head argument) rest

/-- Shifting under abstractions raises the cutoff. -/
theorem shiftFromAbstractAll : ∀ (count cutoff : Nat) (body : Term),
    shiftFrom cutoff (abstractAll count body) = abstractAll count (shiftFrom (cutoff + count) body)
  | 0, _, _ => rfl
  | count + 1, cutoff, body => by
      show Term.abstraction (shiftFrom (cutoff + 1) (abstractAll count body)) = _
      rw [shiftFromAbstractAll count (cutoff + 1) body, Nat.add_right_comm, Nat.add_assoc]
      rfl

/-- A shifted head node is a head node. -/
theorem shiftFromHeadNode (cutoff abstractions head : Nat) (arguments : List Term) :
    shiftFrom cutoff (headNode abstractions head arguments) =
      headNode abstractions (if head < cutoff + abstractions then head else head + 1)
        (arguments.map (shiftFrom (cutoff + abstractions))) := by
  unfold headNode
  rw [shiftFromAbstractAll, shiftFromApplyAll]
  by_cases below : head < cutoff + abstractions <;> simp [shiftFrom, below]

/-- Shifting preserves stratification. -/
theorem Stratified.shiftFrom {term : Term} (stratified : Stratified term) :
    ∀ cutoff, Stratified (Term.shiftFrom cutoff term) := by
  induction stratified with
  | truncated =>
      intro cutoff
      rw [shiftFromUnchanged Omega cutoff (fun index _ => closedOmega index)]
      exact .truncated
  | choice _ _ leftInner rightInner =>
      intro cutoff
      exact .choice (leftInner cutoff) (rightInner cutoff)
  | parallel _ _ leftInner rightInner =>
      intro cutoff
      exact .parallel (leftInner cutoff) (rightInner cutoff)
  | headNode abstractions head arguments _ inner =>
      intro cutoff
      rw [shiftFromHeadNode]
      refine .headNode _ _ _ fun argument member => ?_
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact inner original originalMember _

/-- Shifting preserves β normal forms. -/
theorem BetaNormal.shiftFrom {term : Term} (normal : BetaNormal term) :
    ∀ cutoff, BetaNormal (Term.shiftFrom cutoff term) := by
  induction normal with
  | headNode abstractions head arguments _ inner =>
      intro cutoff
      rw [shiftFromHeadNode]
      refine .headNode _ _ _ fun argument member => ?_
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact inner original originalMember _

theorem Stratified.shiftTimes {term : Term} (stratified : Stratified term) :
    ∀ count, Stratified (ContextualPreorder.shiftTimes count term)
  | 0 => stratified
  | count + 1 => (Stratified.shiftTimes stratified count).shiftFrom 0

theorem BetaNormal.shiftTimes {term : Term} (normal : BetaNormal term) :
    ∀ count, BetaNormal (ContextualPreorder.shiftTimes count term)
  | 0 => normal
  | count + 1 => (BetaNormal.shiftTimes normal count).shiftFrom 0

/-- A variable is a head node with no abstraction and no argument. -/
theorem headNodeVariable (index : Nat) : headNode 0 index [] = .boundVariable index := rfl

/-- Every padded argument of stratified arguments is stratified. -/
theorem stratifiedPaddedArguments {arguments : List Term}
    (stratified : ∀ argument ∈ arguments, Stratified argument) (extra : Nat) :
    ∀ argument ∈ paddedArguments extra arguments, Stratified argument := by
  intro argument member
  rcases List.mem_append.mp member with inArguments | inTrailing
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inArguments
    exact (stratified original originalMember).shiftTimes extra
  · have isVariable : ∃ index, argument = .boundVariable index := by
      clear member
      induction extra with
      | zero => exact absurd inTrailing List.not_mem_nil
      | succ extra inner =>
          rcases List.mem_cons.mp inTrailing with equal | rest
          · exact ⟨extra, equal⟩
          · exact inner rest
    obtain ⟨index, rfl⟩ := isVariable
    rw [← headNodeVariable]
    exact .headNode 0 index [] (fun _ member => absurd member List.not_mem_nil)

/-- Every padded argument of β normal arguments is β normal. -/
theorem betaNormalPaddedArguments {arguments : List Term}
    (normal : ∀ argument ∈ arguments, BetaNormal argument) (extra : Nat) :
    ∀ argument ∈ paddedArguments extra arguments, BetaNormal argument := by
  intro argument member
  rcases List.mem_append.mp member with inArguments | inTrailing
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inArguments
    exact (normal original originalMember).shiftTimes extra
  · have isVariable : ∃ index, argument = .boundVariable index := by
      clear member
      induction extra with
      | zero => exact absurd inTrailing List.not_mem_nil
      | succ extra inner =>
          rcases List.mem_cons.mp inTrailing with equal | rest
          · exact ⟨extra, equal⟩
          · exact inner rest
    obtain ⟨index, rfl⟩ := isVariable
    rw [← headNodeVariable]
    exact .headNode 0 index [] (fun _ member => absurd member List.not_mem_nil)

/-! ## Closed βη normal forms are β normal head nodes -/

/-- A spine applied to one more argument. -/
theorem applyAllAppend : ∀ (head : Term) (arguments : List Term) (last : Term),
    applyAll head (arguments ++ [last]) = .application (applyAll head arguments) last
  | _, [], _ => rfl
  | head, argument :: rest, last => applyAllAppend (.application head argument) rest last

theorem lengthTrailingVariables : ∀ count, (trailingVariables count).length = count
  | 0 => rfl
  | count + 1 => by
      show (trailingVariables count).length + 1 = count + 1
      rw [lengthTrailingVariables count]

theorem lengthPaddedArguments (extra : Nat) (arguments : List Term) :
    (paddedArguments extra arguments).length = arguments.length + extra := by
  simp [paddedArguments, lengthTrailingVariables]

/-- A spine applied to two lists of arguments in turn. -/
theorem applyAllAppendAll : ∀ (head : Term) (first second : List Term),
    applyAll head (first ++ second) = applyAll (applyAll head first) second
  | _, [], _ => rfl
  | head, argument :: rest, second => applyAllAppendAll (.application head argument) rest second

/-- A pure term with no β redex is β normal. -/
theorem betaNormalOfPure : ∀ (term : Term), Pure term →
    EverySubterm (fun subterm => ¬ BetaRedex subterm ∧ ¬ EtaRedex subterm) term →
      BetaNormal term
  | .boundVariable index, _, _ => by
      rw [← headNodeVariable]
      exact .headNode 0 index [] (fun _ member => absurd member List.not_mem_nil)
  | .abstraction body, pure, every => by
      have bodyNormal := betaNormalOfPure body pure every.2
      cases bodyNormal with
      | headNode abstractions head arguments argumentsNormal =>
          exact .headNode (abstractions + 1) head arguments argumentsNormal
  | .application function argument, pure, every => by
      have functionNormal := betaNormalOfPure function pure.1 every.2.1
      have argumentNormal := betaNormalOfPure argument pure.2 every.2.2
      cases functionNormal with
      | headNode abstractions head arguments argumentsNormal =>
          cases abstractions with
          | zero =>
              show BetaNormal (.application (applyAll (.boundVariable head) arguments) argument)
              rw [← applyAllAppend]
              refine .headNode 0 head (arguments ++ [argument]) fun member inList => ?_
              rcases List.mem_append.mp inList with inArguments | isLast
              · exact argumentsNormal member inArguments
              · rw [List.mem_singleton.mp isLast]
                exact argumentNormal
          | succ abstractions =>
              exact absurd ⟨_, _, rfl⟩ every.1.1
  | .choice _ _, pure, _ => absurd pure id
  | .parallel _ _, pure, _ => absurd pure id

/-- A closed βη normal form is β normal. -/
theorem betaNormalOfNormalForm {term : Term} (normal : NormalForm term) : BetaNormal term :=
  betaNormalOfPure term normal.2.1 normal.2.2

/-! ## Size -/

/-- The size of a term: a variable counts 1, an abstraction one more than its body, an
application the sum of its two sides, a choice and a parallel one more than that sum. -/
def termSize : Term → Nat
  | .boundVariable _ => 1
  | .abstraction body => termSize body + 1
  | .application function argument => termSize function + termSize argument
  | .choice left right => termSize left + termSize right + 1
  | .parallel left right => termSize left + termSize right + 1

theorem termSizeShiftFrom : ∀ (term : Term) (cutoff : Nat),
    termSize (shiftFrom cutoff term) = termSize term
  | .boundVariable index, cutoff => by
      unfold shiftFrom
      split <;> rfl
  | .abstraction body, cutoff => by
      simp only [shiftFrom, termSize, termSizeShiftFrom body (cutoff + 1)]
  | .application function argument, cutoff => by
      simp only [shiftFrom, termSize, termSizeShiftFrom function cutoff,
        termSizeShiftFrom argument cutoff]
  | .choice left right, cutoff => by
      simp only [shiftFrom, termSize, termSizeShiftFrom left cutoff, termSizeShiftFrom right cutoff]
  | .parallel left right, cutoff => by
      simp only [shiftFrom, termSize, termSizeShiftFrom left cutoff, termSizeShiftFrom right cutoff]

theorem termSizeShiftTimes : ∀ (count : Nat) (term : Term),
    termSize (shiftTimes count term) = termSize term
  | 0, _ => rfl
  | count + 1, term => (termSizeShiftFrom _ 0).trans (termSizeShiftTimes count term)

/-- The sizes of the arguments add up. -/
def argumentsSize : List Term → Nat
  | [] => 0
  | argument :: rest => termSize argument + argumentsSize rest

theorem termSizeApplyAll : ∀ (head : Term) (arguments : List Term),
    termSize (applyAll head arguments) = termSize head + argumentsSize arguments
  | _, [] => rfl
  | head, argument :: rest => by
      rw [show applyAll head (argument :: rest) = applyAll (.application head argument) rest from rfl,
        termSizeApplyAll (.application head argument) rest]
      simp only [termSize, argumentsSize]
      omega

theorem termSizeAbstractAll : ∀ (count : Nat) (body : Term),
    termSize (abstractAll count body) = termSize body + count
  | 0, _ => rfl
  | count + 1, body => by
      show termSize (abstractAll count body) + 1 = _
      rw [termSizeAbstractAll count body]
      omega

theorem termSizeHeadNode (abstractions head : Nat) (arguments : List Term) :
    termSize (headNode abstractions head arguments) = 1 + argumentsSize arguments + abstractions := by
  unfold headNode
  rw [termSizeAbstractAll, termSizeApplyAll]
  rfl

theorem termSizeBelowArgumentsSize : ∀ {arguments : List Term} {argument : Term},
    argument ∈ arguments → termSize argument ≤ argumentsSize arguments
  | [], _, member => absurd member List.not_mem_nil
  | first :: rest, argument, member => by
      rcases List.mem_cons.mp member with equal | inRest
      · subst equal
        simp only [argumentsSize]
        omega
      · have inner := termSizeBelowArgumentsSize inRest
        simp only [argumentsSize]
        omega

/-- A padded argument is a shifted argument, no larger than all the arguments together, or one of
the new variables, of size 1, which exists only when the expansion adds abstractions. -/
theorem termSizePaddedArgument {extra : Nat} {arguments : List Term} {position : Nat}
    {argument : Term} (found : (paddedArguments extra arguments)[position]? = some argument) :
    termSize argument ≤ argumentsSize arguments ∨ (termSize argument = 1 ∧ 0 < extra) := by
  have member : argument ∈ paddedArguments extra arguments := List.mem_of_getElem? found
  rcases List.mem_append.mp member with inArguments | inTrailing
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inArguments
    rw [termSizeShiftTimes]
    exact .inl (termSizeBelowArgumentsSize originalMember)
  · right
    clear found member
    induction extra with
    | zero => exact absurd inTrailing List.not_mem_nil
    | succ extra inner =>
        rcases List.mem_cons.mp inTrailing with equal | rest
        · subst equal
          exact ⟨rfl, Nat.succ_pos extra⟩
        · exact ⟨(inner rest).1, Nat.succ_pos extra⟩

end LambdaJit.ContextualPreorder
