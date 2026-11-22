import LambdaJit.ContextualPreorderCompleteness

/-!
# The proofs file's theorem A: the parts that do not mention a derivability

The declarations of theorem A of the proofs file, section 20.2, with the approximants made stratified as lemma C0 (section 20.3) does, that
do not mention a derivability relation: free indices, shifting and substitution of stratified
terms and truncations, `bindVariable`, and the free indices of redexes. Theorem A itself, in
⊢_{λ-lattice-η}, is module `LatticeEtaApproximation`.

Formulation choices the proofs file leaves open:

- ⋄ is written Ω, as in module `ContextualPreorderSeparation`, and approximants are kept stratified
  at every step: where the proofs file abstracts an approximant (λx. B, in (CA) and in (L)) or
  substitutes ⋄ into one (app(A) in (L)), the result is made stratified again at once, by the
  rewriting of lemma C0 (T6, T7 and T8) or by truncating a head that became ⋄.
- FV(T′) ⊆ FV(M) is `FreeIncluded`. A fresh variable is a de Bruijn index at or above a bound of
  the free indices, and λx. B binds it by `bindVariable`.
- The substitution M[x⃗ := N⃗] of the basic lemma A4 is the β redex (λx⃗. M) N⃗ (`applyAll` of
  `abstractAll`), equal to it by the β rule, so the lemma needs no simultaneous substitution of
  open terms.
-/

namespace LambdaJit.ContextualPreorder

open LambdaJit.Semantics
open LambdaJit.Semantics.Term

/-! ## Free indices -/

/-- FV(term) ⊆ FV(other). -/
def FreeIncluded (term other : Term) : Prop :=
  ∀ index, OccursFree index term → OccursFree index other

theorem FreeIncluded.transitive {first second third : Term} (firstSecond : FreeIncluded first second)
    (secondThird : FreeIncluded second third) : FreeIncluded first third :=
  fun index occurs => secondThird index (firstSecond index occurs)

/-- The free indices of a shifted term. -/
theorem occursFreeShiftFrom : ∀ (term : Term) (cutoff index : Nat),
    OccursFree index (shiftFrom cutoff term) →
      (index < cutoff ∧ OccursFree index term) ∨ (cutoff < index ∧ OccursFree (index - 1) term)
  | .boundVariable position, cutoff, index, occurs => by
      by_cases below : position < cutoff
      · simp only [shiftFrom, below, ite_true, OccursFree] at occurs
        subst occurs
        exact .inl ⟨below, rfl⟩
      · simp only [shiftFrom, below, ite_false, OccursFree] at occurs
        subst occurs
        exact .inr ⟨by omega, by show position = position + 1 - 1; omega⟩
  | .abstraction body, cutoff, index, occurs => by
      rcases occursFreeShiftFrom body (cutoff + 1) (index + 1) occurs with
        ⟨below, inner⟩ | ⟨above, inner⟩
      · exact .inl ⟨by omega, inner⟩
      · refine .inr ⟨by omega, ?_⟩
        show OccursFree (index - 1 + 1) body
        rw [show index - 1 + 1 = index + 1 - 1 by omega]
        exact inner
  | .application function argument, cutoff, index, occurs => by
      rcases occurs with inner | inner
      · rcases occursFreeShiftFrom function cutoff index inner with ⟨b, found⟩ | ⟨a, found⟩
        · exact .inl ⟨b, .inl found⟩
        · exact .inr ⟨a, .inl found⟩
      · rcases occursFreeShiftFrom argument cutoff index inner with ⟨b, found⟩ | ⟨a, found⟩
        · exact .inl ⟨b, .inr found⟩
        · exact .inr ⟨a, .inr found⟩
  | .choice left right, cutoff, index, occurs => by
      rcases occurs with inner | inner
      · rcases occursFreeShiftFrom left cutoff index inner with ⟨b, found⟩ | ⟨a, found⟩
        · exact .inl ⟨b, .inl found⟩
        · exact .inr ⟨a, .inl found⟩
      · rcases occursFreeShiftFrom right cutoff index inner with ⟨b, found⟩ | ⟨a, found⟩
        · exact .inl ⟨b, .inr found⟩
        · exact .inr ⟨a, .inr found⟩
  | .parallel left right, cutoff, index, occurs => by
      rcases occurs with inner | inner
      · rcases occursFreeShiftFrom left cutoff index inner with ⟨b, found⟩ | ⟨a, found⟩
        · exact .inl ⟨b, .inl found⟩
        · exact .inr ⟨a, .inl found⟩
      · rcases occursFreeShiftFrom right cutoff index inner with ⟨b, found⟩ | ⟨a, found⟩
        · exact .inl ⟨b, .inr found⟩
        · exact .inr ⟨a, .inr found⟩

/-- The free indices of a substitution instance: those of the term below the substituted index,
those above it lowered by one, and those of the replacement. -/
theorem occursFreeSubstitute : ∀ (term : Term) (depth : Nat) (replacement : Term) (index : Nat),
    OccursFree index (substitute depth replacement term) →
      (index < depth ∧ OccursFree index term) ∨ (depth ≤ index ∧ OccursFree (index + 1) term) ∨
        OccursFree index replacement
  | .boundVariable position, depth, replacement, index, occurs => by
      by_cases below : position < depth
      · simp only [substitute, below, ite_true, OccursFree] at occurs
        subst occurs
        exact .inl ⟨below, rfl⟩
      · by_cases equal : position = depth
        · subst equal
          simp only [substitute, Nat.lt_irrefl, ite_false, ite_true] at occurs
          exact .inr (.inr occurs)
        · simp only [substitute, below, equal, ite_false, OccursFree] at occurs
          exact .inr (.inl ⟨by omega, by show position = index + 1; omega⟩)
  | .abstraction body, depth, replacement, index, occurs => by
      rcases occursFreeSubstitute body (depth + 1) (shift replacement) (index + 1) occurs with
        ⟨below, inner⟩ | ⟨above, inner⟩ | inner
      · exact .inl ⟨by omega, inner⟩
      · exact .inr (.inl ⟨by omega, inner⟩)
      · rcases occursFreeShiftFrom replacement 0 (index + 1) inner with ⟨impossible, _⟩ | ⟨_, found⟩
        · omega
        · exact .inr (.inr found)
  | .application function argument, depth, replacement, index, occurs => by
      rcases occurs with inner | inner
      · rcases occursFreeSubstitute function depth replacement index inner with
          ⟨b, found⟩ | ⟨a, found⟩ | found
        · exact .inl ⟨b, .inl found⟩
        · exact .inr (.inl ⟨a, .inl found⟩)
        · exact .inr (.inr found)
      · rcases occursFreeSubstitute argument depth replacement index inner with
          ⟨b, found⟩ | ⟨a, found⟩ | found
        · exact .inl ⟨b, .inr found⟩
        · exact .inr (.inl ⟨a, .inr found⟩)
        · exact .inr (.inr found)
  | .choice left right, depth, replacement, index, occurs => by
      rcases occurs with inner | inner
      · rcases occursFreeSubstitute left depth replacement index inner with
          ⟨b, found⟩ | ⟨a, found⟩ | found
        · exact .inl ⟨b, .inl found⟩
        · exact .inr (.inl ⟨a, .inl found⟩)
        · exact .inr (.inr found)
      · rcases occursFreeSubstitute right depth replacement index inner with
          ⟨b, found⟩ | ⟨a, found⟩ | found
        · exact .inl ⟨b, .inr found⟩
        · exact .inr (.inl ⟨a, .inr found⟩)
        · exact .inr (.inr found)
  | .parallel left right, depth, replacement, index, occurs => by
      rcases occurs with inner | inner
      · rcases occursFreeSubstitute left depth replacement index inner with
          ⟨b, found⟩ | ⟨a, found⟩ | found
        · exact .inl ⟨b, .inl found⟩
        · exact .inr (.inl ⟨a, .inl found⟩)
        · exact .inr (.inr found)
      · rcases occursFreeSubstitute right depth replacement index inner with
          ⟨b, found⟩ | ⟨a, found⟩ | found
        · exact .inl ⟨b, .inr found⟩
        · exact .inr (.inl ⟨a, .inr found⟩)
        · exact .inr (.inr found)

/-- A truncation has no free index its term lacks: Ω is closed. -/
theorem Truncates.freeIncluded {approximant term : Term} (truncates : Truncates approximant term) :
    FreeIncluded approximant term := by
  induction truncates with
  | truncated term => exact fun index occurs => absurd occurs (closedOmega index)
  | boundVariable index => exact fun _ occurs => occurs
  | abstraction _ inner => exact fun index occurs => inner (index + 1) occurs
  | application _ _ functionInner argumentInner =>
      exact fun index occurs => occurs.elim (fun found => .inl (functionInner index found))
        (fun found => .inr (argumentInner index found))
  | choice _ _ leftInner rightInner =>
      exact fun index occurs => occurs.elim (fun found => .inl (leftInner index found))
        (fun found => .inr (rightInner index found))
  | parallel _ _ leftInner rightInner =>
      exact fun index occurs => occurs.elim (fun found => .inl (leftInner index found))
        (fun found => .inr (rightInner index found))

/-- Every term truncates itself. -/
theorem Truncates.reflexive : ∀ term : Term, Truncates term term
  | .boundVariable index => .boundVariable index
  | .abstraction body => .abstraction (Truncates.reflexive body)
  | .application function argument =>
      .application (Truncates.reflexive function) (Truncates.reflexive argument)
  | .choice left right => .choice (Truncates.reflexive left) (Truncates.reflexive right)
  | .parallel left right => .parallel (Truncates.reflexive left) (Truncates.reflexive right)

/-- Truncation is preserved by substituting the same term into both sides. -/
theorem Truncates.substitute {approximant term : Term} (truncates : Truncates approximant term) :
    ∀ (depth : Nat) (replacement : Term),
      Truncates (Term.substitute depth replacement approximant)
        (Term.substitute depth replacement term) := by
  induction truncates with
  | truncated term =>
      intro depth replacement
      rw [substituteClosed closedOmega]
      exact .truncated _
  | boundVariable index => intro depth replacement; exact Truncates.reflexive _
  | abstraction _ inner =>
      intro depth replacement; exact .abstraction (inner (depth + 1) (shift replacement))
  | application _ _ functionInner argumentInner =>
      intro depth replacement
      exact .application (functionInner depth replacement) (argumentInner depth replacement)
  | choice _ _ leftInner rightInner =>
      intro depth replacement
      exact .choice (leftInner depth replacement) (rightInner depth replacement)
  | parallel _ _ leftInner rightInner =>
      intro depth replacement
      exact .parallel (leftInner depth replacement) (rightInner depth replacement)

/-! ## Spines and abstractions under substitution -/

theorem substituteApplyAll (depth : Nat) (replacement : Term) : ∀ (head : Term) (arguments : List Term),
    substitute depth replacement (applyAll head arguments) =
      applyAll (substitute depth replacement head) (arguments.map (substitute depth replacement))
  | _, [] => rfl
  | head, argument :: rest => substituteApplyAll depth replacement (.application head argument) rest

theorem substituteAbstractAll : ∀ (count depth : Nat) (replacement body : Term),
    substitute depth replacement (abstractAll count body) =
      abstractAll count (substitute (depth + count) (shiftTimes count replacement) body)
  | 0, _, _, _ => rfl
  | count + 1, depth, replacement, body => by
      show Term.abstraction (substitute (depth + 1) (shift replacement) (abstractAll count body)) = _
      rw [substituteAbstractAll count (depth + 1) (shift replacement) body, shiftTimesShift,
        Nat.add_right_comm, Nat.add_assoc]
      rfl

theorem shiftTimesClosed {term : Term} (closed : Closed term) : ∀ count, shiftTimes count term = term
  | 0 => rfl
  | count + 1 => by
      show shift (shiftTimes count term) = term
      rw [shiftTimesClosed closed count, shiftClosed closed]

/-- Truncation of spines, argument by argument. -/
theorem truncatesApplyAllOf {head truncatedHead : Term} (headTruncates : Truncates head truncatedHead) :
    ∀ {arguments truncatedArguments : List Term}, TruncatesAll arguments truncatedArguments →
      Truncates (applyAll head arguments) (applyAll truncatedHead truncatedArguments)
  | [], [], _ => headTruncates
  | _ :: _, _ :: _, truncates =>
      truncatesApplyAllOf (.application headTruncates truncates.1) truncates.2
  | [], _ :: _, truncates => truncates.elim
  | _ :: _, [], truncates => truncates.elim

theorem truncatesAbstractAllOf {body truncatedBody : Term} (truncates : Truncates body truncatedBody) :
    ∀ count, Truncates (abstractAll count body) (abstractAll count truncatedBody)
  | 0 => truncates
  | count + 1 => .abstraction (truncatesAbstractAllOf truncates count)

theorem TruncatesAll.append : ∀ {first truncatedFirst : List Term},
    TruncatesAll first truncatedFirst → ∀ {second truncatedSecond : List Term},
      TruncatesAll second truncatedSecond →
        TruncatesAll (first ++ second) (truncatedFirst ++ truncatedSecond)
  | [], [], _, _, _, secondTruncates => secondTruncates
  | _ :: _, _ :: _, firstTruncates, _, _, secondTruncates =>
      ⟨firstTruncates.1, TruncatesAll.append firstTruncates.2 secondTruncates⟩
  | [], _ :: _, firstTruncates, _, _, _ => firstTruncates.elim
  | _ :: _, [], firstTruncates, _, _, _ => firstTruncates.elim

/-! ## Stratification after abstraction and after substituting ⋄ (lemma C0) -/

section Stratification

variable (model : DdLP96Model)

/-- An abstraction over a term that reads ⊥ reads ⊥. -/
theorem DdLP96Model.interpretAbstractAllBottom : ∀ (count : Nat) {body : Term},
    (∀ environment, model.interpret body environment = model.bottom) →
      ∀ environment, model.interpret (abstractAll count body) environment = model.bottom
  | 0, _, bottom => bottom
  | count + 1, _, bottom => fun environment => model.equalOfApply fun value => by
      show model.apply (model.interpret (.abstraction (abstractAll count _)) environment) value = _
      rw [model.interpretAbstraction, DdLP96Model.interpretAbstractAllBottom count bottom,
        model.applyBottom]

/-- Ω applied to anything reads ⊥ (P8). -/
theorem DdLP96Model.interpretApplyAllOmega : ∀ (arguments : List Term)
    (environment : Nat → model.Value),
    model.interpret (applyAll Omega arguments) environment = model.bottom
  | [], environment => model.interpretOmega environment
  | argument :: rest, environment => by
      show model.interpret (applyAll (.application Omega argument) rest) environment = _
      generalize equal : Term.application Omega argument = head
      have headBottom : model.interpret head environment = model.bottom := by
        rw [← equal, model.interpretApplication, model.interpretOmega, model.applyBottom]
      clear equal
      induction rest generalizing head with
      | nil => exact headBottom
      | cons next others inner =>
          exact inner (.application head next) (by
            rw [model.interpretApplication, headBottom, model.applyBottom])

/-- Equal readings of the arguments give equal readings of a head node. -/
theorem DdLP96Model.interpretHeadNodeEqual (abstractions head : Nat) {lowers uppers : List Term}
    (sameLength : lowers.length = uppers.length)
    (pointwise : ∀ (position : Nat) lower upper, lowers[position]? = some lower →
      uppers[position]? = some upper →
        ∀ environment, model.interpret lower environment = model.interpret upper environment)
    (environment : Nat → model.Value) :
    model.interpret (headNode abstractions head lowers) environment =
      model.interpret (headNode abstractions head uppers) environment :=
  model.orderAntisymmetric
    (model.interpretHeadNodeMonotone abstractions head sameLength
      (fun position lower upper lowerFound upperFound environment => by
        rw [pointwise position lower upper lowerFound upperFound environment]
        exact model.orderReflexive _) environment)
    (model.interpretHeadNodeMonotone abstractions head sameLength.symm
      (fun position lower upper lowerFound upperFound environment => by
        rw [pointwise position upper lower upperFound lowerFound environment]
        exact model.orderReflexive _) environment)

/-- Collecting one result per argument of a head node into a list. -/
theorem collectArguments {property : Term → Term → Term → Prop} :
    ∀ {arguments truncatedArguments : List Term}, TruncatesAll arguments truncatedArguments →
      (∀ argument ∈ arguments, ∀ truncated, Truncates argument truncated →
        ∃ result, property argument truncated result) →
      ∃ results : List Term, results.length = arguments.length ∧
        ∀ (position : Nat) argument truncated result, arguments[position]? = some argument →
          truncatedArguments[position]? = some truncated → results[position]? = some result →
            property argument truncated result
  | [], [], _, _ => ⟨[], rfl, fun _ _ _ _ found => by simp at found⟩
  | first :: rest, truncatedFirst :: truncatedRest, truncates, each => by
      obtain ⟨firstResult, firstProperty⟩ := each first List.mem_cons_self truncatedFirst truncates.1
      obtain ⟨restResults, restLength, restProperty⟩ := collectArguments truncates.2
        (fun argument member => each argument (List.mem_cons_of_mem _ member))
      refine ⟨firstResult :: restResults, by simp [restLength], ?_⟩
      intro position argument truncated result argumentFound truncatedFound resultFound
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at argumentFound
          simp only [List.getElem?_cons_zero, Option.some.injEq] at truncatedFound
          simp only [List.getElem?_cons_zero, Option.some.injEq] at resultFound
          subst argumentFound truncatedFound resultFound
          exact firstProperty
      | succ position =>
          simp only [List.getElem?_cons_succ] at argumentFound truncatedFound resultFound
          exact restProperty position argument truncated result argumentFound truncatedFound
            resultFound
  | [], _ :: _, truncates, _ => truncates.elim
  | _ :: _, [], truncates, _ => truncates.elim

/-- Lists related position by position, from a positional property. -/
theorem truncatesAllOfPositions : ∀ {approximants terms : List Term},
    approximants.length = terms.length →
    (∀ (position : Nat) approximant term, approximants[position]? = some approximant →
      terms[position]? = some term → Truncates approximant term) →
    TruncatesAll approximants terms
  | [], [], _, _ => trivial
  | first :: rest, otherFirst :: otherRest, sameLength, positions =>
      ⟨positions 0 first otherFirst rfl rfl,
        truncatesAllOfPositions (by simpa using sameLength)
          (fun position approximant term approximantFound termFound =>
            positions (position + 1) approximant term approximantFound termFound)⟩
  | [], _ :: _, sameLength, _ => absurd sameLength (by simp)
  | _ :: _, [], sameLength, _ => absurd sameLength (by simp)

/-- Substituting ⋄ for a variable in a stratified approximant, made stratified again: a head node
whose head becomes ⋄ becomes ⋄ (the proofs file's ↓, and λx. ⋄ = ⋄). The result truncates the term
with any replacement for the variable, and reads as the approximant with ⋄ substituted. -/
theorem stratifiedSubstituteOmega {approximant : Term} (stratified : Stratified approximant) :
    ∀ {term : Term}, Truncates approximant term → ∀ (depth : Nat) (replacement : Term),
      ∃ newApproximant, Stratified newApproximant ∧
        Truncates newApproximant (substitute depth replacement term) ∧
        ∀ environment, model.interpret newApproximant environment =
          model.interpret (substitute depth Omega approximant) environment := by
  induction stratified with
  | truncated =>
      intro term _ depth replacement
      exact ⟨Omega, .truncated, .truncated _, fun environment => by
        rw [substituteClosed closedOmega]⟩
  | choice _ _ leftInner rightInner =>
      intro term truncates depth replacement
      cases truncates with
      | choice leftTruncates rightTruncates =>
          obtain ⟨leftNew, leftStratified, leftTruncated, leftValue⟩ :=
            leftInner leftTruncates depth replacement
          obtain ⟨rightNew, rightStratified, rightTruncated, rightValue⟩ :=
            rightInner rightTruncates depth replacement
          refine ⟨.choice leftNew rightNew, .choice leftStratified rightStratified,
            .choice leftTruncated rightTruncated, fun environment => ?_⟩
          show _ = model.interpret (.choice (substitute depth Omega _) (substitute depth Omega _)) _
          rw [model.interpretChoice, model.interpretChoice, leftValue, rightValue]
  | parallel _ _ leftInner rightInner =>
      intro term truncates depth replacement
      cases truncates with
      | parallel leftTruncates rightTruncates =>
          obtain ⟨leftNew, leftStratified, leftTruncated, leftValue⟩ :=
            leftInner leftTruncates depth replacement
          obtain ⟨rightNew, rightStratified, rightTruncated, rightValue⟩ :=
            rightInner rightTruncates depth replacement
          refine ⟨.parallel leftNew rightNew, .parallel leftStratified rightStratified,
            .parallel leftTruncated rightTruncated, fun environment => ?_⟩
          show _ = model.interpret (.parallel (substitute depth Omega _) (substitute depth Omega _)) _
          rw [model.interpretParallel, model.interpretParallel, leftValue, rightValue]
  | headNode abstractions head arguments argumentsStratified inner =>
      intro term truncates depth replacement
      obtain ⟨truncatedArguments, rfl, argumentsTruncate⟩ := truncatesHeadNode truncates
      have approximantSubstituted : substitute depth Omega (headNode abstractions head arguments) =
          abstractAll abstractions (applyAll
            (substitute (depth + abstractions) Omega (.boundVariable head))
            (arguments.map (substitute (depth + abstractions) Omega))) := by
        unfold headNode
        rw [substituteAbstractAll, shiftTimesClosed closedOmega, substituteApplyAll]
      have termSubstituted : substitute depth replacement
          (headNode abstractions head truncatedArguments) =
          abstractAll abstractions (applyAll
            (substitute (depth + abstractions) (shiftTimes abstractions replacement)
              (.boundVariable head))
            (truncatedArguments.map (substitute (depth + abstractions)
              (shiftTimes abstractions replacement)))) := by
        unfold headNode
        rw [substituteAbstractAll, substituteApplyAll]
      by_cases atHead : head = depth + abstractions
      · -- The head becomes ⋄: the whole node is ⋄.
        refine ⟨Omega, .truncated, .truncated _, fun environment => ?_⟩
        rw [approximantSubstituted, model.interpretOmega]
        subst atHead
        simp only [substitute, Nat.lt_irrefl, ite_false, ite_true]
        exact (model.interpretAbstractAllBottom abstractions
          (fun environment => model.interpretApplyAllOmega _ environment) environment).symm
      · -- The head stays a variable: the arguments are substituted one by one.
        obtain ⟨newArguments, newLength, newProperty⟩ := collectArguments
          (property := fun argument truncated result => Stratified result ∧
            Truncates result (substitute (depth + abstractions) (shiftTimes abstractions replacement)
              truncated) ∧
            ∀ environment, model.interpret result environment =
              model.interpret (substitute (depth + abstractions) Omega argument) environment)
          argumentsTruncate
          (fun argument member truncated argumentTruncates =>
            inner argument member argumentTruncates (depth + abstractions)
              (shiftTimes abstractions replacement))
        have sameLength := argumentsTruncate.length
        have headSubstituted : ∀ other : Term,
            substitute (depth + abstractions) other (.boundVariable head) =
              .boundVariable (if head < depth + abstractions then head else head - 1) := by
          intro other
          by_cases below : head < depth + abstractions
          · simp [substitute, below]
          · simp [substitute, below, atHead]
        refine ⟨headNode abstractions (if head < depth + abstractions then head else head - 1)
          newArguments, ?_, ?_, ?_⟩
        · refine .headNode _ _ _ fun result member => ?_
          obtain ⟨position, resultFound⟩ := List.mem_iff_getElem?.mp member
          have positionBelow : position < arguments.length := by
            rw [← newLength]
            exact (List.getElem?_eq_some_iff.mp resultFound).1
          obtain ⟨argument, argumentFound⟩ : ∃ argument, arguments[position]? = some argument :=
            ⟨_, List.getElem?_eq_getElem positionBelow⟩
          obtain ⟨truncated, truncatedFound⟩ :
              ∃ truncated, truncatedArguments[position]? = some truncated :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          exact (newProperty position argument truncated result argumentFound truncatedFound
            resultFound).1
        · rw [termSubstituted, headSubstituted]
          apply truncatesAbstractAllOf
          apply truncatesApplyAllOf (.boundVariable _)
          apply truncatesAllOfPositions (by simp [newLength, sameLength])
          intro position result substitutedTruncated resultFound substitutedFound
          rw [List.getElem?_map] at substitutedFound
          rcases truncatedFound : truncatedArguments[position]? with _ | truncated
          · rw [truncatedFound] at substitutedFound
            simp at substitutedFound
          · rw [truncatedFound] at substitutedFound
            simp only [Option.map_some, Option.some.injEq] at substitutedFound
            subst substitutedFound
            have positionBelow : position < arguments.length := by
              rw [← newLength]
              exact (List.getElem?_eq_some_iff.mp resultFound).1
            obtain ⟨argument, argumentFound⟩ : ∃ argument, arguments[position]? = some argument :=
              ⟨_, List.getElem?_eq_getElem positionBelow⟩
            exact (newProperty position argument truncated result argumentFound truncatedFound
              resultFound).2.1
        · intro environment
          rw [approximantSubstituted, headSubstituted]
          apply model.interpretHeadNodeEqual abstractions _ (by simp [newLength])
          intro position result substituted resultFound substitutedFound
          rw [List.getElem?_map] at substitutedFound
          rcases argumentFound : arguments[position]? with _ | argument
          · rw [argumentFound] at substitutedFound
            simp at substitutedFound
          · rw [argumentFound] at substitutedFound
            simp only [Option.map_some, Option.some.injEq] at substitutedFound
            subst substitutedFound
            have positionBelow : position < truncatedArguments.length := by
              rw [← sameLength]
              exact (List.getElem?_eq_some_iff.mp argumentFound).1
            obtain ⟨truncated, truncatedFound⟩ :
                ∃ truncated, truncatedArguments[position]? = some truncated :=
              ⟨_, List.getElem?_eq_getElem positionBelow⟩
            exact (newProperty position argument truncated result argumentFound truncatedFound
              resultFound).2.2

end Stratification

/-! ## Applying an approximant, and abstracting a fresh variable -/

/-- Substituting a variable for a variable keeps a stratified approximant stratified. -/
theorem Stratified.substituteVariable {approximant : Term} (stratified : Stratified approximant) :
    ∀ (depth index : Nat), Stratified (substitute depth (.boundVariable index) approximant) := by
  induction stratified with
  | truncated =>
      intro depth index
      rw [substituteClosed closedOmega]
      exact .truncated
  | choice _ _ leftInner rightInner =>
      intro depth index; exact .choice (leftInner depth index) (rightInner depth index)
  | parallel _ _ leftInner rightInner =>
      intro depth index; exact .parallel (leftInner depth index) (rightInner depth index)
  | headNode abstractions head arguments _ inner =>
      intro depth index
      have substituted : substitute depth (.boundVariable index)
          (ContextualPreorder.headNode abstractions head arguments) =
          abstractAll abstractions (applyAll
            (substitute (depth + abstractions) (.boundVariable (index + abstractions))
              (.boundVariable head))
            (arguments.map (substitute (depth + abstractions)
              (.boundVariable (index + abstractions))))) := by
        unfold ContextualPreorder.headNode
        rw [substituteAbstractAll, shiftTimesVariable, substituteApplyAll]
      have isVariable : ∃ newHead, substitute (depth + abstractions)
          (.boundVariable (index + abstractions)) (.boundVariable head) = .boundVariable newHead := by
        unfold substitute
        split
        · exact ⟨_, rfl⟩
        · split
          · exact ⟨_, rfl⟩
          · exact ⟨_, rfl⟩
      obtain ⟨newHead, headEqual⟩ := isVariable
      rw [substituted, headEqual]
      refine .headNode abstractions newHead _ fun argument member => ?_
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact inner original originalMember _ _

/-- λx. M for a free index x: the index is bound by a new abstraction, the other indices raised
past it. -/
def bindVariable (index : Nat) (term : Term) : Term :=
  substitute (index + 1) (.boundVariable 0) (shift term)

theorem bindVariableApplication {function : Term} {index : Nat}
    (functionFree : FreeBelow index function) :
    bindVariable index (.application function (.boundVariable index)) =
      .application (shift function) (.boundVariable 0) := by
  have shiftedFree := freeBelowShiftFrom function 0 functionFree
  have unchanged : substitute (index + 1) (.boundVariable 0) (shift function) = shift function :=
    substituteUnchanged _ _ _ fun other atLeast occurs => by
      have := shiftedFree other occurs
      omega
  show Term.application (substitute (index + 1) (.boundVariable 0) (shift function))
    (substitute (index + 1) (.boundVariable 0) (shiftFrom 0 (.boundVariable index))) = _
  rw [unchanged]
  simp [shiftFrom, substitute]

/-- The free indices of λx. T for the fresh x of an application M x: those of M. -/
theorem freeIncludedBindVariable {function term : Term} {index : Nat}
    (functionFree : FreeBelow index function)
    (included : FreeIncluded term (.application function (.boundVariable index))) :
    FreeIncluded (.abstraction (bindVariable index term)) function := by
  intro other occurs
  rcases occursFreeSubstitute (shift term) (index + 1) (.boundVariable 0) (other + 1) occurs with
    ⟨below, inner⟩ | ⟨atLeast, inner⟩ | inner
  · rcases occursFreeShiftFrom term 0 (other + 1) inner with ⟨impossible, _⟩ | ⟨_, found⟩
    · omega
    · rcases included other found with inFunction | isIndex
      · exact inFunction
      · simp only [OccursFree] at isIndex
        omega
  · rcases occursFreeShiftFrom term 0 (other + 1 + 1) inner with ⟨impossible, _⟩ | ⟨_, found⟩
    · omega
    · rcases included (other + 1) found with inFunction | isIndex
      · have := functionFree (other + 1) inFunction
        omega
      · simp only [OccursFree] at isIndex
        omega
  · simp only [OccursFree] at inner
    omega

theorem Truncates.bindVariable {approximant term : Term} (truncates : Truncates approximant term)
    (index : Nat) :
    Truncates (ContextualPreorder.bindVariable index approximant)
      (ContextualPreorder.bindVariable index term) :=
  (truncates.shiftFrom 0).substitute _ _

section Application

variable (model : DdLP96Model)

/-- λx. T with x fresh reads, applied to the value of x, as T. -/
theorem DdLP96Model.interpretBindVariable {term : Term} {index : Nat}
    (free : FreeBelow (index + 1) term) (environment : Nat → model.Value) :
    model.interpret (bindVariable index term) (extendEnvironment (environment index) environment) =
      model.interpret term environment := by
  unfold bindVariable
  rw [model.interpretSubstitute, model.interpretVariable]
  show model.interpret (shift term) (DdLP96Model.insertEnvironment (index + 1) (environment index)
    (extendEnvironment (environment index) environment)) = _
  rw [← DdLP96Model.extendInsertEnvironment, model.interpretShift]
  apply model.interpretAgree
  intro other occurs
  have below := free other occurs
  unfold DdLP96Model.insertEnvironment
  by_cases strictly : other < index
  · simp [strictly]
  · have equal : other = index := by omega
    subst equal
    simp

end Application

/-! ## A fresh index with a compact value (the proofs file, 20.2) -/

namespace DdLP96Model

variable (model : DdLP96Model)

/-- A fresh index with a given compact value in ρ₀, beyond the free indices of a term. -/
theorem freshIndex {level : Nat} {value : model.Value} (compact : model.Compact level value)
    (term : Term) : ∃ index, FreeBelow index term ∧ model.richEnvironment index = value := by
  obtain ⟨bound, free⟩ := freeBound term
  obtain ⟨index, atLeast, equal⟩ := model.richEnvironmentRich level value compact bound
  exact ⟨index, fun other occurs => Nat.lt_of_lt_of_le (free other occurs) atLeast, equal⟩

end DdLP96Model

/-! ## The substitution of the basic lemma as a β redex -/

/-- (λx₁ … xₖ. M) N₁ … Nₖ, standing for M[x⃗ := N⃗]; the outermost λ takes N₁, so index i of M
stands for N_{k−i} (from 1). -/
def redex (arguments : List Term) (term : Term) : Term :=
  applyAll (abstractAll arguments.length term) arguments

theorem abstractAllAbstraction : ∀ (count : Nat) (body : Term),
    abstractAll count (.abstraction body) = abstractAll (count + 1) body
  | 0, _ => rfl
  | count + 1, body => by
      show Term.abstraction (abstractAll count (.abstraction body)) =
        Term.abstraction (abstractAll (count + 1) body)
      rw [abstractAllAbstraction count body]

/-- A shift does not move indices below its cutoff, so between two cutoffs with no free index in
between, the two shifts agree. -/
theorem shiftFromCutoffs : ∀ (term : Term) {lower upper : Nat}, lower ≤ upper →
    (∀ index, lower ≤ index → index < upper → ¬ OccursFree index term) →
      shiftFrom lower term = shiftFrom upper term
  | .boundVariable index, lower, upper, ordered, absent => by
      by_cases below : index < lower
      · have belowUpper : index < upper := by omega
        simp [shiftFrom, below, belowUpper]
      · have notBelowUpper : ¬ index < upper := fun belowUpper => absent index (by omega) belowUpper rfl
        simp [shiftFrom, below, notBelowUpper]
  | .abstraction body, lower, upper, ordered, absent => by
      show Term.abstraction (shiftFrom (lower + 1) body) = Term.abstraction (shiftFrom (upper + 1) body)
      rw [shiftFromCutoffs body (lower := lower + 1) (upper := upper + 1) (by omega)
        fun index atLeast below occurs => by
        apply absent (index - 1) (by omega) (by omega)
        show OccursFree (index - 1 + 1) body
        rw [show index - 1 + 1 = index by omega]
        exact occurs]
  | .application function argument, lower, upper, ordered, absent => by
      show Term.application (shiftFrom lower function) (shiftFrom lower argument) =
        Term.application (shiftFrom upper function) (shiftFrom upper argument)
      rw [shiftFromCutoffs function ordered fun index atLeast below occurs =>
          absent index atLeast below (.inl occurs),
        shiftFromCutoffs argument ordered fun index atLeast below occurs =>
          absent index atLeast below (.inr occurs)]
  | .choice left right, lower, upper, ordered, absent => by
      show Term.choice (shiftFrom lower left) (shiftFrom lower right) =
        Term.choice (shiftFrom upper left) (shiftFrom upper right)
      rw [shiftFromCutoffs left ordered fun index atLeast below occurs =>
          absent index atLeast below (.inl occurs),
        shiftFromCutoffs right ordered fun index atLeast below occurs =>
          absent index atLeast below (.inr occurs)]
  | .parallel left right, lower, upper, ordered, absent => by
      show Term.parallel (shiftFrom lower left) (shiftFrom lower right) =
        Term.parallel (shiftFrom upper left) (shiftFrom upper right)
      rw [shiftFromCutoffs left ordered fun index atLeast below occurs =>
          absent index atLeast below (.inl occurs),
        shiftFromCutoffs right ordered fun index atLeast below occurs =>
          absent index atLeast below (.inr occurs)]

/-- A term shifted k times has no free index below k. -/
theorem occursFreeShiftTimes : ∀ (count : Nat) (term : Term) (index : Nat),
    OccursFree index (shiftTimes count term) → count ≤ index
  | 0, _, _, _ => Nat.zero_le _
  | count + 1, term, index, occurs => by
      rcases occursFreeShiftFrom (shiftTimes count term) 0 index occurs with
        ⟨impossible, _⟩ | ⟨positive, found⟩
      · omega
      · have := occursFreeShiftTimes count term (index - 1) found
        omega

/-- Substituting at index d into a term shifted d + 1 times removes one shift. -/
theorem substituteShiftTimes (depth : Nat) (replacement term : Term) :
    substitute depth replacement (shiftTimes (depth + 1) term) = shiftTimes depth term := by
  show substitute depth replacement (shiftFrom 0 (shiftTimes depth term)) = _
  rw [shiftFromCutoffs _ (Nat.zero_le depth) fun index _ below occurs => by
    have := occursFreeShiftTimes depth term index occurs
    omega]
  exact substituteShiftFromCancel _ _ _

/-- Free indices pass from the head of a spine to the spine. -/
theorem occursFreeApplyAllHead {index : Nat} : ∀ {head : Term} (arguments : List Term),
    OccursFree index head → OccursFree index (applyAll head arguments)
  | _, [], occurs => occurs
  | _, _ :: rest, occurs => occursFreeApplyAllHead (head := .application _ _) rest (.inl occurs)

/-- Free indices pass from an argument of a spine to the spine. -/
theorem occursFreeApplyAllArgument {index : Nat} : ∀ {head : Term} {arguments : List Term}
    {argument : Term}, argument ∈ arguments → OccursFree index argument →
      OccursFree index (applyAll head arguments)
  | _, [], _, member, _ => absurd member List.not_mem_nil
  | _, first :: rest, argument, member, occurs => by
      rcases List.mem_cons.mp member with equal | inRest
      · subst equal
        exact occursFreeApplyAllHead (head := .application _ _) rest (.inr occurs)
      · exact occursFreeApplyAllArgument (head := .application _ first) inRest occurs

/-- The free indices of a spine are its head's and its arguments'. -/
theorem occursFreeApplyAllCases {index : Nat} : ∀ {head : Term} {arguments : List Term},
    OccursFree index (applyAll head arguments) →
      OccursFree index head ∨ ∃ argument ∈ arguments, OccursFree index argument
  | _, [], occurs => .inl occurs
  | _, first :: rest, occurs => by
      rcases occursFreeApplyAllCases (head := .application _ first) occurs with
        found | ⟨argument, member, found⟩
      · rcases found with inHead | inFirst
        · exact .inl inHead
        · exact .inr ⟨first, List.mem_cons_self, inFirst⟩
      · exact .inr ⟨argument, List.mem_cons_of_mem _ member, found⟩

/-- A redex over a term bound by its abstractions has only its arguments' free indices. -/
theorem redexFreeIncluded {arguments : List Term} {term : Term}
    (free : FreeBelow arguments.length term) (other : Term) :
    FreeIncluded (redex arguments term) (redex arguments other) := by
  intro index occurs
  rcases occursFreeApplyAllCases occurs with inAbstraction | ⟨argument, member, found⟩
  · have := free _ ((occursFreeAbstractAll _ _ _).mp inAbstraction)
    omega
  · exact occursFreeApplyAllArgument member found

end LambdaJit.ContextualPreorder
