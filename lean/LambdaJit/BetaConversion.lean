import LambdaJit.ContextualPreorderSeparation
import LambdaJit.LatticeEtaDerivability

/-!
# A search for a β reduction, and its soundness in ⊢_{λ-lattice-η}

The e-graph unites two terms by β conversion where it reduced several β redexes at once: the
higher-order matching's expansions and normal forms, and the higher-order saturator's root
reverse β (`gezi.egraph.Justification.BetaConversion`, which names the node the other reduces
to). The steps are not recorded: the normal form is computed on values
(`gezi.ir.BindingNormalForm`), and the redexes lie under abstractions, inside the codes of
thunks, where the article's first-order encoding has no binder. So an article states such a union
as one import equation, the side that reduces on the left, and the checker decides it here.

`betaReduces fuel left right` searches for β steps from `left` to `right`, a step taken anywhere:
under an abstraction and on either side of an application, a choice or a parallel. It compares the
two constructor by constructor; where `left` has a head redex (`headContracted`) and `right` an
application spine of the same length whose head is an abstraction too, it compares them so first,
and otherwise, or when that fails, contracts the redex. Only `left` is reduced: the writer orients
each equation, so the search does not reduce the side that is already the reduct, which for the
root reverse β is a whole program. It answers `true` only when it has found the steps, so
`betaReducesDerivable` makes every accepted pair an equation of ⊢_{λ-lattice-η}, by the β rule, the
congruence under λ (ξ) and the congruences of a congruence. It answers `false` when the fuel runs
out first, and on two terms equal only up to the η rule: that rejects an article, and accepts no
wrong equation.
-/

namespace LambdaJit.Semantics

open Term (instantiate)
open LambdaJit.ContextualPreorder (termSize)

/-- The term with its head redex contracted: `(λx. M) N` is `M[x := N]`, and the head redex of
`F A` is the head redex of `F`; `none` when the term has no head redex. -/
def headContracted : Term → Option Term
  | .application function argument =>
      match function with
      | .abstraction body => some (instantiate body argument)
      | _ => (headContracted function).map (fun reduced => .application reduced argument)
  | _ => none

/-- Whether two terms of one constructor have parts that `joins` accepts, pair by pair, or are one
variable; `false` for two terms of different constructors. -/
def partsJoin (joins : Term → Term → Bool) : Term → Term → Bool
  | .boundVariable leftIndex, .boundVariable rightIndex => leftIndex == rightIndex
  | .abstraction leftBody, .abstraction rightBody => joins leftBody rightBody
  | .application leftFunction leftArgument, .application rightFunction rightArgument =>
      joins leftFunction rightFunction && joins leftArgument rightArgument
  | .choice leftFirst leftSecond, .choice rightFirst rightSecond =>
      joins leftFirst rightFirst && joins leftSecond rightSecond
  | .parallel leftFirst leftSecond, .parallel rightFirst rightSecond =>
      joins leftFirst rightFirst && joins leftSecond rightSecond
  | _, _ => false

/-- The number of arguments of a term's application spine and whether its head is an
abstraction: the shape a redex keeps while no step contracts it. -/
def spineShape : Term → Nat × Bool
  | .application function _ => ((spineShape function).1 + 1, (spineShape function).2)
  | .abstraction _ => (0, true)
  | _ => (0, false)

/-- Whether `left` reaches `right` by β steps, within `fuel` levels of comparisons and
contractions: where `left` has no head redex, their parts reach pair by pair; where it has one,
their parts reach when the two spines have one shape, or else the contracted `left` reaches
`right`. -/
def betaReduces : Nat → Term → Term → Bool
  | 0, left, right => left == right
  | fuel + 1, left, right =>
      match headContracted left with
      | some reduced =>
          (spineShape left == spineShape right && partsJoin (betaReduces fuel) left right) ||
            betaReduces fuel reduced right
      | none => partsJoin (betaReduces fuel) left right

/-- The fuel the checker gives a reduction at most: eight levels for every node of the two sides. A
bound on the search, chosen, not measured; a conversion that needs more is rejected. -/
def conversionFuel (left right : Term) : Nat :=
  8 * (termSize left + termSize right)

/-- `betaReduces` by iterative deepening: with the fuel 1, 2, 4 and so on, the first power of two at
least `limit` the last. The search is depth first, so with more fuel than it needs it goes deeper
into a comparison that fails before it turns back: measured 2026-11-17 on a root reverse β of
the entry `wren` (two sides of 47,472 nodes, `lean --run`), the fuel 8 accepts in 3 s and the fuel 16 in
53 s. Deepening costs about what the least sufficient fuel costs. -/
def betaReducesDeepening (limit : Nat) (left right : Term) : Bool :=
  (List.range (Nat.log2 limit + 2)).any fun exponent => betaReduces (2 ^ exponent) left right

namespace DerivableLatticeEta

variable {hypotheses : Term → Term → Prop}

/-- A contraction of the head redex is a β step in its context, under any hypotheses. -/
theorem headContractedDerivable : ∀ {term reduced : Term},
    headContracted term = some reduced → DerivableLatticeEta hypotheses term reduced
  | .application function argument, reduced, contracted => by
      cases function with
      | abstraction body =>
          simp only [headContracted, Option.some.injEq] at contracted
          subst contracted
          exact .beta body argument
      | boundVariable _ => simp [headContracted] at contracted
      | application innerFunction innerArgument =>
          simp only [headContracted, Option.map_eq_some_iff] at contracted
          obtain ⟨innerReduced, innerContracted, rebuilt⟩ := contracted
          subst rebuilt
          exact congruenceFunction argument (headContractedDerivable innerContracted)
      | choice _ _ => simp [headContracted] at contracted
      | parallel _ _ => simp [headContracted] at contracted
  | .boundVariable _, _, contracted | .abstraction _, _, contracted | .choice _ _, _, contracted
  | .parallel _ _, _, contracted => by simp [headContracted] at contracted

/-- Two terms whose parts `joins` accepts are derivably equal, given that the accepted parts are. -/
theorem partsJoinDerivable {joins : Term → Term → Bool}
    (parts : ∀ {first second : Term}, joins first second = true →
      DerivableLatticeEta hypotheses first second) :
    ∀ {left right : Term}, partsJoin joins left right = true → DerivableLatticeEta hypotheses left right
  | .boundVariable leftIndex, .boundVariable _, accepted => by
      simp only [partsJoin, beq_iff_eq] at accepted
      subst accepted
      exact reflexive (.boundVariable leftIndex)
  | .abstraction _, .abstraction _, accepted => .congruenceAbstraction (parts accepted)
  | .application _ _, .application _ _, accepted => by
      simp only [partsJoin, Bool.and_eq_true] at accepted
      exact .transitive (congruenceFunction _ (parts accepted.1)) (.congruenceArgument _ (parts accepted.2))
  | .choice _ _, .choice _ _, accepted => by
      simp only [partsJoin, Bool.and_eq_true] at accepted
      exact congruenceChoice (parts accepted.1) (parts accepted.2)
  | .parallel _ _, .parallel _ _, accepted => by
      simp only [partsJoin, Bool.and_eq_true] at accepted
      exact .transitive (congruenceParallelLeft _ (parts accepted.1))
        (congruenceParallelRight _ (parts accepted.2))
  | .boundVariable _, .abstraction _, accepted | .boundVariable _, .application _ _, accepted
  | .boundVariable _, .choice _ _, accepted | .boundVariable _, .parallel _ _, accepted
  | .abstraction _, .boundVariable _, accepted
  | .abstraction _, .application _ _, accepted | .abstraction _, .choice _ _, accepted
  | .abstraction _, .parallel _ _, accepted | .application _ _, .boundVariable _, accepted
  | .application _ _, .abstraction _, accepted | .application _ _, .choice _ _, accepted
  | .application _ _, .parallel _ _, accepted | .choice _ _, .boundVariable _, accepted
  | .choice _ _, .abstraction _, accepted | .choice _ _, .application _ _, accepted
  | .choice _ _, .parallel _ _, accepted | .parallel _ _, .boundVariable _, accepted
  | .parallel _ _, .abstraction _, accepted | .parallel _ _, .application _ _, accepted
  | .parallel _ _, .choice _ _, accepted => by simp [partsJoin] at accepted

/-- Two terms that `betaReduces` accepts, with any fuel, are equal in ⊢_{λ-lattice-η} under any
hypotheses: every step of the search is a β step in a context or a congruence. -/
theorem betaReducesDerivable : ∀ (fuel : Nat) {left right : Term},
    betaReduces fuel left right = true → DerivableLatticeEta hypotheses left right
  | 0, left, right, accepted => by
      simp only [betaReduces, beq_iff_eq] at accepted
      subst accepted
      exact reflexive left
  | fuel + 1, left, right, accepted => by
      have parts : ∀ {first second : Term}, betaReduces fuel first second = true →
          DerivableLatticeEta hypotheses first second :=
        fun joined => betaReducesDerivable fuel joined
      simp only [betaReduces] at accepted
      cases contracted : headContracted left with
      | some reduced =>
          simp only [contracted, Bool.or_eq_true, Bool.and_eq_true] at accepted
          rcases accepted with ⟨_, structural⟩ | rest
          · exact partsJoinDerivable parts structural
          · exact .transitive (headContractedDerivable contracted) (parts rest)
      | none =>
          simp only [contracted] at accepted
          exact partsJoinDerivable parts accepted

/-- Two terms that `betaReducesDeepening` accepts are equal in ⊢_{λ-lattice-η}: one of its rounds
accepts them. -/
theorem betaReducesDeepeningDerivable {limit : Nat} {left right : Term}
    (accepted : betaReducesDeepening limit left right = true) :
    DerivableLatticeEta hypotheses left right := by
  simp only [betaReducesDeepening, List.any_eq_true] at accepted
  obtain ⟨exponent, _, reduces⟩ := accepted
  exact betaReducesDerivable _ reduces

end DerivableLatticeEta

/-! The search on a redex under an abstraction and on a redex whose contraction makes another, both
checked by the kernel, so a change that loses either fails the build. -/

/-- λz. (λx. x) z reduces to λz. z: the redex is under the abstraction. -/
example :
    betaReduces 16 (.abstraction (.application (.abstraction (.boundVariable 0)) (.boundVariable 0)))
      (.abstraction (.boundVariable 0)) = true := by decide +kernel

/-- (λx. x x) (λy. y) reduces to λy. y in two contractions at the head, inside a parallel compared
part by part. -/
example :
    betaReduces 32
      (.parallel
        (.application (.abstraction (.application (.boundVariable 0) (.boundVariable 0)))
          (.abstraction (.boundVariable 0)))
        (.abstraction (.boundVariable 0)))
      (.parallel (.abstraction (.boundVariable 0)) (.abstraction (.boundVariable 0))) = true := by
  decide +kernel

end LambdaJit.Semantics
