import LambdaJit.StatementNormalisation
import LambdaJit.ParallelTypesTheorems

/-!
# Hand-written proofs of library lemmas that no decision proves

The command `lemma_soundness` (module `LemmaSoundness`) declares the soundness of a lemma that the
Lean module written by `lean_statements_exported/1` of `gezi/prolog/gezi/lean_statements.pl`
exports. Before it asks the kernel to evaluate the decisions of module `StatementNormalisation`, it
looks up a hand-written proof here, by this naming rule:

- the proof of the lemma `Name` is the theorem
  `LambdaJit.LibraryLemmaProofs.«Name»`, the exported soundness declaration
  `LambdaJit.Exported.«Name»` with the namespace `LambdaJit.Exported` replaced by
  `LambdaJit.LibraryLemmaProofs`;
- it states `EndToEnd.EquationDerivable` of its own copy of the lemma's statement,
  `LambdaJit.LibraryLemmaProofs.Statement.«Name»`, copied from the export: the two sides
  are derivable by ⊢_{λ-lattice-η} under every valuation, which gives their soundness
  (`EndToEnd.equationSoundOfDerivable`); or it states `EndToEnd.EquationSound` of that copy, the
  soundness itself, for a lemma that is sound by Definition 14 and that ⊢_{λ-lattice-η} does
  not derive.

The command declares the exported lemma as a theorem from that proof when the elaborator finds the
proof's type definitionally equal to the derivability or to the soundness of the exported
statement, and fails with an error when it finds neither: a copy that no longer matches the export,
after a change of the library or of the encoding, stops the build of the exported module instead of
becoming an axiom.

The statements here are those of the three lemmas of `parallel_types.pl`, the four of
`filtered_recursion_naturals.pl` and the five of `contracts.pl`
(`gezi/corpora/standard_library`). Their sides unfold `nat_type`, `nat_fold` or `fixpoint`,
so that neither the normaliser nor leftmost outermost contraction joins them within the fuels of
module `StatementNormalisation` (measured 2026-10-07: neither within 60 contractions on a side),
and ten of them need the numbered equations; `natural_double_as_fold` and `unary_as_fold` need
the β rule only, under a congruence that stops the unfolding of the fixpoint. Each proof joins the
statement to a theorem of module `ParallelTypesTheorems`, or to a short derivation written here,
about the terms of `Semantics` with the library's defines written by hand: it takes a derivation
between two such terms and two runs of a search, which the kernel evaluates (`decide +kernel`),
from each side of the statement with its metavariables abstracted
(`StatementNormalisation.abstracted`) to the term of its side. There are two searches:

- `linked`, for the lemmas of `parallel_types.pl` and `contracts.pl`: equality, one normal form
  within `linkNormalisationFuel` contractions (module `Normalisation`), the congruence of a
  constructor, or one leftmost outermost contraction of its left term, tried in that order at
  every level, `linkedSound` proving what it finds. It tries every alternative at every level, so
  its cost grows exponentially with its fuel: on a side of `nat_fold_filtered_contract` it fails
  at fuel 16 and does not finish within 200 seconds at fuel 20, compiled (measured 2026-10-07).
- `headLinked`, for the four lemmas of `filtered_recursion_naturals.pl`: it contracts a side only
  at a head redex, such as the redex that the interpretation of the constant `apply`, λf.λx. f x,
  makes with its arguments, and compares the terms by congruence when both or neither have a head redex, so
  that a fixpoint the two sides share is compared rather than unfolded; `headLinkedSound` proves
  what it finds. At fuel 100 it joins each of the eight sides (measured 2026-10-07: about 30
  milliseconds a side, compiled; about 4 seconds a side in the kernel).

A metavariable of a lemma is a variable bound by one of the abstractions around the abstracted
side, one abstraction for each occurrence of the metavariable in the list of the variables of the
left side and then of the right side (`Interpretation.termVariables`), and the hand-written term
reads it as the variable of the abstraction of its first occurrence.
-/

namespace LambdaJit.LibraryLemmaProofs

open LambdaJit.Semantics
open LambdaJit.Semantics.Term
open LambdaJit.Interpretation (termVariables)
open LambdaJit.StatementNormalisation (abstracted equationDerivableOfAbstractedDerivable
  derivableUnderAbstractions)
open LambdaJit.EndToEnd (EquationDerivable)
open LambdaJit.Readback (abstractions)

/-! ## The statements, copied from the export -/

namespace Statement

/-- The statement of the lemma `successor_filtered` of the knowledge module `parallel_types`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «successor_filtered» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
            (.application
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))) }

/-- The statement of the lemma `successor_filtered_chained` of the knowledge module `parallel_types`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «successor_filtered_chained» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
            (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
          (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))) }

/-- The statement of the lemma `natural_double_as_fold` of the knowledge module `parallel_types`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «natural_double_as_fold» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 0) (.apply (.slot 1) (.slot 2)))) [.slot 2] [(.slot 2), (.slot 3)])), [.slot 3, .slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])) [.slot 3, .slot 0] [(.slot 1), (.slot 2)])), [.slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))) }

/-- The statement of the lemma `zero_filtered` of the knowledge module `contracts`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «zero_filtered» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
    right := (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])) }

/-- The statement of the lemma `true_filtered` of the knowledge module `contracts`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «true_filtered» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.slot 0), [.ignored, .slot 0])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "choice"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
    right := (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])) }

/-- The statement of the lemma `false_filtered` of the knowledge module `contracts`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «false_filtered» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.slot 0), [.ignored, .slot 0])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "choice"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
    right := (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])) }

/-- The statement of the lemma `filter_nat_idempotent` of the knowledge module `contracts`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «filter_nat_idempotent» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
        (.application
          (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
            (.application
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))),
    right := (.application
        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.application
            (.application
              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))) }

/-- The statement of the lemma `unary_as_fold` of the knowledge module `contracts`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «unary_as_fold» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])), [.slot 3, .slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])) [.slot 3, .slot 0] [(.slot 1), (.slot 2)])), [.slot 1, .slot 2])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))) }

/-- The statement of the lemma `nat_fold_filtered_contract` of the knowledge module `filtered_recursion_naturals`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «nat_fold_filtered_contract» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "6"⟩, (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 3) (.apply (.apply (.slot 4) (.slot 5)) (.slot 1)))), [.slot 2, .slot 5]),
      (⟨["LambdaJit", "thunk"], "7"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])) [.slot 3, .slot 0] [(.slot 1), (.slot 2)])), [.slot 1, .slot 2])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.application
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                  (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
        (.application
          (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
            (.application
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))) }

/-- The statement of the lemma `nat_fold_filtered_contract_chained` of the knowledge module `filtered_recursion_naturals`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «nat_fold_filtered_contract_chained» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "6"⟩, (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 3) (.apply (.apply (.slot 4) (.slot 5)) (.slot 1)))), [.slot 2, .slot 5]),
      (⟨["LambdaJit", "thunk"], "7"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])) [.slot 3, .slot 0] [(.slot 1), (.slot 2)])), [.slot 1, .slot 2])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.application
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
            (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                  (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
          (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))) }

/-- The statement of the lemma `nat_fold_filtered_branch` of the knowledge module `filtered_recursion_naturals`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «nat_fold_filtered_branch» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])) [.slot 3, .slot 0] [(.slot 1), (.slot 2)])), [.slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 3) (.apply (.apply (.slot 4) (.slot 5)) (.slot 1)))), [.slot 2, .slot 5]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "6"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "7"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
            (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "choice"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
            (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])]))
                        (.application
                          (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                  (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))) }

/-- The statement of the lemma `nat_fold_filtered_branch_in_context` of the knowledge module `filtered_recursion_naturals`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «nat_fold_filtered_branch_in_context» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 2), (.slot 3)])) [.slot 3, .slot 0] [(.slot 1), (.slot 2)])), [.slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) (.apply (.slot 3) (.apply (.apply (.slot 4) (.slot 5)) (.slot 1)))), [.slot 2, .slot 5]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.choice (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "6"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "7"⟩, (.apply (.slot 0) (.apply (.slot 1) (.slot 2))), [.slot 0, .slot 1, .slot 2])],
    left := (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
              (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))),
    right := (.application
        (.application
          (.constant ⟨["LambdaJit"], "choice"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                  (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])]))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                        (.application
                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                        (.application
                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                    (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
            (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))) }

end Statement

/-! ## A search for a derivation -/

/-- The fuel of the normaliser in `sameNormalForm`, on each side. -/
def linkNormalisationFuel : Nat := 60

/-- Whether the normaliser brings `left` and `right` to one normal form within
`linkNormalisationFuel` contractions on each side. -/
def sameNormalForm (left right : Term) : Bool :=
  match normalise linkNormalisationFuel left, normalise linkNormalisationFuel right with
  | some leftNormal, some rightNormal => leftNormal == rightNormal
  | _, _ => false

/-- Two terms with one normal form are equal by ⊢_{λ-lattice-η} from any hypotheses
(`Semantics.derivableOfNormaliseEqual`). -/
theorem derivableOfSameNormalForm {hypotheses : Term → Term → Prop} {left right : Term}
    (same : sameNormalForm left right = true) : DerivableLatticeEta hypotheses left right := by
  unfold sameNormalForm at same
  split at same
  · rename_i leftNormal rightNormal leftNormalised rightNormalised
    simp only [beq_iff_eq] at same
    subst same
    exact (derivableOfNormaliseEqual leftNormalised rightNormalised)
  · cases same

/-- A search for a derivation of `left` = `right`, at most `fuel` levels deep: the two terms are
equal; or they have one normal form (`sameNormalForm`); or they are one constructor, an
application, an abstraction, a choice or a parallel, and the search links their operands in order;
or `left` has a leftmost outermost redex and the search links its contractum to `right`. -/
def linked : Nat → Term → Term → Bool
  | 0, left, right => left == right
  | fuel + 1, left, right =>
      left == right
      || sameNormalForm left right
      || (match left, right with
          | .application leftFunction leftArgument, .application rightFunction rightArgument =>
              linked fuel leftFunction rightFunction && linked fuel leftArgument rightArgument
          | .abstraction leftBody, .abstraction rightBody => linked fuel leftBody rightBody
          | .choice leftFirst leftSecond, .choice rightFirst rightSecond =>
              linked fuel leftFirst rightFirst && linked fuel leftSecond rightSecond
          | .parallel leftFirst leftSecond, .parallel rightFirst rightSecond =>
              linked fuel leftFirst rightFirst && linked fuel leftSecond rightSecond
          | _, _ => false)
      || (match step left with
          | some contracted => linked fuel contracted right
          | none => false)

/-- What `linked` finds is a derivation: reflexivity, `derivableOfSameNormalForm`, the
congruences of `DerivableLatticeEta`, and the β rule or the η rule of a contraction (`Semantics.stepSound`), joined
by transitivity. -/
theorem linkedSound {hypotheses : Term → Term → Prop} :
    ∀ {fuel : Nat} {left right : Term}, linked fuel left right = true →
      DerivableLatticeEta hypotheses left right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right equal
      simp only [linked, beq_iff_eq] at equal
      subst equal
      exact .reflexive _
  | succ remaining remainingSound =>
      intro left right found
      simp only [linked, Bool.or_eq_true, beq_iff_eq] at found
      rcases found with ((same | normal) | congruent) | stepped
      · subst same
        exact .reflexive _
      · exact derivableOfSameNormalForm normal
      · split at congruent
        · simp only [Bool.and_eq_true] at congruent
          exact .transitive (.congruenceFunction _ (remainingSound congruent.1))
            (.congruenceArgument _ (remainingSound congruent.2))
        · exact .congruenceAbstraction (remainingSound congruent)
        · simp only [Bool.and_eq_true] at congruent
          exact .transitive (.congruenceChoiceLeft _ (remainingSound congruent.1))
            (.congruenceChoiceRight _ (remainingSound congruent.2))
        · simp only [Bool.and_eq_true] at congruent
          exact .transitive (.congruenceParallelLeft _ (remainingSound congruent.1))
            (.congruenceParallelRight _ (remainingSound congruent.2))
        · cases congruent
      · split at stepped
        · rename_i contracted contractedEqual
          exact .transitive (stepSound contractedEqual) (remainingSound stepped)
        · cases stepped

/-- A statement is derivable under every valuation when `linked` joins each of its sides, with its
variables abstracted, to a
term, and ⊢_{λ-lattice-η} derives the equation of the two terms from no hypothesis. -/
theorem statementDerivableOfLinked {statement : EndToEnd.Statement} {fuel : Nat}
    {leftTerm rightTerm : Term}
    (leftLinked : linked fuel
      (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right) statement.left)
      leftTerm = true)
    (rightLinked : linked fuel
      (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right) statement.right)
      rightTerm = true)
    (derived : DerivableLatticeEta (fun _ _ => False) leftTerm rightTerm) :
    EquationDerivable statement.signature statement.left statement.right :=
  equationDerivableOfAbstractedDerivable
    (.transitive (linkedSound leftLinked) (.transitive derived (.symmetric (linkedSound rightLinked))))

/-! ## A search guided by head redexes -/

/-- The term at the head of the application spine of `term`: `term` itself when it is no
application, else the head of its function. -/
def spineHead : Term → Term
  | .application function _ => spineHead function
  | term => term

/-- The number of arguments on the application spine of `term`. -/
def spineLength : Term → Nat
  | .application function _ => spineLength function + 1
  | _ => 0

/-- Whether `term` has a beta redex at its head: an abstraction applied to at least one argument at
the head of its spine, so that leftmost outermost contraction contracts that redex. -/
def headIsRedex (term : Term) : Bool :=
  match spineHead term with
  | .abstraction _ => spineLength term != 0
  | _ => false

/-- Whether `headLinked` may compare `left` and `right` by the congruence of their constructor: both
or neither have a head redex, and when both do, their spines have one length. -/
def congruenceFirst (left right : Term) : Bool :=
  headIsRedex left == headIsRedex right && (!headIsRedex left || spineLength left == spineLength right)

/-- A search for a derivation of `left` = `right`, at most `fuel` levels deep, that contracts head
redexes before it compares: the two terms are equal; or `congruenceFirst` holds, they are one
constructor, and the search links their operands in order; or `left` has a head redex and the
search links its leftmost outermost contractum to `right`; or only `right` has one and the search
links `left` to its contractum. Unlike `linked`, it does not compare normal forms, and it contracts
a side only at the head, so that a fixpoint the two sides share is compared by congruence rather
than unfolded. -/
def headLinked : Nat → Term → Term → Bool
  | 0, left, right => left == right
  | fuel + 1, left, right =>
      left == right
      || (congruenceFirst left right
          && match left, right with
            | .application leftFunction leftArgument, .application rightFunction rightArgument =>
                headLinked fuel leftFunction rightFunction && headLinked fuel leftArgument rightArgument
            | .abstraction leftBody, .abstraction rightBody => headLinked fuel leftBody rightBody
            | .choice leftFirst leftSecond, .choice rightFirst rightSecond =>
                headLinked fuel leftFirst rightFirst && headLinked fuel leftSecond rightSecond
            | .parallel leftFirst leftSecond, .parallel rightFirst rightSecond =>
                headLinked fuel leftFirst rightFirst && headLinked fuel leftSecond rightSecond
            | _, _ => false)
      || (headIsRedex left
          && match step left with
            | some contracted => headLinked fuel contracted right
            | none => false)
      || (!headIsRedex left && headIsRedex right
          && match step right with
            | some contracted => headLinked fuel left contracted
            | none => false)

/-- What `headLinked` finds is a derivation: reflexivity, the congruences of `DerivableLatticeEta`, and
the β rule or the η rule of a contraction on either side (`Semantics.stepSound`), joined by
transitivity and symmetry. -/
theorem headLinkedSound {hypotheses : Term → Term → Prop} :
    ∀ {fuel : Nat} {left right : Term}, headLinked fuel left right = true →
      DerivableLatticeEta hypotheses left right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right equal
      simp only [headLinked, beq_iff_eq] at equal
      subst equal
      exact .reflexive _
  | succ remaining remainingSound =>
      intro left right found
      simp only [headLinked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at found
      rcases found with ((same | ⟨_, congruent⟩) | ⟨_, steppedLeft⟩) | ⟨_, steppedRight⟩
      · subst same
        exact .reflexive _
      · split at congruent
        · simp only [Bool.and_eq_true] at congruent
          exact .transitive (.congruenceFunction _ (remainingSound congruent.1))
            (.congruenceArgument _ (remainingSound congruent.2))
        · exact .congruenceAbstraction (remainingSound congruent)
        · simp only [Bool.and_eq_true] at congruent
          exact .transitive (.congruenceChoiceLeft _ (remainingSound congruent.1))
            (.congruenceChoiceRight _ (remainingSound congruent.2))
        · simp only [Bool.and_eq_true] at congruent
          exact .transitive (.congruenceParallelLeft _ (remainingSound congruent.1))
            (.congruenceParallelRight _ (remainingSound congruent.2))
        · cases congruent
      · split at steppedLeft
        · rename_i contracted contractedEqual
          exact .transitive (stepSound contractedEqual) (remainingSound steppedLeft)
        · cases steppedLeft
      · split at steppedRight
        · rename_i contracted contractedEqual
          exact .transitive (remainingSound steppedRight) (.symmetric (stepSound contractedEqual))
        · cases steppedRight

/-- A statement is derivable under every valuation when `headLinked` joins each of its sides, with
its variables abstracted,
to a term, and ⊢_{λ-lattice-η} derives the equation of the two terms from no hypothesis. -/
theorem statementDerivableOfHeadLinked {statement : EndToEnd.Statement} {fuel : Nat}
    {leftTerm rightTerm : Term}
    (leftLinked : headLinked fuel
      (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right) statement.left)
      leftTerm = true)
    (rightLinked : headLinked fuel
      (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right) statement.right)
      rightTerm = true)
    (derived : DerivableLatticeEta (fun _ _ => False) leftTerm rightTerm) :
    EquationDerivable statement.signature statement.left statement.right :=
  equationDerivableOfAbstractedDerivable
    (.transitive (headLinkedSound leftLinked)
      (.transitive derived (.symmetric (headLinkedSound rightLinked))))

/-! ## The proofs -/

open LambdaJit.ParallelTypesTheorems (compose filterNatural successor zero naturalFoldFixpoint
  naturalType successorFiltered successorFilteredChained naturalDoubleAsFold filterNaturalApply
  naturalTypeUnfold)

/-- The lemma `successor_filtered` of the knowledge module `parallel_types` is derivable: the
statement's two sides, abstracted, are linked to the two sides of
`ParallelTypesTheorems.successorFiltered`. -/
theorem «successor_filtered» :
    EquationDerivable Statement.«successor_filtered».signature Statement.«successor_filtered».left
      Statement.«successor_filtered».right :=
  statementDerivableOfLinked (fuel := 16) (by decide +kernel) (by decide +kernel) successorFiltered

/-- The lemma `successor_filtered_chained` of the knowledge module `parallel_types` is derivable: the
metavariable `Rest` occurs on both sides, so each side is abstracted twice and `Rest` is the
variable of the outer abstraction; under the two abstractions, the sides are linked to the two
sides of `ParallelTypesTheorems.successorFilteredChained` at that variable. -/
theorem «successor_filtered_chained» :
    EquationDerivable Statement.«successor_filtered_chained».signature Statement.«successor_filtered_chained».left
      Statement.«successor_filtered_chained».right :=
  statementDerivableOfLinked (fuel := 20) (by decide +kernel) (by decide +kernel)
    (.congruenceAbstraction (.congruenceAbstraction (successorFilteredChained (.boundVariable 1))))

/-- The lemma `natural_double_as_fold` of the knowledge module `parallel_types` is derivable: the
statement's two sides, abstracted, are linked to the two sides of
`ParallelTypesTheorems.naturalDoubleAsFold`. -/
theorem «natural_double_as_fold» :
    EquationDerivable Statement.«natural_double_as_fold».signature Statement.«natural_double_as_fold».left
      Statement.«natural_double_as_fold».right :=
  statementDerivableOfLinked (fuel := 16) (by decide +kernel) (by decide +kernel) naturalDoubleAsFold

/-- filter_nat zero = zero: filter_nat zero = zero ∥ nat_type
(`ParallelTypesTheorems.filterNaturalApply`) = zero ∥ (zero + successor nat_type)
(`ParallelTypesTheorems.naturalTypeUnfold`) = zero, by (5). -/
theorem zeroFilteredDerivable :
    DerivableLatticeEta (fun _ _ => False) (.application filterNatural zero) zero :=
  .transitive (filterNaturalApply zero)
    (.transitive (.congruenceParallelRight zero naturalTypeUnfold) (.parallelAbsorption zero _))

/-- The lemma `zero_filtered` of the knowledge module `contracts` is derivable: the statement's two
sides are linked to the two sides of `zeroFilteredDerivable`. -/
theorem «zero_filtered» :
    EquationDerivable Statement.«zero_filtered».signature Statement.«zero_filtered».left Statement.«zero_filtered».right :=
  statementDerivableOfLinked (fuel := 16) (by decide +kernel) (by decide +kernel) zeroFilteredDerivable

/-- The define `true`, λx.λy. x. -/
def trueTerm : Term := .abstraction (.abstraction (.boundVariable 1))

/-- The define `false`, λx.λy. y. -/
def falseTerm : Term := .abstraction (.abstraction (.boundVariable 0))

/-- The lemma `true_filtered` of the knowledge module `contracts` is derivable: its left side,
filter_boolean true, is linked to true ∥ (true + false), which is true by (5), its right side. -/
theorem «true_filtered» :
    EquationDerivable Statement.«true_filtered».signature Statement.«true_filtered».left Statement.«true_filtered».right :=
  statementDerivableOfLinked (fuel := 16) (leftTerm := .parallel trueTerm (.choice trueTerm falseTerm))
    (by decide +kernel) (by decide +kernel) (.parallelAbsorption trueTerm falseTerm)

/-- The lemma `false_filtered` of the knowledge module `contracts` is derivable: its left side,
filter_boolean false, is linked to false ∥ (true + false), which is false ∥ (false + true) by (1)
and false by (5), its right side. -/
theorem «false_filtered» :
    EquationDerivable Statement.«false_filtered».signature Statement.«false_filtered».left Statement.«false_filtered».right :=
  statementDerivableOfLinked (fuel := 16) (leftTerm := .parallel falseTerm (.choice trueTerm falseTerm))
    (by decide +kernel) (by decide +kernel)
    (.transitive (.congruenceParallelRight falseTerm (.choiceCommutative trueTerm falseTerm))
      (.parallelAbsorption falseTerm trueTerm))

/-- The lemma `filter_nat_idempotent` of the knowledge module `contracts` is derivable: its left side,
compose filter_nat filter_nat, is linked to λx. (x ∥ nat_type) ∥ nat_type, which is
λx. x ∥ (nat_type ∥ nat_type) by (4) and λx. x ∥ nat_type by the idempotence of the parallel
(`DerivableLatticeEta.parallelIdempotent`), to which its right side, filter_nat, is linked. -/
theorem «filter_nat_idempotent» :
    EquationDerivable Statement.«filter_nat_idempotent».signature Statement.«filter_nat_idempotent».left
      Statement.«filter_nat_idempotent».right :=
  statementDerivableOfLinked (fuel := 20)
    (leftTerm := .abstraction (.parallel (.parallel (.boundVariable 0) naturalType) naturalType))
    (by decide +kernel) (by decide +kernel)
    (.congruenceAbstraction
      (.transitive (.parallelAssociative (.boundVariable 0) naturalType naturalType)
        (.congruenceParallelRight (.boundVariable 0) (DerivableLatticeEta.parallelIdempotent naturalType))))

/-- The lemma `unary_as_fold` of the knowledge module `contracts` is derivable: both sides, unary and
nat_fold zero successor, are linked to one term,
`ParallelTypesTheorems.naturalFoldFixpoint zero successor`. -/
theorem «unary_as_fold» :
    EquationDerivable Statement.«unary_as_fold».signature Statement.«unary_as_fold».left Statement.«unary_as_fold».right :=
  statementDerivableOfLinked (fuel := 20) (leftTerm := naturalFoldFixpoint zero successor)
    (by decide +kernel) (by decide +kernel) (.reflexive _)

open LambdaJit.ParallelTypesTheorems (naturalFold naturalFoldFiltered naturalFoldFilteredContract
  naturalFoldFilteredContractChained naturalFoldFilteredBranch naturalFoldFilteredBranchInContext)

/-- The lemma `nat_fold_filtered_contract` of the knowledge module `filtered_recursion_naturals` is
sound: its metavariables `Base` and `Step` occur on both sides, so each side is abstracted four
times, `Base` the variable of the outermost abstraction and `Step` that of the next; under the four
abstractions, `headLinked` joins the sides to the two sides of
`ParallelTypesTheorems.naturalFoldFilteredContract` at those variables. -/
theorem «nat_fold_filtered_contract» :
    EquationDerivable Statement.«nat_fold_filtered_contract».signature Statement.«nat_fold_filtered_contract».left
      Statement.«nat_fold_filtered_contract».right :=
  statementDerivableOfHeadLinked (fuel := 100) (by decide +kernel) (by decide +kernel)
    (derivableUnderAbstractions
      (naturalFoldFilteredContract (.boundVariable 3) (.boundVariable 2)) 4)

/-- The lemma `nat_fold_filtered_contract_chained` of the knowledge module
`filtered_recursion_naturals` is derivable: as `nat_fold_filtered_contract`, with the metavariables
`Base`, `Step` and `Rest`, six abstractions, and
`ParallelTypesTheorems.naturalFoldFilteredContractChained`. -/
theorem «nat_fold_filtered_contract_chained» :
    EquationDerivable Statement.«nat_fold_filtered_contract_chained».signature Statement.«nat_fold_filtered_contract_chained».left
      Statement.«nat_fold_filtered_contract_chained».right :=
  statementDerivableOfHeadLinked (fuel := 100) (by decide +kernel) (by decide +kernel)
    (derivableUnderAbstractions
      (naturalFoldFilteredContractChained (.boundVariable 5) (.boundVariable 4) (.boundVariable 3)) 6)

/-- The lemma `nat_fold_filtered_branch` of the knowledge module `filtered_recursion_naturals` is
sound: its metavariables `Base` and `Step` occur once on the left side and twice on the right, so
each side is abstracted six times, `Base` the variable of the outermost abstraction and `Step` that
of the next; under the six abstractions, `headLinked` joins the sides to the two sides of
`ParallelTypesTheorems.naturalFoldFilteredBranch` at those variables. -/
theorem «nat_fold_filtered_branch» :
    EquationDerivable Statement.«nat_fold_filtered_branch».signature Statement.«nat_fold_filtered_branch».left
      Statement.«nat_fold_filtered_branch».right :=
  statementDerivableOfHeadLinked (fuel := 100) (by decide +kernel) (by decide +kernel)
    (derivableUnderAbstractions
      (naturalFoldFilteredBranch (.boundVariable 5) (.boundVariable 4)) 6)

/-- The lemma `nat_fold_filtered_branch_in_context` of the knowledge module
`filtered_recursion_naturals` is derivable: its metavariables `Context`, `Base` and `Step` occur once on
the left side and twice on the right, so each side is abstracted nine times; under the nine
abstractions, `headLinked` joins the sides to the two sides of
`ParallelTypesTheorems.naturalFoldFilteredBranchInContext` at the variables of the three outermost
abstractions. -/
theorem «nat_fold_filtered_branch_in_context» :
    EquationDerivable Statement.«nat_fold_filtered_branch_in_context».signature Statement.«nat_fold_filtered_branch_in_context».left
      Statement.«nat_fold_filtered_branch_in_context».right :=
  statementDerivableOfHeadLinked (fuel := 100) (by decide +kernel) (by decide +kernel)
    (derivableUnderAbstractions
      (naturalFoldFilteredBranchInContext (.boundVariable 8) (.boundVariable 7) (.boundVariable 6)) 9)

end LambdaJit.LibraryLemmaProofs
