import LambdaJit.LibraryLemmaProofs
import LambdaJit.RefinementSearch
import LambdaJit.StaticArgumentFixpoint
import LambdaJit.LatticeEtaConsistency
import LambdaJit.ContextualPreorderAdequacy

/-!
# Hand-written proofs of library lemmas of the entry `wren`

Proofs that the command `lemma_soundness` (module `LemmaSoundness`) looks up for lemmas of the
knowledge modules of the entry `wren` (`gezi/corpora/compiler/wren_typed_block`), by the
naming rule of module `LibraryLemmaProofs`: the proof of the lemma `Name` is the theorem
`LambdaJit.LibraryLemmaProofs.«Name»`, about its own copy of the lemma's statement,
`LambdaJit.LibraryLemmaProofs.Statement.«Name»`, copied from the export.

Two kinds of proof:

- `EndToEnd.EquationDerivable`: the equation is derived in ⊢_{λ-lattice-η} (`DerivableLatticeEta`,
  no unit law); it is a contextual equivalence, Definition 14, by
  `ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta` (module `LatticeEtaConsistency`).
- `EndToEnd.EquationSound`: the equation is ≃_O, Definition 14, and ⊢ does not derive it. The proof
  links each side by ⊢_{λ-lattice-η} to a term, shows in Wadsworth's D∞ that the two terms read
  alike in every environment, and crosses to ≃_O by
  `DdLP96Model.contextualEquivalenceOfInterpretEqual`; the model is that bridge and does not
  define the semantics (`equationSoundOfLinkedReadings`).
-/

namespace LambdaJit.LibraryLemmaProofs

open LambdaJit.Semantics
open LambdaJit.StatementNormalisation (abstracted equationDerivableOfAbstractedDerivable
  equationSoundOfAbstractedEquivalent)
open LambdaJit.Interpretation (termVariables)
open LambdaJit.EndToEnd (EquationDerivable EquationSound)
open LambdaJit.Readback (abstractions)
open LambdaJit.RefinementSearch (absorbs absorbsSound absorbedInto absorbedIntoSound developed
  developedSound underAbstractions)

namespace Statement

/-- The statement of the lemma `wren_typed_bindings` of the knowledge module `wren_typed_block`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «wren_typed_bindings» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.slot 0), [.slot 0, .ignored, .ignored]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.apply (.apply (.slot 0) (.slot 1)) (.slot 1)), [.slot 1]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "6"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 5), (.slot 3), (.slot 4)])) [.slot 4] [(.slot 1), (.slot 0), (.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.apply (.apply (.slot 2) (.slot 3)) (.slot 4)))) [.slot 4] [(.slot 5), (.slot 6), (.slot 3), (.slot 4)])) [.slot 4] [(.slot 1), (.slot 0), (.slot 4), (.slot 3), (.slot 2), (.slot 5)])), [.slot 3, .slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "7"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 2))) [.slot 2] [(.slot 3), (.slot 4)])), [.slot 4, .slot 0]),
      (⟨["LambdaJit", "thunk"], "8"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1]),
      (⟨["LambdaJit", "thunk"], "9"⟩, (.apply (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 2)) (.slot 1)), [.slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "10"⟩, (.apply (.apply (.apply (.slot 0) (.apply (.apply (.apply (.slot 1) (.slot 2)) (.slot 3)) (.slot 3))) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3)) [.slot 3] [(.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3)) [.slot 3] [(.slot 2), (.slot 5), (.slot 4)])) [.slot 4] [(.slot 1), (.slot 4), (.slot 5), (.slot 2), (.slot 6)])) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3)) [.slot 3] [(.slot 2), (.slot 1), (.slot 3)])) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3)) [.slot 3] [(.slot 2), (.slot 4), (.slot 3)])) [.slot 3] [(.slot 1), (.slot 4), (.slot 5), (.slot 2)])), [.slot 5, .slot 2, .slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "11"⟩, (.slot 0), [.ignored]),
      (⟨["LambdaJit", "thunk"], "12"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "13"⟩, (.apply (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 1)) (.slot 2)), [.slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "14"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 5), (.slot 3), (.slot 4)])) [.slot 4] [(.slot 1), (.slot 0), (.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 2), (.slot 3), (.slot 4)])) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3))) [.slot 3] [(.slot 2), (.slot 3), (.slot 4)])) [.slot 4] [(.slot 1), (.slot 0), (.slot 4), (.slot 3)])), [.slot 3, .slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "15"⟩, (.slot 0), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "16"⟩, (.choice (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.choice (.apply (.slot 3) (.apply (.slot 4) (.slot 5))) (.apply (.slot 6) (.apply (.slot 4) (.slot 7))))), [.slot 4, .slot 0]),
      (⟨["LambdaJit", "thunk"], "17"⟩, (.apply (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 1))) [.slot 1] [(.slot 0)]) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 1))) [.slot 1] [(.slot 0)])), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "18"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "19"⟩, (.parallel (.apply (.slot 0) (.parallel (.slot 1) (.slot 2))) (.slot 3)), [.slot 2, .slot 3, .slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "20"⟩, (.apply (.slot 0) (.apply (.slot 1) (.parallel (.slot 2) (.slot 3)))), [.slot 2]),
      (⟨["LambdaJit", "thunk"], "21"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 0)) (.slot 1)) (.slot 2)) [.slot 2] [(.slot 1), (.slot 0)])), [.slot 1, .slot 0])],
    left := (.application
      (.application
        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                        (.application
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                            (.application
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "8"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))))
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "9"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "13"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                      (.application
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
            (.application
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
      (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))),
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
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                            (.application
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                (.application
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "8"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "9"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                              (.application
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "13"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
              (.application
                (.application
                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
      (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "8"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.constant ⟨["LambdaJit", "thunk"], "15"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "parallel"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                              (.application
                                                (.application
                                                  (.application
                                                    (.application
                                                      (.application
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                        (.application
                                                          (.application
                                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                            (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                          (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "19"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.application
                                                        (.application
                                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                                  (.application
                                                    (.application
                                                      (.application
                                                        (.application
                                                          (.application
                                                            (.application
                                                              (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                            (.application
                                                              (.application
                                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                                (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                              (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                          (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                        (.application
                                                          (.application
                                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                            (.application
                                                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                          (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                              (.application
                                                (.application
                                                  (.application
                                                    (.application
                                                      (.application
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                        (.application
                                                          (.application
                                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                            (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                          (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "19"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                              (.application
                                                (.application
                                                  (.application
                                                    (.application
                                                      (.application
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                        (.application
                                                          (.application
                                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                            (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                          (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                        (.application
                                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.application
                                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                          (.application
                                            (.application
                                              (.application
                                                (.application
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                        (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                      (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.application
                                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.application
                                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "20"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "19"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                            (.application
                                              (.application
                                                (.application
                                                  (.application
                                                    (.application
                                                      (.application
                                                        (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                      (.application
                                                        (.application
                                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                          (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                        (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                      (.application
                                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.application
                                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                        (.application
                                          (.application
                                            (.application
                                              (.application
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                (.application
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                    (.application
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "8"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                  (.application
                                    (.application
                                      (.application
                                        (.application
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                          (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.application
                                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                          (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                      (.application
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "20"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "19"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                        (.application
                                          (.application
                                            (.application
                                              (.application
                                                (.application
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                  (.application
                                                    (.application
                                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                      (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                    (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.application
                                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                    (.application
                                      (.application
                                        (.application
                                          (.application
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "9"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                  (.application
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                              (.application
                                (.application
                                  (.application
                                    (.application
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.application
                                          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
                  (.application
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "20"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "19"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                    (.application
                                      (.application
                                        (.application
                                          (.application
                                            (.application
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                              (.application
                                                (.application
                                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                                  (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                                (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.application
                                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                (.application
                                  (.application
                                    (.application
                                      (.application
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                            (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "13"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                              (.application
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                          (.application
                            (.application
                              (.application
                                (.application
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.application
                                      (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                  (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
              (.application
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "20"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.constant ⟨["LambdaJit", "thunk"], "19"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                                (.application
                                  (.application
                                    (.application
                                      (.application
                                        (.application
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                          (.application
                                            (.application
                                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                              (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                            (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.application
                                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                            (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                        (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                            (.application
                              (.application
                                (.application
                                  (.application
                                    (.application
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                      (.application
                                        (.application
                                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                          (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                        (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.application
                                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                    (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                          (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                      (.application
                        (.application
                          (.application
                            (.application
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "16"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "17"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.constant ⟨["LambdaJit", "thunk"], "18"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.application
                                  (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                  (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                              (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                        (.application
                          (.application
                            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                            (.application
                              (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                              (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                          (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                        (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))))
          (.application
            (.application
              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
              (.constant ⟨["LambdaJit", "thunk"], "21"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
            (.constant ⟨["LambdaJit", "thunk"], "21"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))) }


end Statement

/-- The lemma `wren_typed_bindings` of the knowledge module `wren_typed_block` is derivable in
⊢_{λ-lattice-η}: the paper proof is section 17 of the proofs file.
Its metavariables occur three times, so each side is abstracted three times
(`StatementNormalisation.abstracted`). Under the abstractions, the right side contracts in two
steps at its head, through the constant of the choice, to M + N, M the body of the left side and
N the typed bindings; `RefinementSearch.headRefined` finds that N refines M, at fuel 40, and the
kernel evaluates the search (`decide +kernel`). -/
theorem «wren_typed_bindings» :
    EquationDerivable Statement.«wren_typed_bindings».signature Statement.«wren_typed_bindings».left Statement.«wren_typed_bindings».right :=
  equationDerivableOfAbstractedDerivable
    (absorbsSound (count := 3) (steps := 2) (fuel := 40) (by decide +kernel))

/-! ## Lemmas sound by Definition 14 and not derivable by ⊢ -/

namespace Statement

/-- The statement of the lemma `wren_static_argument_fixpoint` of the knowledge module
`wren_typed_specialization`: the two sides of the equation that an article imports for it,
copied from the export. -/
def «wren_static_argument_fixpoint» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 0)) (.slot 1)) (.slot 2)) [.slot 2] [(.slot 1), (.slot 0)])), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.apply (.apply (.slot 0) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) [.slot 1] [(.slot 1), (.slot 2)])) (.slot 3)) (.slot 2)), [.slot 1, .slot 3, .slot 2]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3)), [.slot 1, .slot 2]),
      (⟨["LambdaJit", "thunk"], "3"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1]),
      (⟨["LambdaJit", "thunk"], "4"⟩, (.slot 0), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "5"⟩, (.parallel (.apply (.apply (.apply (.apply (.slot 0) (.thunk (.parallel (.apply (.apply (.slot 0) (.parallel (.slot 1) (.slot 2))) (.parallel (.slot 3) (.slot 2))) (.slot 2)) [.slot 1, .slot 3] [(.slot 1), (.slot 2)])) (.parallel (.slot 3) (.slot 2))) (.slot 4)) (.parallel (.slot 5) (.slot 2))) (.slot 2)), [.slot 1, .slot 3, .slot 5]),
      (⟨["LambdaJit", "thunk"], "6"⟩, (.apply (.apply (.slot 0) (.slot 1)) (.slot 1)), [.slot 1]),
      (⟨["LambdaJit", "thunk"], "7"⟩, (.slot 0), [.ignored, .slot 0]),
      (⟨["LambdaJit", "thunk"], "8"⟩, (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 1)) (.slot 0))), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "9"⟩, (.choice (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.choice (.apply (.slot 3) (.apply (.slot 4) (.slot 5))) (.apply (.slot 6) (.apply (.slot 4) (.slot 7))))), [.slot 4, .slot 0]),
      (⟨["LambdaJit", "thunk"], "10"⟩, (.slot 0), [.slot 0, .ignored, .ignored]),
      (⟨["LambdaJit", "thunk"], "11"⟩, (.apply (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 1))) [.slot 1] [(.slot 0)]) (.thunk (.apply (.slot 0) (.apply (.slot 1) (.slot 1))) [.slot 1] [(.slot 0)])), [.slot 0]),
      (⟨["LambdaJit", "thunk"], "12"⟩, (.parallel (.slot 0) (.slot 1)), [.slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "13"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "14"⟩, (.slot 0), [.slot 0, .ignored]),
      (⟨["LambdaJit", "thunk"], "15"⟩, (.apply (.slot 0) (.slot 1)), [.slot 1, .ignored, .ignored, .slot 0])],
    left := (.application
      (.application
        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
      (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
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
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.application
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                  (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
      (.application
        (.application
          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
          (.application
            (.constant ⟨["LambdaJit", "thunk"], "3"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
            (.constant ⟨["LambdaJit", "thunk"], "4"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.application
                  (.application
                    (.constant ⟨["LambdaJit", "thunk"], "5"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])]))
                    (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.application
                    (.application
                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                      (.application
                        (.application
                          (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.application
                              (.application
                                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                (.constant ⟨["LambdaJit", "thunk"], "8"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.constant ⟨["LambdaJit", "thunk"], "8"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                        (.application
                          (.application
                            (.application
                              (.application
                                (.application
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "9"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])])])])])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "10"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                  (.application
                                    (.application
                                      (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                      (.constant ⟨["LambdaJit", "thunk"], "11"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                                    (.constant ⟨["LambdaJit", "thunk"], "12"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "13"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                              (.application
                                (.application
                                  (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                                  (.application
                                    (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                    (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                                (.constant ⟨["LambdaJit", "thunk"], "7"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.constant ⟨["LambdaJit", "thunk"], "15"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                          (.application
                            (.application
                              (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                              (.application
                                (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                                (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                            (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.application
                          (.constant ⟨["LambdaJit", "thunk"], "6"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                          (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                      (.constant ⟨["LambdaJit", "thunk"], "14"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
                (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))) }

end Statement

/-- Whether the developed `term` (`RefinementSearch.developed`) is `target`, or is a choice under
`count` abstractions that absorbs into `target` (`RefinementSearch.absorbedInto`). -/
def linkedTo (count fuel : Nat) (term target : Term) : Bool :=
  developed term == target || absorbedInto count fuel (developed term) target

theorem linkedToSound {count fuel : Nat} {term target : Term} (found : linkedTo count fuel term target = true) :
    DerivableLatticeEta (fun _ _ => False) term target := by
  unfold linkedTo at found
  simp only [Bool.or_eq_true, beq_iff_eq] at found
  rcases found with equal | absorbed
  · rw [← equal]
    exact developedSound term
  · exact .transitive (developedSound term) (absorbedIntoSound absorbed)

theorem underAbstractionsAbstractions : ∀ (count : Nat) (body : Term),
    underAbstractions count (abstractions count body) = some body
  | 0, _ => rfl
  | count + 1, body => underAbstractionsAbstractions count body

/-- An equation is sound, Definition 14, when its two sides, abstracted, are linked by
⊢_{λ-lattice-η} (`linkedTo`) to two terms under `count` abstractions whose bodies read alike in
every environment of D∞: the readings of the abstracted sides are then equal
(`LatticeEtaConsistency.interpretDerivableLatticeEta`), which gives ≃_O
(`DdLP96Model.contextualEquivalenceOfInterpretEqual` at `DInfinity.wadsworthModel`). -/
theorem equationSoundOfLinkedReadings {statement : EndToEnd.Statement} {count leftFuel rightFuel : Nat}
    {leftBody rightBody : Term}
    (leftLinked : linkedTo count leftFuel
      (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right) statement.left)
      (abstractions count leftBody) = true)
    (rightLinked : linkedTo count rightFuel
      (abstracted statement.signature (termVariables statement.left ++ termVariables statement.right) statement.right)
      (abstractions count rightBody) = true)
    (same : ∀ environment, DInfinity.Limit.interpret leftBody environment =
      DInfinity.Limit.interpret rightBody environment) :
    EquationSound statement.signature statement.left statement.right := by
  apply equationSoundOfAbstractedEquivalent
  apply DInfinity.wadsworthModel.contextualEquivalenceOfInterpretEqual
  intro environment
  have impossible : ∀ left right, (fun _ _ => False : Term → Term → Prop) left right →
      ∀ environment, DInfinity.wadsworthModel.interpret left environment =
        DInfinity.wadsworthModel.interpret right environment :=
    fun _ _ contradiction => contradiction.elim
  rw [DInfinity.wadsworthModel.interpretDerivableLatticeEta impossible (linkedToSound leftLinked),
    DInfinity.wadsworthModel.interpretDerivableLatticeEta impossible (linkedToSound rightLinked)]
  exact DInfinity.Limit.interpretUnderAbstractions (underAbstractionsAbstractions count leftBody)
    (underAbstractionsAbstractions count rightBody) same environment

/-- The lemma `wren_static_argument_fixpoint` of the knowledge module `wren_typed_specialization`
is sound by Definition 14; ⊢ does not derive it. The paper proof is section 18 of
the proofs file. Its metavariables occur nine times, so each side
is abstracted nine times. One development of the left side is Θ′ F X H and of the right side is
Θ′ G X + N, N the typed branch, Θ′ the by-value fixed point combinator; `headRefined` finds that N
refines Θ′ G X (section 18.4), at fuel 20. Θ′ F X H and Θ′ G X read alike in every environment of
D∞ (`DInfinity.Limit.interpretStaticArgument`, section 18.1), and the readings carry the equation to
≃_O. -/
theorem «wren_static_argument_fixpoint» :
    EquationSound Statement.«wren_static_argument_fixpoint».signature Statement.«wren_static_argument_fixpoint».left Statement.«wren_static_argument_fixpoint».right :=
  equationSoundOfLinkedReadings (count := 9) (leftFuel := 0) (rightFuel := 20)
    (leftBody := DInfinity.Limit.staticArgumentLeft) (rightBody := DInfinity.Limit.staticArgumentRight)
    (by decide +kernel) (by decide +kernel) DInfinity.Limit.interpretStaticArgument


namespace Statement

/-- The statement of the lemma `wren_own_loop_lifted` of the knowledge module `wren_own_loop_lifting`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «wren_own_loop_lifted» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 0)) (.slot 1)) (.slot 2)) [.slot 2] [(.slot 1), (.slot 0)])), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.apply (.apply (.slot 0) (.slot 1)) (.slot 2))) [.slot 1] [(.slot 2), (.slot 1)])) (.thunk (.apply (.slot 0) (.apply (.apply (.slot 1) (.slot 2)) (.apply (.apply (.slot 1) (.slot 2)) (.slot 3)))) [.slot 2] [(.slot 3), (.slot 2), (.slot 1)])), [.slot 2, .slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3))) [.slot 1] [(.slot 2), (.slot 3), (.slot 1)])) (.thunk (.apply (.slot 0) (.apply (.apply (.apply (.slot 1) (.slot 2)) (.slot 0)) (.apply (.apply (.apply (.slot 1) (.slot 2)) (.slot 0)) (.slot 3)))) [.slot 2] [(.slot 3), (.slot 2), (.slot 1)])), [.slot 2, .slot 0, .slot 3, .slot 1])],
    left := (.application
      (.application
        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
      (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
    right := (.application
      (.application
        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
      (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))) }

/-- The statement of the lemma `wren_own_loop_lifted_respelled` of the knowledge module `wren_own_loop_lifting`:
the two sides of the equation that an article imports for it, copied from the export. -/
def «wren_own_loop_lifted_respelled» : EndToEnd.Statement :=
  { signature := [(⟨["LambdaJit", "thunk"], "0"⟩, (.apply (.slot 0) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 0)) (.slot 1)) (.slot 2)) [.slot 2] [(.slot 1), (.slot 0)])), [.slot 1, .slot 0]),
      (⟨["LambdaJit", "thunk"], "1"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.apply (.apply (.slot 0) (.slot 1)) (.slot 2))) [.slot 1] [(.slot 2), (.slot 1)])) (.thunk (.apply (.apply (.slot 0) (.slot 1)) (.apply (.apply (.slot 0) (.slot 1)) (.apply (.slot 2) (.slot 3)))) [.slot 1] [(.slot 2), (.slot 3), (.slot 1)])), [.slot 2, .slot 0, .slot 1]),
      (⟨["LambdaJit", "thunk"], "2"⟩, (.apply (.apply (.apply (.slot 0) (.slot 1)) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.slot 3))) [.slot 1] [(.slot 2), (.slot 3), (.slot 1)])) (.thunk (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.apply (.apply (.apply (.slot 0) (.slot 1)) (.slot 2)) (.apply (.slot 2) (.slot 3)))) [.slot 1] [(.slot 2), (.slot 3), (.slot 1)])), [.slot 2, .slot 0, .slot 3, .slot 1])],
    left := (.application
      (.application
        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                  (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.application
                (.constant ⟨["LambdaJit", "thunk"], "1"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])]))
                (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))))
          (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
      (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))),
    right := (.application
      (.application
        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
        (.application
          (.application
            (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
            (.application
              (.application
                (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                (.application
                  (.application
                    (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                    (.application
                      (.application
                        (.constant ⟨["LambdaJit"], "apply"⟩ (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨[], "->"⟩ [(.operator ⟨["LambdaJit"], "term"⟩ []), (.operator ⟨["LambdaJit"], "term"⟩ [])])]))
                        (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ [])))
                      (.constant ⟨["LambdaJit", "thunk"], "0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
                  (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
              (.termVariable ⟨[], "metavariable1"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
          (.termVariable ⟨[], "metavariable0"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))))
      (.termVariable ⟨[], "metavariable2"⟩ (.operator ⟨["LambdaJit"], "term"⟩ []))) }

end Statement

/-- The lemma `wren_own_loop_lifted` of the knowledge module `wren_own_loop_lifting` is sound by
Definition 14; ⊢ does not derive it. The paper proof is section 18 of
the proofs file, with the loop's body K in place of section 18's.
Its metavariables occur six times, so each side is abstracted six times; one development of the
left side is Θ′ G X S and of the right side Θ′ F X H S, G the loop with its held argument H dropped
and F the loop with H lifted to an argument. The two read alike in every environment of D∞
(`DInfinity.Limit.interpretOwnLoopLifted`), and the readings carry the equation to ≃_O. -/
theorem «wren_own_loop_lifted» :
    EquationSound Statement.«wren_own_loop_lifted».signature Statement.«wren_own_loop_lifted».left Statement.«wren_own_loop_lifted».right :=
  equationSoundOfLinkedReadings (count := 6) (leftFuel := 0) (rightFuel := 0)
    (leftBody := DInfinity.Limit.ownLoopLeft DInfinity.Limit.liftedDroppedExit)
    (rightBody := DInfinity.Limit.ownLoopRight DInfinity.Limit.liftedLiftedExit)
    (by decide +kernel) (by decide +kernel) DInfinity.Limit.interpretOwnLoopLifted

/-- The lemma `wren_own_loop_lifted_respelled` of the knowledge module `wren_own_loop_lifting` is
sound by Definition 14, as `wren_own_loop_lifted` is, with H applied to the state before the two
recursive calls of the exit instead of after them
(`DInfinity.Limit.interpretOwnLoopRespelled`). -/
theorem «wren_own_loop_lifted_respelled» :
    EquationSound Statement.«wren_own_loop_lifted_respelled».signature Statement.«wren_own_loop_lifted_respelled».left
      Statement.«wren_own_loop_lifted_respelled».right :=
  equationSoundOfLinkedReadings (count := 6) (leftFuel := 0) (rightFuel := 0)
    (leftBody := DInfinity.Limit.ownLoopLeft DInfinity.Limit.respelledDroppedExit)
    (rightBody := DInfinity.Limit.ownLoopRight DInfinity.Limit.respelledLiftedExit)
    (by decide +kernel) (by decide +kernel) DInfinity.Limit.interpretOwnLoopRespelled

end LambdaJit.LibraryLemmaProofs
