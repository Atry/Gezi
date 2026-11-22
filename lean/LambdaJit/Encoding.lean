import LambdaJit.EndToEnd

/-!
# The writer's encoding of an IR term as an article term

Link (ii) of D6 is that the article term that
the writer `gezi/prolog/gezi/opentheory_article.pl` writes for an IR term reads, by
`Interpretation.read`, as the readback of that IR term (`Readback.readback`). This module states
the writer's encoding in Lean (`encode`) and proves that its reading is the readback; that the
Prolog writer computes `encode` is tested, not proved (the last paragraph below).

- `nameOf` and `signatureWellFormed`: the name of a thunk constant is the article's (D7.1), the
  entry of the signature with its code and holes; on a signature with distinct names, none of
  them an operator's, that name stands for the thunk (`operatorOfNameOf`).
- `encode`: the writer's encoding of a finite term (module `Ir`), its `key_encoding/2` and
  `layer_encoding/2`: an application as `LambdaJit.apply` applied to the encodings of its two
  sides, a parallel likewise with `LambdaJit.parallel`, a choice likewise with
  `LambdaJit.choice`, and a thunk as its constant applied by HOL
  application to the encodings of its fillings in slot order, a thunk without fillings as its
  constant alone; each constant at the type the writer's `symbol_type/2` gives it. `encode` is
  undefined where the writer's code throws on a finite term: on a thunk with more holes that are
  slots than its code reads slots (`thunk_arity/3`, `more_holes_than_slots`), and on a thunk with
  fillings whose number is not its constant's arity (`fillings_differ`).
- `readEncode`: wherever `encode` gives an article term for a finite term, the reading of that
  article term is the readback of the finite term, as an equality of partial functions: one is
  defined exactly where the other is, with the same term. No step of a derivability relation is
  needed.
- `endToEndEncoded` and `endToEndEncodedOfChecked`: the end-to-end theorem on an article whose
  exported equation is the encoding of two finite terms: their readbacks are contextually
  equivalent, ≃_O of DdLP96's Definition 14.

The definitions are tied to the writer by the test
`the_writer_encodes_as_lean_encodes_on_the_fixpoint_runs` of
`gezi/tests/opentheory_article.plt`, which compares the writer's encoding (`term_encoded/2`)
of the two sides of each of the seven fixpoint runs with `encode` of the same IR terms, printed by
Lean, byte for byte, and checks with Lean that the exported equation of each run's expected
article is the encoding of its two sides; the kernel checks the latter too (modules
`FixpointRunSides` and `FixpointRunFixtures`). That is a check on those terms, not a proof that the
Prolog writer computes `encode` (FIXME at `key_term_written/2` of the writer).
-/

namespace LambdaJit.Encoding

open LambdaJit.Interpretation
open LambdaJit.EndToEnd (termType binaryType applyTerm choiceTerm parallelTerm
  EquationSound endToEndRead endToEndOfChecked contextualEquivalenceOfRead operatorOfApply
  operatorOfChoice operatorOfParallel)
open LambdaJit.ContextualPreorder (ContextualEquivalence)
open LambdaJit.Readback (readback readbackList readbackCode readbackCodeList finalSlots
  abstractions)

/-! ## The name of a thunk constant under a signature

A thunk constant's name is the article's (D7.1): the writer numbers the constants of an article in
the order they first occur, and the signature read from the article's definitions gives each name
its code and holes. The encoding names the thunk of a code and holes by the first entry of the
signature with that code and those holes (`nameOf`); on a signature whose names are distinct and
none of the three fixed operators' (`signatureWellFormed`), the name's operator is that thunk
(`operatorOfNameOf`). -/

/-- Whether a name is one of the three operators' fixed names. -/
def fixedName (name : Article.Name) : Bool :=
  name == applyName || name == choiceName || name == parallelName

/-- A signature whose names are distinct and none of them fixed. -/
def signatureWellFormed (signature : Signature) : Bool :=
  decide (signature.map Prod.fst).Nodup && signature.all fun entry => !fixedName entry.1

/-- The name of the first entry of the signature with the code `code` (`Code.equal`) and the
holes `holes`. -/
def nameOf (signature : Signature) (code : Code) (holes : List Hole) : Option Article.Name :=
  (signature.find? fun entry => entry.2.1.equal code && entry.2.2 == holes).map Prod.fst

/-- In a list whose keys are distinct, the first entry of a key is its entry. -/
theorem lookupFirstOfNodup {Key Value : Type} [DecidableEq Key] {key : Key} {value : Value} :
    ∀ {entries : List (Key × Value)}, (entries.map Prod.fst).Nodup → (key, value) ∈ entries →
      Article.lookupFirst key entries = some value
  | [], _, member => absurd member List.not_mem_nil
  | (entryKey, entryValue) :: rest, distinct, member => by
      simp only [List.map_cons, List.nodup_cons] at distinct
      simp only [Article.lookupFirst]
      rcases List.mem_cons.mp member with isFirst | inRest
      · simp only [Prod.mk.injEq] at isFirst
        rw [isFirst.1, isFirst.2]
        simp
      · have keyInRest : key ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(key, value), inRest, rfl⟩
        have differs : entryKey ≠ key := fun same => distinct.1 (same ▸ keyInRest)
        simp only [differs, if_false]
        exact lookupFirstOfNodup distinct.2 inRest

/-- On a well-formed signature, the name `nameOf` gives a code and holes stands for their thunk. -/
theorem operatorOfNameOf {signature : Signature} {code : Code} {holes : List Hole}
    {name : Article.Name} (wellFormed : signatureWellFormed signature = true)
    (found : nameOf signature code holes = some name) :
    operatorOf signature name = .thunk code holes := by
  simp only [signatureWellFormed, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at wellFormed
  obtain ⟨distinct, unfixed⟩ := wellFormed
  simp only [nameOf, Option.map_eq_some_iff] at found
  obtain ⟨⟨entryName, entryCode, entryHoles⟩, entryFound, sameName⟩ := found
  have entryMember := List.mem_of_find?_eq_some entryFound
  have matched := List.find?_some entryFound
  simp only [Bool.and_eq_true, beq_iff_eq] at matched
  simp only at sameName
  subst sameName
  have notFixed := unfixed _ entryMember
  simp only [fixedName, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at notFixed
  obtain ⟨⟨notApply, notChoice⟩, notParallel⟩ := notFixed
  simp only [operatorOf, notApply, notChoice, notParallel, if_false,
    lookupFirstOfNodup distinct entryMember, Code.equality_of_equal matched.1, matched.2]

/-! ## The encoding -/

/-- The type `term → … → term` of a thunk constant with `arity` fillings, the writer's
`term_function_type/2`. -/
def thunkType : Nat → Article.LogicType
  | 0 => termType
  | arity + 1 => .arrow termType (thunkType arity)

/-- The thunk constant named `name` of `code` with `holes` at its type, the writer's
`symbol_type/2`. -/
def thunkConstant (name : Article.Name) (code : Code) (holes : List Hole) : Article.Term :=
  .constant name (thunkType (thunkArity code holes))

mutual
/-- The writer's encoding of a finite term (`key_encoding/2` and `layer_encoding/2`), each thunk
constant named by the signature (`nameOf`), undefined where the writer throws: a thunk with more
holes that are slots than its code reads slots (`thunk_arity/3`, `more_holes_than_slots`), or with
fillings whose number is not its constant's arity (`fillings_differ`); and undefined where the
signature names no thunk of the code and the holes. A thunk without fillings is its constant
alone, at any arity, as the writer's alias `thunk(Code, Holes, [])` writes it. -/
def encode (signature : Signature) : FiniteTerm → Option Article.Term
  | .thunk code holes fillings =>
      if slotHoleCount holes ≤ slotCount code ∧
          (fillings.isEmpty = true ∨ fillings.length = thunkArity code holes) then
        match nameOf signature code holes with
        | some name => (encodeList signature fillings).map
            (applyArguments (thunkConstant name code holes))
        | none => none
      else none
  | .apply function argument => do
      let functionTerm ← encode signature function
      let argumentTerm ← encode signature argument
      pure (applyTerm functionTerm argumentTerm)
  | .choice left right => do
      let leftTerm ← encode signature left
      let rightTerm ← encode signature right
      pure (choiceTerm leftTerm rightTerm)
  | .parallel left right => do
      let leftTerm ← encode signature left
      let rightTerm ← encode signature right
      pure (parallelTerm leftTerm rightTerm)

/-- The encodings of a list of finite terms. -/
def encodeList (signature : Signature) : List FiniteTerm → Option (List Article.Term)
  | [] => some []
  | term :: terms => do
      let head ← encode signature term
      let tail ← encodeList signature terms
      pure (head :: tail)
end

/-- The signature of the examples: successor's code and holes, and the identity's. -/
def exampleSignature : Signature :=
  [(⟨["LambdaJit", "thunk"], "0"⟩, .apply (.slot 0) (.slot 1), [.slot 1, .ignored, .slot 0]),
    (⟨["LambdaJit", "thunk"], "1"⟩, .slot 0, [.slot 0, .ignored]),
    (⟨["LambdaJit", "thunk"], "2"⟩, .apply (.slot 0) (.slot 1), [.slot 1]),
    (⟨["LambdaJit", "thunk"], "3"⟩, .slot 0, [.slot 0])]

/-- Successor applied to zero: `LambdaJit.apply` applied to two thunk constants without fillings. -/
example : encode exampleSignature
      (.apply (.thunk (.apply (.slot 0) (.slot 1)) [.slot 1, .ignored, .slot 0] [])
        (.thunk (.slot 0) [.slot 0, .ignored] [])) =
    some (applyTerm (.constant ⟨["LambdaJit", "thunk"], "0"⟩ termType)
      (.constant ⟨["LambdaJit", "thunk"], "1"⟩ termType)) := by
  rfl

/-- A thunk with one filling, and a right-nested chain of three choices' members. -/
example :
    encode exampleSignature
      (.choice (.thunk (.apply (.slot 0) (.slot 1)) [.slot 1] [.thunk (.slot 0) [.slot 0] []])
        (.choice (.thunk (.slot 0) [.slot 0] [])
          (.parallel (.thunk (.slot 0) [.slot 0] []) (.thunk (.slot 0) [.slot 0] [])))) =
    some (choiceTerm
      (.application (.constant ⟨["LambdaJit", "thunk"], "2"⟩ (.arrow termType termType))
        (.constant ⟨["LambdaJit", "thunk"], "3"⟩ termType))
      (choiceTerm (.constant ⟨["LambdaJit", "thunk"], "3"⟩ termType)
        (parallelTerm (.constant ⟨["LambdaJit", "thunk"], "3"⟩ termType)
          (.constant ⟨["LambdaJit", "thunk"], "3"⟩ termType)))) := by
  rfl

/-- The writer throws on a thunk whose fillings are fewer than its constant's arity. -/
example : encode exampleSignature
    (.thunk (.apply (.slot 0) (.slot 1)) [] [.thunk (.slot 0) [.slot 0] []]) = none := by
  rfl

/-- The example signature is well formed. -/
example : signatureWellFormed exampleSignature = true := by
  decide

/-! ## The reading of the encoding is the readback -/

/-- The readings of a list of article terms, defined when each is defined. -/
def readList (signature : Signature) : List Article.Term → Option (List Semantics.Term)
  | [] => some []
  | term :: terms => do
      let head ← read signature term
      let tail ← readList signature terms
      pure (head :: tail)

/-- The reading of `head` applied to `arguments`: the arguments are read, and `head` reads them
before the further values. -/
theorem readAppliedApplyArguments (signature : Signature) :
    ∀ (arguments : List Article.Term) (head : Article.Term) (values : List Semantics.Term),
    readApplied signature (applyArguments head arguments) values =
      (readList signature arguments).bind
        (fun argumentTerms => readApplied signature head (argumentTerms ++ values))
  | [], head, values => by simp [applyArguments, readList]
  | argument :: arguments, head, values => by
      rw [applyArguments,
        readAppliedApplyArguments signature arguments (.application head argument) values]
      have unfoldRead : Interpretation.read signature argument = readApplied signature argument [] := rfl
      cases argumentRead : readApplied signature argument [] with
      | none =>
          cases restRead : readList signature arguments with
          | none => simp [readList, unfoldRead, argumentRead, restRead]
          | some argumentTerms => simp [readList, unfoldRead, argumentRead, restRead, readApplied]
      | some argumentTerm =>
          cases restRead : readList signature arguments with
          | none => simp [readList, unfoldRead, argumentRead, restRead]
          | some argumentTerms => simp [readList, unfoldRead, argumentRead, restRead, readApplied]

theorem readbackListCons (term : FiniteTerm) (terms : List FiniteTerm) :
    readbackList (term :: terms) =
      (readback term).bind (fun head => (readbackList terms).map (head :: ·)) := by
  simp only [readbackList]
  cases readback term <;> cases readbackList terms <;> rfl

theorem readbackListLength : ∀ (terms : List FiniteTerm) (readBack : List Semantics.Term),
    readbackList terms = some readBack → readBack.length = terms.length
  | [], readBack, equal => by
      simp only [readbackList, Option.some.injEq] at equal
      rw [← equal]
      rfl
  | term :: terms, readBack, equal => by
      cases headReadback : readback term with
      | none => simp [readbackList, headReadback] at equal
      | some head =>
          cases tailReadback : readbackList terms with
          | none => simp [readbackList, headReadback, tailReadback] at equal
          | some tail =>
              simp only [readbackList, headReadback, tailReadback, Option.bind_eq_bind,
                Option.bind_some, Option.pure_def, Option.some.injEq] at equal
              rw [← equal, List.length_cons, List.length_cons,
                readbackListLength terms tail tailReadback]

theorem fillLength {α : Type} (hole : Hole) (holes : List Hole) (values : List α) (argument : α) :
    (fill hole holes values argument).length =
      values.length + (if hole = .ignored then 0 else 1) := by
  cases hole with
  | ignored => simp [fill]
  | slot index =>
      simp only [fill, List.length_append, List.length_take, List.length_cons, List.length_drop]
      simp
      omega

/-- The slot values a thunk's holes make: its fillings and one value per hole that is a slot. -/
theorem finalSlotsLength : ∀ (holes : List Hole) (values : List Semantics.Term),
    (finalSlots holes values).length = values.length + slotHoleCount holes
  | [], values => by simp [finalSlots, slotHoleCount]
  | hole :: holes, values => by
      rw [finalSlots, finalSlotsLength holes, fillLength, List.length_map]
      cases hole with
      | ignored =>
          simp [slotHoleCount, List.filter]
      | slot index =>
          have kept : (Hole.slot index != Hole.ignored) = true := rfl
          simp only [slotHoleCount, List.filter, kept, List.length_cons]
          simp
          omega

mutual
/-- A code whose readback is defined reads only slots that have a value. -/
theorem slotCountOfReadbackCode : ∀ (code : Code) (slots : List Semantics.Term)
    (term : Semantics.Term), readbackCode slots code = some term → slotCount code ≤ slots.length
  | .slot index, slots, term, readBack => by
      simp only [readbackCode] at readBack
      have := (List.getElem?_eq_some_iff.mp readBack).1
      simp only [slotCount]
      omega
  | .apply function argument, slots, term, readBack => by
      cases functionReadback : readbackCode slots function with
      | none => simp [readbackCode, functionReadback] at readBack
      | some functionTerm =>
          cases argumentReadback : readbackCode slots argument with
          | none => simp [readbackCode, functionReadback, argumentReadback] at readBack
          | some argumentTerm =>
              have functionBound := slotCountOfReadbackCode function slots _ functionReadback
              have argumentBound := slotCountOfReadbackCode argument slots _ argumentReadback
              simp only [slotCount]
              omega
  | .thunk code holes fillings, slots, term, readBack => by
      cases fillingsReadback : readbackCodeList slots fillings with
      | none => simp [readbackCode, fillingsReadback] at readBack
      | some fillingTerms =>
          simp only [slotCount]
          exact slotCountListOfReadbackCodeList fillings slots _ fillingsReadback
  | .choice left right, slots, term, readBack => by
      cases leftReadback : readbackCode slots left with
      | none => simp [readbackCode, leftReadback] at readBack
      | some leftTerm =>
          cases rightReadback : readbackCode slots right with
          | none => simp [readbackCode, leftReadback, rightReadback] at readBack
          | some rightTerm =>
              have leftBound := slotCountOfReadbackCode left slots _ leftReadback
              have rightBound := slotCountOfReadbackCode right slots _ rightReadback
              simp only [slotCount]
              omega
  | .parallel left right, slots, term, readBack => by
      cases leftReadback : readbackCode slots left with
      | none => simp [readbackCode, leftReadback] at readBack
      | some leftTerm =>
          cases rightReadback : readbackCode slots right with
          | none => simp [readbackCode, leftReadback, rightReadback] at readBack
          | some rightTerm =>
              have leftBound := slotCountOfReadbackCode left slots _ leftReadback
              have rightBound := slotCountOfReadbackCode right slots _ rightReadback
              simp only [slotCount]
              omega

theorem slotCountListOfReadbackCodeList : ∀ (codes : List Code) (slots : List Semantics.Term)
    (terms : List Semantics.Term), readbackCodeList slots codes = some terms →
      slotCountList codes ≤ slots.length
  | [], _, _, _ => by simp [slotCountList]
  | code :: codes, slots, terms, readBack => by
      cases headReadback : readbackCode slots code with
      | none => simp [readbackCodeList, headReadback] at readBack
      | some head =>
          cases tailReadback : readbackCodeList slots codes with
          | none => simp [readbackCodeList, headReadback, tailReadback] at readBack
          | some tail =>
              have headBound := slotCountOfReadbackCode code slots _ headReadback
              have tailBound := slotCountListOfReadbackCodeList codes slots _ tailReadback
              simp only [slotCountList]
              omega
end

/-- A thunk constant applied to the readings `values` of its fillings reads as the readback of the
thunk, where the values are as many as the constant's arity or there are none. With none and an
arity other than 0, both are undefined: the code reads a slot beyond the holes. -/
theorem readLiteralThunk (code : Code) (holes : List Hole) (values : List Semantics.Term)
    (counted : values.isEmpty = true ∨ values.length = thunkArity code holes) :
    (Operator.thunk code holes).readLiteral values =
      (readbackCode (finalSlots holes values) code).bind
        (fun body => some (abstractions holes.length body)) := by
  simp only [Operator.readLiteral]
  split
  · cases readbackCode (finalSlots holes values) code <;> rfl
  · rename_i otherCount
    have empty : values = [] := by
      cases counted with
      | inl isEmpty => exact List.isEmpty_iff.mp isEmpty
      | inr length => exact absurd length otherCount
    subst empty
    cases bodyReadback : readbackCode (finalSlots holes []) code with
    | none => rfl
    | some body =>
        have bound := slotCountOfReadbackCode code _ body bodyReadback
        rw [finalSlotsLength, List.length_nil, Nat.zero_add] at bound
        have : thunkArity code holes = 0 := by
          simp only [thunkArity]
          omega
        exact absurd this.symm otherCount

mutual
/-- Wherever the writer writes an article term for a finite term, the reading ⟦·⟧ of that article
term is the readback of the finite term, as partial functions: undefined together, and equal
where defined, on a well-formed signature. -/
theorem readEncode {signature : Signature} (wellFormed : signatureWellFormed signature = true) :
    ∀ (term : FiniteTerm) (encoded : Article.Term),
    encode signature term = some encoded → read signature encoded = readback term
  | .thunk code holes fillings, encoded, encodedEqual => by
      have fillingsRead := readEncodeList wellFormed fillings
      simp only [encode] at encodedEqual
      split at encodedEqual
      · rename_i counted
        split at encodedEqual
        · rename_i name found
          cases fillingsEncoded : encodeList signature fillings with
          | none => simp [fillingsEncoded] at encodedEqual
          | some fillingTerms =>
            simp only [fillingsEncoded, Option.map_some, Option.some.injEq] at encodedEqual
            subst encodedEqual
            have readings := fillingsRead fillingTerms fillingsEncoded
            simp only [Interpretation.read, readAppliedApplyArguments, readings, List.append_nil]
            simp only [readApplied, thunkConstant, operatorOfNameOf wellFormed found]
            cases fillingsReadback : readbackList fillings with
            | none => simp [readback, fillingsReadback]
            | some values =>
                have length := readbackListLength fillings values fillingsReadback
                have valuesCounted :
                    values.isEmpty = true ∨ values.length = thunkArity code holes := by
                  cases counted.2 with
                  | inl isEmpty =>
                      left
                      rw [List.isEmpty_iff] at isEmpty ⊢
                      subst isEmpty
                      exact List.eq_nil_of_length_eq_zero length
                  | inr fillingsLength =>
                      right
                      rw [length, fillingsLength]
                simp only [Option.bind_some, readLiteralThunk code holes values valuesCounted,
                  readback, fillingsReadback, Option.bind_eq_bind, Option.pure_def]
        · cases encodedEqual
      · cases encodedEqual
  | .apply function argument, encoded, encodedEqual => by
      cases functionEncoded : encode signature function with
      | none => simp [encode, functionEncoded] at encodedEqual
      | some functionTerm =>
          cases argumentEncoded : encode signature argument with
          | none => simp [encode, functionEncoded, argumentEncoded] at encodedEqual
          | some argumentTerm =>
              simp only [encode, functionEncoded, argumentEncoded, Option.bind_eq_bind,
                Option.bind_some, Option.pure_def, Option.some.injEq] at encodedEqual
              subst encodedEqual
              have functionRead := readEncode wellFormed function functionTerm functionEncoded
              have argumentRead := readEncode wellFormed argument argumentTerm argumentEncoded
              have spelled : applyTerm functionTerm argumentTerm =
                  applyArguments (.constant applyName binaryType) [functionTerm, argumentTerm] :=
                rfl
              rw [spelled, Interpretation.read, readAppliedApplyArguments signature]
              simp only [readList, Interpretation.read] at functionRead argumentRead ⊢
              simp only [readback]
              rw [functionRead, argumentRead]
              cases readback function <;> cases readback argument <;>
                simp [readApplied, operatorOfApply, Operator.readLiteral]
  | .choice left right, encoded, encodedEqual => by
      cases leftEncoded : encode signature left with
      | none => simp [encode, leftEncoded] at encodedEqual
      | some leftTerm =>
          cases rightEncoded : encode signature right with
          | none => simp [encode, leftEncoded, rightEncoded] at encodedEqual
          | some rightTerm =>
              simp only [encode, leftEncoded, rightEncoded, Option.bind_eq_bind,
                Option.bind_some, Option.pure_def, Option.some.injEq] at encodedEqual
              subst encodedEqual
              have leftRead := readEncode wellFormed left leftTerm leftEncoded
              have rightRead := readEncode wellFormed right rightTerm rightEncoded
              have spelled : choiceTerm leftTerm rightTerm =
                  applyArguments (.constant choiceName binaryType) [leftTerm, rightTerm] :=
                rfl
              rw [spelled, Interpretation.read, readAppliedApplyArguments signature]
              simp only [readList, Interpretation.read] at leftRead rightRead ⊢
              simp only [readback]
              rw [leftRead, rightRead]
              cases readback left <;> cases readback right <;>
                simp [readApplied, operatorOfChoice, Operator.readLiteral]
  | .parallel left right, encoded, encodedEqual => by
      cases leftEncoded : encode signature left with
      | none => simp [encode, leftEncoded] at encodedEqual
      | some leftTerm =>
          cases rightEncoded : encode signature right with
          | none => simp [encode, leftEncoded, rightEncoded] at encodedEqual
          | some rightTerm =>
              simp only [encode, leftEncoded, rightEncoded, Option.bind_eq_bind,
                Option.bind_some, Option.pure_def, Option.some.injEq] at encodedEqual
              subst encodedEqual
              have leftRead := readEncode wellFormed left leftTerm leftEncoded
              have rightRead := readEncode wellFormed right rightTerm rightEncoded
              have spelled : parallelTerm leftTerm rightTerm =
                  applyArguments (.constant parallelName binaryType) [leftTerm, rightTerm] :=
                rfl
              rw [spelled, Interpretation.read, readAppliedApplyArguments signature]
              simp only [readList, Interpretation.read] at leftRead rightRead ⊢
              simp only [readback]
              rw [leftRead, rightRead]
              cases readback left <;> cases readback right <;>
                simp [readApplied, operatorOfParallel, Operator.readLiteral]

/-- `readEncode` on a list. -/
theorem readEncodeList {signature : Signature} (wellFormed : signatureWellFormed signature = true) :
    ∀ (terms : List FiniteTerm) (encoded : List Article.Term),
    encodeList signature terms = some encoded → readList signature encoded = readbackList terms
  | [], encoded, encodedEqual => by
      simp only [encodeList, Option.some.injEq] at encodedEqual
      subst encodedEqual
      rfl
  | term :: terms, encoded, encodedEqual => by
      cases headEncoded : encode signature term with
      | none => simp [encodeList, headEncoded] at encodedEqual
      | some head =>
          cases tailEncoded : encodeList signature terms with
          | none => simp [encodeList, headEncoded, tailEncoded] at encodedEqual
          | some tail =>
              simp only [encodeList, headEncoded, tailEncoded, Option.bind_eq_bind,
                Option.bind_some, Option.pure_def, Option.some.injEq] at encodedEqual
              subst encodedEqual
              simp only [readList, readbackList, readEncode wellFormed term head headEncoded,
                readEncodeList wellFormed terms tail tailEncoded]

end

/-! ## The end-to-end theorem on encoded sides -/

/-- The end-to-end theorem on an article whose exported equation is the encoding of two finite
terms: when the reader accepts `text`, every import equation is sound, and an exported theorem is
`left = right` with `left` and `right` the writer's encodings of `first` and `second`, whose
readbacks are defined, then readback first ≃_O readback second; the encodings name thunk
constants by a well-formed signature under which the import equations are sound. -/
theorem endToEndEncoded {text : String} {theory : Article.Theory} {signature : Signature}
    (wellFormed : signatureWellFormed signature = true)
    (accepted : Article.readArticle text = .ok theory)
    (importsSound : ∀ equation ∈ Article.importEquations theory.assumptions,
      EquationSound signature equation.1 equation.2)
    {exported : Article.Sequent} (member : exported ∈ theory.theorems)
    {sideType : Article.LogicType} {first second : FiniteTerm} {left right : Article.Term}
    (firstEncoded : encode signature first = some left)
    (secondEncoded : encode signature second = some right)
    (isEquation : exported.conclusion = .equation sideType left right)
    {firstTerm secondTerm : Semantics.Term}
    (firstReadback : readback first = some firstTerm)
    (secondReadback : readback second = some secondTerm) :
    ContextualEquivalence firstTerm secondTerm :=
  endToEndRead accepted importsSound member isEquation
    ((readEncode wellFormed first left firstEncoded).trans firstReadback)
    ((readEncode wellFormed second right secondEncoded).trans secondReadback)

/-- `endToEndEncoded` on an article whose import set `EndToEnd.importChecked` accepts, as the
fixtures check articles: when `resultChecked` accepts the reading of `text` with the sound
`lemmas` and the exported equation `left = right`, the encodings of `first` and `second`, then
their readbacks, which are defined where the readings of `left` and `right` are, are
contextually equivalent. -/
theorem endToEndEncodedOfChecked {text : String} {lemmas : List EndToEnd.Statement}
    {signature : Signature} {first second : FiniteTerm} {left right : Article.Term}
    (wellFormed : signatureWellFormed signature = true)
    (lemmasSound : ∀ lemma ∈ lemmas, lemma.Sound)
    (checked : EndToEnd.resultChecked signature lemmas left right (Article.readArticle text) = true)
    (firstEncoded : encode signature first = some left)
    (secondEncoded : encode signature second = some right)
    (leftRead : (read signature left).isSome = true)
    (rightRead : (read signature right).isSome = true) :
    ∃ firstTerm secondTerm, readback first = some firstTerm ∧
      readback second = some secondTerm ∧ ContextualEquivalence firstTerm secondTerm := by
  obtain ⟨firstTerm, firstRead⟩ := Option.isSome_iff_exists.mp leftRead
  obtain ⟨secondTerm, secondRead⟩ := Option.isSome_iff_exists.mp rightRead
  refine ⟨firstTerm, secondTerm, ?_, ?_, ?_⟩
  · rw [← readEncode wellFormed first left firstEncoded, firstRead]
  · rw [← readEncode wellFormed second right secondEncoded, secondRead]
  · exact contextualEquivalenceOfRead (endToEndOfChecked lemmasSound checked) firstRead
      secondRead

end LambdaJit.Encoding
