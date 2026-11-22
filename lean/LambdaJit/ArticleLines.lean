import LambdaJit.Article

/-!
# The lines of an article text joined by newlines

`Article.articleLines` splits a text with `String.splitOn`, which is defined by well-founded
recursion on byte positions and does not reduce in Lean's kernel. This module proves, once for
every list of lines, that the text made of the lines each followed by a newline splits back into
those lines (`articleLinesJoin`), when no line holds a newline. A fixture whose text is written
as its list of lines then needs the kernel only for the commands of the lines, which `decide`
evaluates.

The proof follows `String.splitOnAux` with the one-character separator `"\n"` along the
characters of the text: a byte position of the text is the UTF-8 size of the characters before
it (`charactersByteSize`), at which `String.Pos.Raw.get` reads the next character
(`getAtPrefix`), and `String.Pos.Raw.extract` between two such positions is the string of the
characters between them (`extractBetween`).
-/

namespace LambdaJit.ArticleLines

/-- The UTF-8 size of a list of characters, the sum of the sizes of its characters. -/
def charactersByteSize : List Char → Nat
  | [] => 0
  | character :: characters => character.utf8Size + charactersByteSize characters

/-- The UTF-8 size of two lists of characters one after the other is the sum of their sizes. -/
theorem charactersByteSizeAppend : ∀ (first second : List Char),
    charactersByteSize (first ++ second) = charactersByteSize first + charactersByteSize second
  | [], second => by simp [charactersByteSize]
  | character :: first, second => by
      simp only [List.cons_append, charactersByteSize, charactersByteSizeAppend first second]
      omega

/-- The byte size of the string of a list of characters is their UTF-8 size. -/
theorem utf8ByteSizeOfList : ∀ characters : List Char,
    (String.ofList characters).utf8ByteSize = charactersByteSize characters
  | [] => rfl
  | character :: characters => by
      have split : String.ofList (character :: characters) =
          String.singleton character ++ String.ofList characters := by
        apply String.ext
        simp [String.toList_append, String.toList_singleton, String.toList_ofList]
      rw [split, String.utf8ByteSize_append, String.utf8ByteSize_singleton,
        utf8ByteSizeOfList characters]
      rfl

/-- The byte size of a string is the UTF-8 size of its characters. -/
theorem utf8ByteSizeCharacters (text : String) :
    text.utf8ByteSize = charactersByteSize text.toList := by
  conv => lhs; rw [← String.ofList_toList (s := text)]
  exact utf8ByteSizeOfList text.toList

/-- `utf8GetAux` at the position after `before` reads the character that follows it. -/
theorem utf8GetAuxAtPrefix (character : Char) (rest : List Char) :
    ∀ (before : List Char) (offset : Nat),
      String.Pos.Raw.utf8GetAux (before ++ character :: rest) ⟨offset⟩
          ⟨offset + charactersByteSize before⟩ = character
  | [], offset => by simp [String.Pos.Raw.utf8GetAux, charactersByteSize]
  | first :: before, offset => by
      have positive := Char.utf8Size_pos first
      have differ :
          (⟨offset⟩ : String.Pos.Raw) ≠ ⟨offset + charactersByteSize (first :: before)⟩ := by
        intro same
        have := congrArg String.Pos.Raw.byteIdx same
        simp only [charactersByteSize] at this
        omega
      simp only [List.cons_append, String.Pos.Raw.utf8GetAux, differ, if_false,
        String.Pos.Raw.add_char_eq]
      have shifted := utf8GetAuxAtPrefix character rest before (offset + first.utf8Size)
      have position : offset + charactersByteSize (first :: before) =
          offset + first.utf8Size + charactersByteSize before := by
        simp only [charactersByteSize]
        omega
      rw [position]
      exact shifted

/-- The character of a text at the byte position after the characters `before`. -/
theorem getAtPrefix {text : String} {before rest : List Char} {character : Char}
    (characters : text.toList = before ++ character :: rest) :
    String.Pos.Raw.get text ⟨charactersByteSize before⟩ = character := by
  have read := utf8GetAuxAtPrefix character rest before 0
  simp only [Nat.zero_add] at read
  simp only [String.Pos.Raw.get, characters]
  exact read

/-- The second loop of `String.Pos.Raw.extract` (`go₂`), from the byte position of `segment`'s
first character to the position after its last, collects `segment`. -/
theorem extractSecond (rest : List Char) : ∀ (segment : List Char) (offset : Nat),
    String.Pos.Raw.extract.go₂ (segment ++ rest) ⟨offset⟩ ⟨offset + charactersByteSize segment⟩ =
      segment
  | [], offset => by
      cases rest with
      | nil => rfl
      | cons first rest => simp [String.Pos.Raw.extract.go₂, charactersByteSize]
  | first :: segment, offset => by
      have positive := Char.utf8Size_pos first
      have differ :
          (⟨offset⟩ : String.Pos.Raw) ≠ ⟨offset + charactersByteSize (first :: segment)⟩ := by
        intro same
        have := congrArg String.Pos.Raw.byteIdx same
        simp only [charactersByteSize] at this
        omega
      have position : offset + charactersByteSize (first :: segment) =
          offset + first.utf8Size + charactersByteSize segment := by
        simp only [charactersByteSize]
        omega
      simp only [List.cons_append, String.Pos.Raw.extract.go₂, differ, if_false,
        String.Pos.Raw.add_char_eq]
      rw [position, extractSecond rest segment (offset + first.utf8Size)]

/-- The first loop of `String.Pos.Raw.extract` (`go₁`) passes the characters `start` before the
start position and hands the rest to the second loop. -/
theorem extractFirst (rest : List Char) (ending : String.Pos.Raw) :
    ∀ (start : List Char) (offset : Nat),
      String.Pos.Raw.extract.go₁ (start ++ rest) ⟨offset⟩ ⟨offset + charactersByteSize start⟩
          ending =
        String.Pos.Raw.extract.go₂ rest ⟨offset + charactersByteSize start⟩ ending
  | [], offset => by
      cases rest with
      | nil => rfl
      | cons first rest => simp [String.Pos.Raw.extract.go₁, charactersByteSize]
  | first :: start, offset => by
      have positive := Char.utf8Size_pos first
      have differ :
          (⟨offset⟩ : String.Pos.Raw) ≠ ⟨offset + charactersByteSize (first :: start)⟩ := by
        intro same
        have := congrArg String.Pos.Raw.byteIdx same
        simp only [charactersByteSize] at this
        omega
      have position : offset + charactersByteSize (first :: start) =
          offset + first.utf8Size + charactersByteSize start := by
        simp only [charactersByteSize]
        omega
      simp only [List.cons_append, String.Pos.Raw.extract.go₁, differ, if_false,
        String.Pos.Raw.add_char_eq]
      rw [position, extractFirst rest ending start (offset + first.utf8Size)]

/-- The string between the byte positions after `start` and after `start ++ segment`. -/
theorem extractBetween {text : String} {start segment rest : List Char}
    (characters : text.toList = start ++ segment ++ rest) :
    String.Pos.Raw.extract text ⟨charactersByteSize start⟩
        ⟨charactersByteSize (start ++ segment)⟩ = String.ofList segment := by
  cases segment with
  | nil => simp [String.Pos.Raw.extract]
  | cons first segment =>
      have positive := Char.utf8Size_pos first
      have ordered :
          ¬ charactersByteSize start ≥ charactersByteSize (start ++ first :: segment) := by
        rw [charactersByteSizeAppend]
        simp only [charactersByteSize]
        omega
      simp only [String.Pos.Raw.extract, ordered, if_false, characters, List.append_assoc]
      have origin : (0 : String.Pos.Raw) = ⟨0⟩ := rfl
      rw [origin]
      have skipped := extractFirst ((first :: segment) ++ rest)
        ⟨charactersByteSize (start ++ first :: segment)⟩ start 0
      simp only [Nat.zero_add] at skipped
      rw [skipped]
      have taken := extractSecond rest (first :: segment) (charactersByteSize start)
      rw [charactersByteSizeAppend]
      rw [taken]

/-- The pieces of `segment ++ rest` split at its newline characters, `segment` holding none: the
characters before each newline and after the last one, each as a string. -/
def pieces : List Char → List Char → List String
  | segment, [] => [String.ofList segment]
  | segment, character :: rest =>
      if character = '\n' then String.ofList segment :: pieces [] rest
      else pieces (segment ++ [character]) rest

/-- `String.splitOnAux` with the separator `"\n"`, from the byte position after the characters
`start ++ segment` with the current piece beginning after `start`, gives the pieces found so far
and then the pieces of the rest. -/
theorem splitOnAuxNewline (text : String) :
    ∀ (rest start segment : List Char) (found : List String),
      text.toList = start ++ segment ++ rest →
        String.splitOnAux text "\n" ⟨charactersByteSize start⟩
            ⟨charactersByteSize (start ++ segment)⟩ 0 found =
          found.reverse ++ pieces segment rest
  | [], start, segment, found, characters => by
      rw [String.splitOnAux.eq_1]
      have atEnd : String.Pos.Raw.atEnd text ⟨charactersByteSize (start ++ segment)⟩ = true := by
        simp only [String.Pos.Raw.atEnd, utf8ByteSizeCharacters, characters, List.append_nil]
        simp
      simp only [atEnd, if_true, extractBetween characters, pieces, List.reverse_cons]
  | character :: rest, start, segment, found, characters => by
      rw [String.splitOnAux.eq_1]
      have notAtEnd :
          String.Pos.Raw.atEnd text ⟨charactersByteSize (start ++ segment)⟩ = false := by
        have positive := Char.utf8Size_pos character
        simp only [String.Pos.Raw.atEnd, utf8ByteSizeCharacters, characters,
          charactersByteSizeAppend, charactersByteSize, decide_eq_false_iff_not]
        omega
      have read : String.Pos.Raw.get text ⟨charactersByteSize (start ++ segment)⟩ = character :=
        getAtPrefix (by rw [characters, List.append_assoc])
      have separator : String.Pos.Raw.get "\n" 0 = '\n' := by decide
      have separatorNext : String.Pos.Raw.next "\n" 0 = ⟨1⟩ := by decide
      have separatorEnd : String.Pos.Raw.atEnd "\n" ⟨1⟩ = true := by decide
      have next : String.Pos.Raw.next text ⟨charactersByteSize (start ++ segment)⟩ =
          ⟨charactersByteSize (start ++ segment) + character.utf8Size⟩ := by
        simp only [String.Pos.Raw.next, read, String.Pos.Raw.add_char_eq]
      simp only [notAtEnd, read, separator, separatorNext, separatorEnd, next]
      by_cases newline : character = '\n'
      · subst newline
        have size : ('\n' : Char).utf8Size = 1 := by decide
        have unoffset : (⟨charactersByteSize (start ++ segment) + ('\n' : Char).utf8Size⟩ :
            String.Pos.Raw).unoffsetBy ⟨1⟩ = ⟨charactersByteSize (start ++ segment)⟩ := by
          simp only [String.Pos.Raw.unoffsetBy, size, Nat.add_sub_cancel]
        have after : charactersByteSize (start ++ segment) + ('\n' : Char).utf8Size =
            charactersByteSize (start ++ segment ++ ['\n']) := by
          rw [charactersByteSizeAppend (start ++ segment) ['\n']]
          simp [charactersByteSize]
        simp only [beq_self_eq_true, if_true, unoffset, extractBetween characters]
        rw [after]
        have inner := splitOnAuxNewline text rest (start ++ segment ++ ['\n']) []
          (String.ofList segment :: found)
          (by rw [characters]; simp)
        simp only [List.append_nil] at inner
        rw [inner]
        simp [pieces]
      · have differ : (character == '\n') = false := by simpa using newline
        have unoffset : (⟨charactersByteSize (start ++ segment)⟩ : String.Pos.Raw).unoffsetBy 0 =
            ⟨charactersByteSize (start ++ segment)⟩ := by
          simp [String.Pos.Raw.unoffsetBy]
        have after : charactersByteSize (start ++ segment) + character.utf8Size =
            charactersByteSize (start ++ (segment ++ [character])) := by
          rw [← List.append_assoc, charactersByteSizeAppend (start ++ segment) [character]]
          simp [charactersByteSize]
        simp only [differ, unoffset, next, if_false, Bool.false_eq_true]
        rw [after]
        have inner := splitOnAuxNewline text rest start (segment ++ [character]) found
          (by rw [characters]; simp)
        rw [inner]
        simp [pieces, newline]

/-- The pieces of the characters of lines each followed by a newline, no line holding one: the
lines, and the empty string after the last newline. -/
theorem piecesOfLines : ∀ lines : List String, (∀ line ∈ lines, '\n' ∉ line.toList) →
    pieces [] (lines.map (fun line => line.toList ++ ['\n'])).flatten = lines ++ [""]
  | [], _ => rfl
  | line :: lines, noNewline => by
      have lineClean : '\n' ∉ line.toList := noNewline line List.mem_cons_self
      have restClean : ∀ other ∈ lines, '\n' ∉ other.toList :=
        fun other member => noNewline other (List.mem_cons_of_mem _ member)
      have segmentPieces : ∀ (segment characters : List Char), '\n' ∉ characters →
          ∀ rest : List Char,
            pieces segment (characters ++ '\n' :: rest) =
              String.ofList (segment ++ characters) :: pieces [] rest := by
        intro segment characters clean rest
        induction characters generalizing segment with
        | nil => simp [pieces]
        | cons character characters inner =>
            have differ : character ≠ '\n' := fun same => clean (same ▸ List.mem_cons_self)
            have innerClean : '\n' ∉ characters :=
              fun member => clean (List.mem_cons_of_mem _ member)
            simp only [List.cons_append, pieces, differ, if_false]
            rw [inner (segment ++ [character]) innerClean]
            simp
      simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.singleton_append]
      rw [segmentPieces [] line.toList lineClean, piecesOfLines lines restClean]
      simp [String.ofList_toList]

/-- The text of lines each followed by a newline, no line holding one, splits back into the
lines. -/
theorem articleLinesJoin (lines : List String) (noNewline : ∀ line ∈ lines, '\n' ∉ line.toList) :
    Article.articleLines (String.join (lines.map (· ++ "\n"))) = lines := by
  have characters : (String.join (lines.map (· ++ "\n"))).toList =
      [] ++ [] ++ (lines.map (fun line => line.toList ++ ['\n'])).flatten := by
    simp only [String.toList_join, List.flatMap, List.map_map, List.nil_append]
    congr 1
    apply List.map_congr_left
    intro line _
    simp [String.toList_append]
  have split := splitOnAuxNewline (String.join (lines.map (· ++ "\n")))
    (lines.map (fun line => line.toList ++ ['\n'])).flatten [] [] [] characters
  simp only [charactersByteSize, List.append_nil, List.reverse_nil, List.nil_append] at split
  have separatorNotEmpty : ("\n" == "") = false := by decide
  unfold Article.articleLines
  simp only [String.splitOn, separatorNotEmpty, Bool.false_eq_true, if_false]
  have origin : (0 : String.Pos.Raw) = ⟨0⟩ := rfl
  rw [origin] at split
  rw [origin, split, piecesOfLines lines noNewline, List.getLast?_concat]
  simp

/-- Whether no line holds a newline, as a Boolean the kernel evaluates: on the characters the
reader takes the line apart into (`Article.characters`), so that a decision that also reads the
lines decodes each line once. -/
def linesClean (lines : List String) : Bool :=
  lines.all fun line => !(Article.characters line).contains '\n'

theorem noNewlineOfLinesClean {lines : List String} (clean : linesClean lines = true) :
    ∀ line ∈ lines, '\n' ∉ line.toList := by
  intro line member inside
  simp only [linesClean, List.all_eq_true, Bool.not_eq_true', Article.characters_eq_toList]
    at clean
  have contained := List.contains_iff_mem.mpr inside
  rw [clean line member] at contained
  cases contained

/-- The reader reads the text of lines each followed by a newline, no line holding one, as it
reads the lines. -/
theorem readArticleOfLines {lines : List String} (clean : linesClean lines = true) :
    Article.readArticle (String.join (lines.map (· ++ "\n"))) = Article.readLines lines := by
  unfold Article.readArticle
  rw [articleLinesJoin lines (noNewlineOfLinesClean clean)]

end LambdaJit.ArticleLines
