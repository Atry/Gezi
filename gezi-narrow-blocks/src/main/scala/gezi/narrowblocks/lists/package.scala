package gezi.narrowblocks

/** The opt-in copy of the narrow back end with lists, selected by the extractor `narrow_list_block` of
  * `corpora/compiler/entry_options/extractor`: the narrow grammar's check with
  * the list kind, the list and boolean branches and filtered lets
  * ([[NarrowBlocks]]), lists at run time ([[NarrowList]]), the compilation of a
  * program's narrow blocks to JVM bytecode ([[NarrowBlockCompilation]]) with
  * the memo of a run's recursion calls ([[NarrowMemo]]), and the lemma route
  * ([[LemmaRoute]]). The framework's `gezi.narrowblocks` stays the default
  * beside it until it beats the default everywhere: a general improvement is
  * opt-in by copy on write, the old and the new kept side by side, and the old
  * is deleted only once the new is better everywhere.
  *
  * THE LIST KIND. A filter `e ∥ list_type c`, c a narrow criterion
  * (`binary_set p`), is a decode point of a narrow list: the grammar reads it
  * by its term and the family's backend facts (`data_family`, `data_fields`
  * and `jvm_type(list)` of `list_type`) and holds no type. A closed list
  * decodes only where such a filter stands at its root; the family is never
  * read from the list's constructors alone. At run time a block's value is a
  * natural or a [[NarrowList]], the suffix from `start` of a vector decoded
  * once, so that every suffix shares its cells. A natural read that no filter
  * governs (a native's operand that is a bare binder or a call's result, a
  * block's result) is checked at run time (`instanceof BigInteger`), and a
  * value of the other representation where a filter stands is the block
  * giving no value, the reader then falling back to the choice's other
  * member.
  *
  * THE BRANCHES. The list branch `(e ∥ list_type c) n (λh. λt. a)` takes its
  * cases' positions from `data_family` (nil at 0, cons at 1) and its fields'
  * representations from `data_fields` (the head a narrow natural, the tail a
  * narrow list). The boolean branch `(e ∥ boolean_type) x y` evaluates only
  * the case it selects. Increment and equality are natives with typed
  * versions; equality's result, a boolean, is read from the native's declared
  * result place, a backend fact, and its typed version writes the filter
  * `∥ boolean_type` the boolean branch reads.
  *
  * THE MEMO ([[NarrowMemo]]). Every call of a compiled block, within one run
  * of the block, is keyed by its arguments' values and the recursion called,
  * a list by its decode point and its start, and recorded only once its body
  * has returned, so that a re-entered call misses and is evaluated as
  * without the memo. It needs no mark in the term: it answers only from
  * finished calls, its key holds every input, it applies to every call of
  * every block alike, and emptying it changes only time (the clearing law).
  *
  * THE RECORD LISTS, the opt-in route [[DeclaredFamilyRoute]]. A filter
  * `e ∥ list_type (T c1 … ck)`, T a data family the backend declares with one
  * constructor whose fields are `parameter(0)` to `parameter(k - 1)` and each
  * ci a narrow criterion, is a decode point of a list of records: a closed
  * list decodes there, column by column, into a [[NarrowRecords]]. The grammar
  * gets no new kind: the operand stays a closed term, read by the one decoding
  * entry of a block's literals (`NarrowBlockCompilation.constant`), and only a
  * native's `gezi.jit.NativePlace.NaturalRecordList` whose declared
  * representations are those the filter names reads it. The family is read
  * from the backend's facts and the filter in the term, never from a name or
  * from the record's constructors alone. [[LemmaRoute]] decodes no record.
  *
  * THE FAMILY RESULTS, on the same route. A native whose result place is
  * `gezi.jit.NativePlace.DeclaredFamilyValue` returns a
  * `gezi.jit.ConstructedNaturals`, a constructor's position and its natural
  * fields, and a block calls it only at its root, so that no arithmetic reads
  * it. The block is replaced by that constructor applied to the fields'
  * numerals (`NarrowBlockCompilation.constructedTerm`). The family and the
  * fields' criteria are those of the filter `∥ F c1 … ck` at the root of the
  * body of the term the native is bound to; a value that does not fit them
  * gives no term, and the reader reads the program.
  */
package object lists
