package gezi.standardlibrary

/** A term table: a data file under Gezi's directory whose tuple's one field
  * is the Scott tuple of library terms, each imported at the file's top, and
  * the names the host gives the positions, in order, for its own look-up and
  * display (`StandardLibrary.entryMembers`). The file names none of its
  * terms (the host reads no string key), so a field the file
  * adds is added here at its position.
  *
  * @param file
  *   the file's path relative to Gezi's directory
  * @param names
  *   the names of the tuple's fields, in order
  */
final case class TermTable(file: String, names: Vector[String]):
  require(names.distinct.size == names.size, s"a name twice among the fields of $file")

/** The term tables of the tests' and the problem generators' data files. */
object TermTables:

  val problemLibraryTerms: TermTable = TermTable(
    "problems/standard_library_terms/terms.lambdalattice",
    Vector(
      "fixpoint",
      "binary_bitwise_or",
      "binary_minimum",
      "binary_maximum",
      "merge_binary_equality",
      "merge_binary_times",
      "merge_binary_plus",
      "merge_binary_increment",
      "binary_odd",
      "binary_even",
      "binary_zero",
      "word_multiply",
      "word_end",
      "word_cell",
      "false",
      "true",
      "identity",
      "nil",
      "cons",
      "list_fold",
      "compose",
      "even",
      "double",
      "nat_fold",
      "successor",
      "zero"
    )
  )

  val hotSiteTerms: TermTable = TermTable(
    "tests/cancel_fixtures/hot_site_terms.lambdalattice",
    Vector(
      "fixpoint",
      "binary_bitwise_or",
      "binary_minimum",
      "binary_maximum",
      "merge_binary_plus",
      "binary_odd",
      "binary_even",
      "binary_zero"
    )
  )

  val codecTerms: TermTable = TermTable(
    "tests/jit_fixtures/codec_terms.lambdalattice",
    Vector(
      "merge_binary_equality",
      "binary_less_than",
      "binary_maximum",
      "merge_binary_times",
      "merge_binary_plus",
      "int16_negate",
      "merge_binary_increment",
      "int16_type",
      "word_type",
      "word_cell",
      "word_end",
      "binary_set",
      "binary_odd",
      "binary_even",
      "binary_zero",
      "boolean_type",
      "false",
      "true",
      "successor",
      "zero"
    )
  )

  val fixedWidthTerms: TermTable = TermTable(
    "tests/jit_fixtures/fixed_width_terms.lambdalattice",
    Vector(
      "int32_of_natural",
      "int32_to_natural",
      "int32_less_than",
      "int32_equal",
      "int32_negate",
      "int32_multiply",
      "int32_subtract",
      "int32_add",
      "int16_of_natural",
      "int16_to_natural",
      "int16_less_than",
      "int16_equal",
      "int16_negate",
      "int16_multiply",
      "int16_subtract",
      "int16_add",
      "word_of_natural",
      "word_to_natural",
      "word_less_than",
      "word_equal",
      "word_negate",
      "word_multiply",
      "word_subtract",
      "word_add"
    )
  )

  val jitLibraryTerms: TermTable = TermTable(
    "tests/jit_fixtures/library_terms.lambdalattice",
    Vector(
      "merge_binary_increment",
      "binary_odd",
      "binary_even",
      "binary_zero",
      "binary_set",
      "int16_type",
      "word_end",
      "word_cell",
      "word_type",
      "even",
      "double",
      "compose",
      "fixpoint",
      "konstant",
      "identity",
      "list_fold",
      "list_type",
      "cons",
      "nil",
      "boolean_not",
      "boolean_type",
      "false",
      "true",
      "nat_type",
      "nat_fold",
      "successor",
      "zero"
    )
  )

  val zeroUniverseTerms: TermTable = TermTable(
    "tests/jit_fixtures/zero_universe_terms.lambdalattice",
    Vector(
      "no_field",
      "field",
      "no_alternative",
      "alternative",
      "function_type",
      "structure"
    )
  )

  /** The trace showcase's Hindley-Milner page:
    * the judgment
    * type_of, and the type its trace proves the page's program has.
    */
  val showcaseTerms: TermTable = TermTable(
    "tests/jit_fixtures/showcase_terms.lambdalattice",
    Vector("type_of", "function_from_bool_to_bool")
  )

  val programFamilyLibraryTerms: TermTable = TermTable(
    "tests/program_family_fixtures/library_terms.lambdalattice",
    Vector(
      "fixpoint",
      "list_fold",
      "nat_fold",
      "compose",
      "konstant",
      "identity",
      "boolean_not",
      "false",
      "true",
      "cons",
      "nil",
      "successor",
      "zero"
    )
  )
