package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemFamilies

import gezi.frontend.Term

/** The prelude of the contest corpora: a fixpoint combinator and the Scott
  * encoding, all pure lambda, each piece a program file of
  * `problems/prelude_clauses`, read as it is written. The composite functions
  * import the pieces they use off their scope, a recursive one as the fixpoint
  * of its body, whose own file the attractors' sources read too.
  */
final class Prelude(problems: ProblemFamilies):

  private val file = problems("prelude_clauses")

  /** The Y combinator, `fixpoint @ F` reducing to `F @ (fixpoint @ F)`. */
  val fixpoint: ProblemTerm = file.program("fixpoint")

  /** `\x. x`. */
  val identity: ProblemTerm = file.program("identity")

  /** `\k. \_. k`. */
  val konstant: ProblemTerm = file.program("konstant")

  /** The Scott true, `\t. \_. t`. */
  val trueValue: ProblemTerm = file.program("true")

  /** The Scott false, `\_. \f. f`. */
  val falseValue: ProblemTerm = file.program("false")

  /** The empty Scott list, `\n. \_. n`. */
  val nil: ProblemTerm = file.program("nil")

  /** `\h. \t. \_. \c. c h t`. */
  val cons: ProblemTerm = file.program("cons")

  /** `\l. \r. \p. p l r`. */
  val pair: ProblemTerm = file.program("pair")

  /** The first selector of a Scott pair. */
  val first: ProblemTerm = file.program("first")

  /** The second selector of a Scott pair. */
  val second: ProblemTerm = file.program("second")

  /** The Scott zero, `\z. \_. z`. */
  val zero: ProblemTerm = file.program("zero")

  /** `\n. \_. \s. s n`. */
  val successor: ProblemTerm = file.program("successor")

  /** `\a. \b. a true b`. */
  val or: ProblemTerm = file.program("or")

  /** The body `natural_equal` hands its fixpoint, the source of the attractor
    * of the same name (`problems/attractors`).
    */
  val naturalEqualBody: ProblemTerm = file.program("natural_equal_body")

  /** `natural_equal @ M @ N`, the equality of Scott naturals. */
  val naturalEqual: ProblemTerm = file.program("natural_equal")

  /** The body `natural_at_least` hands its fixpoint. */
  val naturalAtLeastBody: ProblemTerm = file.program("natural_at_least_body")

  /** `natural_at_least @ M @ N`, M >= N. */
  val naturalAtLeast: ProblemTerm = file.program("natural_at_least")

  /** The body `natural_difference` hands its fixpoint. */
  val naturalDifferenceBody: ProblemTerm =
    file.program("natural_difference_body")

  /** `natural_difference @ M @ N`, M - N when M >= N. */
  val naturalDifference: ProblemTerm = file.program("natural_difference")

  /** The body `natural_double` hands its fixpoint. */
  val naturalDoubleBody: ProblemTerm = file.program("natural_double_body")

  /** Doubling a Scott natural. */
  val naturalDouble: ProblemTerm = file.program("natural_double")

  /** A BinNat, a Scott list of Scott Booleans least significant bit first, as a
    * unary natural: `bit + 2 * rest`.
    */
  val binaryToUnary: ProblemTerm = file.program("binary_to_unary")

  /** The body `binary_increment` hands its fixpoint. */
  val binaryIncrementBody: ProblemTerm = file.program("binary_increment_body")

  /** A BinNat plus one: a one bit carries, a zero bit stops the carry. */
  val binaryIncrement: ProblemTerm = file.program("binary_increment")

  /** A unary natural as a BinNat, one increment per successor. */
  val unaryToBinary: ProblemTerm = file.program("unary_to_binary")

  /** The body `append` hands its fixpoint. */
  val appendBody: ProblemTerm = file.program("append_body")

  /** Appending two lists. */
  val append: ProblemTerm = file.program("append")

  /** The body `map` hands its fixpoint. */
  val mapBody: ProblemTerm = file.program("map_body")

  /** Mapping a function over a list. */
  val map: ProblemTerm = file.program("map")

  /** The body `length` hands its fixpoint. */
  val lengthBody: ProblemTerm = file.program("length_body")

  /** The length of a list as a Scott natural. */
  val length: ProblemTerm = file.program("length")

  /** The absorbing term `fixpoint @ (\self. \_. self)`: an abstraction that
    * applied to any argument reduces to itself.
    */
  val absorbing: ProblemTerm = file.program("absorbing")

  /** The body `absorbing` hands its fixpoint. */
  val absorbingBody: ProblemTerm = file.program("absorbing_body")

  /** The pieces by the names `prelude.pl` exports them under, in its order. */
  val pieces: Vector[(String, ProblemTerm)] = Vector(
    "fixpoint" -> fixpoint,
    "identity" -> identity,
    "konstant" -> konstant,
    "true" -> trueValue,
    "false" -> falseValue,
    "nil" -> nil,
    "cons" -> cons,
    "pair" -> pair,
    "first" -> first,
    "second" -> second,
    "zero" -> zero,
    "successor" -> successor,
    "or" -> or,
    "natural_equal" -> naturalEqual,
    "natural_at_least" -> naturalAtLeast,
    "natural_difference" -> naturalDifference,
    "natural_double" -> naturalDouble,
    "binary_to_unary" -> binaryToUnary,
    "binary_increment" -> binaryIncrement,
    "unary_to_binary" -> unaryToBinary,
    "append" -> append,
    "map" -> map,
    "length" -> length,
    "absorbing" -> absorbing
  )
