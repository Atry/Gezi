package gezi.contest.corpora.reductions

import java.nio.file.Path
import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions

/** The library terms the repeated problem families build their programs
  * from: the members of the data file `TermTables.problemLibraryTerms` under the
  * root (Gezi's directory, the visible subtree), each read off the
  * file's term by projection (`StandardLibrary.entryMembers`) and held as a
  * closed instruction
  * (`Term.Closed`). A program built from them is a closed term that carries
  * the library's bodies and no name ([[gezi.contest.corpora.reductions]]); nothing is inlined.
  *
  * The names are read here and only here, by the problem generators, to
  * build problems: a family needs these library terms, and taking a member
  * of a file by projection is the general look-up of a tree. No framework
  * code (the saturation, the extraction, the strategies, the JIT, the
  * judge's scoring) reads them, and nothing in the host chooses anything by
  * them: in the framework, knowledge comes in as data and "the code names
  * no type, lemma, combinator or definition" (CONTRIBUTING.md, "Knowledge comes in as data").
  */
final case class StandardLibraryTerms(root: Path, expansions: Expansions):

  /** The members of the library terms' file, by name, read from
    * `expansions`, the URI expansions the owner carries. No later read of
    * the owner's starts from the expansions this read adds, the library's
    * files, which no other read of a group lists or parses.
    */
  private lazy val members: Map[String, Term] =
    StandardLibraryTerms.members(root, expansions)

  private def member(key: String): Term =
    members.getOrElse(key, throw IllegalStateException(s"the key $key is read with the others"))

  /** The binary arithmetic function of the name
    * (`StandardLibraryTerms.binaryArithmeticKeys`) on the Scott numerals the
    * sites of the set-free and repeated-composition families hold, the
    * library's naturals (`corpora/library/binary`):
    * the member of that key. Throws `IllegalArgumentException` for any other
    * name.
    */
  def binaryArithmetic(name: String): Term =
    if StandardLibraryTerms.binaryArithmeticKeys.contains(name) then member(name)
    else throw IllegalArgumentException(s"$name is no binary arithmetic function of the library terms' file")

  def zero: Term = member("zero")
  def successor: Term = member("successor")
  def natFold: Term = member("nat_fold")
  def double: Term = member("double")
  def even: Term = member("even")
  def compose: Term = member("compose")
  def listFold: Term = member("list_fold")
  def cons: Term = member("cons")
  def nil: Term = member("nil")
  def identity: Term = member("identity")
  def trueValue: Term = member("true")
  def falseValue: Term = member("false")
  def wordCell: Term = member("word_cell")
  def wordEnd: Term = member("word_end")
  def wordMultiply: Term = member("word_multiply")
  def binaryZero: Term = member("binary_zero")
  def binaryEven: Term = member("binary_even")
  def binaryOdd: Term = member("binary_odd")
  def binaryIncrement: Term = member("merge_binary_increment")
  def binaryPlus: Term = member("merge_binary_plus")
  def binaryEquality: Term = member("merge_binary_equality")
  def binaryMaximum: Term = member("binary_maximum")
  def binaryMinimum: Term = member("binary_minimum")
  def binaryBitwiseOr: Term = member("binary_bitwise_or")
  def fixpoint: Term = member("fixpoint")

  /** The canonical binary natural of the value
    * (`corpora/library/binary`), built with binary_zero, binary_even and
    * binary_odd, the least significant bit outermost and no binary_even over
    * binary_zero.
    */
  def binary(value: BigInt): Term =
    require(value >= 0, s"a natural is not negative: $value")
    if value == 0 then binaryZero
    else if value.testBit(0) then binaryOdd(binary(value >> 1))
    else binaryEven(binary(value >> 1))

  /** The word of the width whose bits are the value's, the least
    * significant first, built with word_cell and word_end.
    */
  def word(width: Int, value: BigInt): Term =
    require(width >= 0 && value >= 0 && value.bitLength <= width, s"no word of width $width holds $value")
    (0 until width).foldRight(wordEnd)((position, above) =>
      wordCell(if value.testBit(position) then trueValue else falseValue)(above)
    )

  /** successor applied the value times to zero. */
  def numeral(value: Int): Term =
    require(value >= 0, s"a natural is not negative: $value")
    (1 to value).foldLeft(zero)((natural, _) => successor(natural))

  /** The list of the elements, built with cons and nil. */
  def list(elements: Vector[Term]): Term = elements.foldRight(nil)((element, rest) => cons(element)(rest))

  /** `(\f. [f a11 ... a1k, ..., f aR1 ... aRk]) Function`, the list built
    * with the library's cons and nil: the function let bound once and
    * applied at each site to that site's arguments.
    */
  def sites(function: Term, arguments: Vector[Vector[Term]]): Term =
    λ(bound => list(arguments.map(applied(bound, _))))(function)

/** The names of the library terms the families read by name. */
object StandardLibraryTerms:

  /** The keys of the binary arithmetic functions the set-free and
    * repeated-composition families call (`binaryArithmetic`), members of the
    * file.
    */
  val binaryArithmeticKeys: Set[String] =
    Set("merge_binary_increment", "merge_binary_plus", "merge_binary_times", "merge_binary_equality")

  /** The members of the data file under the root, each a closed instruction
    * read by projection (`StandardLibrary.entryMembers`), by the names
    * `TermTables.problemLibraryTerms` gives their positions.
    */
  private def members(root: Path, expansions: Expansions): Map[String, Term] =
    StandardLibrary.entryMembers(root, TermTables.problemLibraryTerms, expansions)._1.view.mapValues(Term.closed).toMap
