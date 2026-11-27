package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term

/** What the set-free families share: spellings read from facts and the
  * Scott lists of Booleans their programs take.
  */
object SetFree:

  /** The spelling a fact names, a constructor of problems/schema/spelling
    * read by its position (`ProblemData.alternative`), in the order of
    * `Spelling`'s cases: direct, then respelled.
    */
  def spelling(term: ProblemField): Spelling =
    ProblemData.alternative(term, Spelling.values.size) match
      case (position, Vector()) => Spelling.fromOrdinal(position)
      case (_, fields)          => throw IllegalArgumentException(s"a spelling has ${fields.size} fields")

  /** The binary arithmetic functions the families take from the standard
    * library's `binary` module, whatever their spelling: a cooperative
    * problem calls the library, so the library function itself is never
    * respelled (only the program's own code is). The families' operands are
    * three-case Scott numerals (`Encodings.binary`), the library's naturals,
    * so the functions are `corpora/library/binary/`'s.
    */
  val standardBinaryArithmetic: Set[String] = StandardLibraryTerms.binaryArithmeticKeys

  /** The function the attractor library names, as `function_surface/2` writes
    * it in the spelling, except a binary arithmetic function
    * (`standardBinaryArithmetic`), which is the library's term of that name
    * (`StandardLibraryTerms.binaryArithmetic`), whatever the spelling.
    */
  def libraryFunction(group: ReductionGroup, name: String, spelling: Spelling): ProblemTerm =
    if standardBinaryArithmetic.contains(name) then group.standardLibrary.binaryArithmetic(name)
    else group.attractors.functionSurface(name, spelling)

  /** The Scott list of the Scott Booleans of the bits, each piece the
    * attractor's direct surface (`boolean_list/2`, `bits_surface/2`).
    */
  def booleanList(attractors: Attractors, bits: Vector[Int]): ProblemTerm =
    bits.foldRight(attractors.attractorSurface("nil", Spelling.Direct))((bit, rest) =>
      attractors.attractorSurface("cons", Spelling.Direct)(bitAttractor(attractors, bit))(rest)
    )

  /** The attractor true for 1, false for 0. */
  def bitAttractor(attractors: Attractors, bit: Int): ProblemTerm = bit match
    case 1     => attractors.attractorSurface("true", Spelling.Direct)
    case 0     => attractors.attractorSurface("false", Spelling.Direct)
    case other => throw IllegalArgumentException(s"not a bit: $other")

  /** The Scott list of the terms, each piece the attractor's direct surface. */
  def scottList(attractors: Attractors, elements: Vector[ProblemTerm]): ProblemTerm =
    elements.foldRight(attractors.attractorSurface("nil", Spelling.Direct))((element, rest) =>
      attractors.attractorSurface("cons", Spelling.Direct)(element)(rest)
    )

  /** The Scott list of the bit lists (`lists_surface/2`). */
  def bitLists(attractors: Attractors, lists: Vector[Vector[Int]]): ProblemTerm =
    scottList(attractors, lists.map(booleanList(attractors, _)))

  /** `n` bits of the linear congruential sequence from the seed, the bit
    * `(Next >> shift) /\ 1` of each state.
    */
  def randomBits(seed: Long, count: Int, shift: Int): Vector[Int] =
    DynamicReferences.states(seed, count).map(state => ((state >> shift) & 1).toInt)
