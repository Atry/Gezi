package gezi.contest.corpora.reductions

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Literals
import gezi.frontend.Term

/** Where a point's reference, the normal forms its points file records,
  * comes from. Reference answers may be computed natively in Scala.
  */
enum Reference:

  /** The normal forms tabling(weak_head) reads from the program within the points
    * file's budget (`Reduction.answeredNormalForms`).
    */
  case Read

  /** The normal forms computed by the family from its draws, in the
    * representation `Reduction.answeredNormalForms` reads back: `claim`
    * names the family's test that checks them against tabling(weak_head)'s reading
    * on small draws.
    */
  case Computed(normalForms: Vector[DeBruijnTerm], claim: String)

/** A point a repeated variant draws: its program, where its reference
  * comes from, and the trap candidates its family computes for it, none by
  * default: closed βη normal forms that the family expects not to be the
  * program's, such as the answers of common wrong solutions
  * (`CsesFamily.trapCandidates`). The judge's points writer offers them as
  * traps through the checks every trap goes through (`PointsFile.written`
  * in contest-judge), so a candidate is never trusted to be outside the
  * reference.
  */
final case class DrawnPoint(program: Term, reference: Reference, trapCandidates: Vector[DeBruijnTerm] = Vector.empty)

/** A point of a corpus family, which the judge's points writer writes by
  * the corpus's name (`CorpusSources` in contest-judge): its name and what
  * it draws, a reduction problem's program read by tabling(weak_head)
  * (`ReductionProblem.corpusPoint`) or a point table's row with the
  * reference the row gives (`CsesPoints`).
  */
final case class CorpusPoint(point: String, drawn: DrawnPoint)

/** The βη normal forms of the standard library's data, as
  * `Reduction.answeredNormalForms` reads them back: `true` is `λt.λf.t` and
  * `false` `λt.λf.f` (the fields 0 and 1 of `corpora/library/native_types/boolean.lambdalattice`),
  * `nil` is `λn.λc.n` and `cons h t` is `λn.λc.c h t` (the fields 0 and 1
  * of `corpora/library/native_types/list.lambdalattice`), `word_end` is `λk.k` and
  * `word_cell b above` is `λk.k b above` (the fields 0 and 1 of
  * `corpora/library/fixed_width/word_representation.lambdalattice`), the marker `constructor` read as its argument.
  */
object StandardLibraryNormalForms:

  /** The word of the width whose bits are the value's, the least
    * significant first.
    */
  def word(width: Int, value: BigInt): DeBruijnTerm =
    require(width >= 0 && value >= 0 && value.bitLength <= width, s"no word of width $width holds $value")
    (0 until width).foldRight(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))) { (position, above) =>
      DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), boolean(value.testBit(position))), above))
    }

  /** The canonical natural of the value as the standard library writes it
    * (`corpora/library/binary`), the normal form of binary_zero, binary_even
    * and binary_odd, the least significant bit outermost
    * (`Literals.naturalTerm`).
    */
  def binary(value: BigInt): DeBruijnTerm =
    require(value >= 0, s"a natural is not negative: $value")
    Literals.naturalTerm(value)

  /** The boolean. */
  def boolean(value: Boolean): DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(if value then 1 else 0)))

  /** The list of the elements, which are closed. */
  def list(elements: Vector[DeBruijnTerm]): DeBruijnTerm =
    elements.foldRight(DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))) { (element, rest) =>
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), element), rest))
      )
    }

  /** The Scott unary numeral: zero is `λz.λs.z` and the successor of p is
    * `λz.λs.s p` (`Encodings.unary`, the attractors `zero` and `successor`).
    */
  def unary(value: Int): DeBruijnTerm =
    require(value >= 0, s"a unary numeral is not negative: $value")
    (1 to value).foldLeft(DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1))))((predecessor, _) =>
      DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), predecessor)))
    )

  /** The binary numeral of the digits, the least significant first, each
    * digit a constructor over the digits above it and the last over zero:
    * zero is `λz.λe.λo.z`, the digit false `λz.λe.λo.e h` and the digit true
    * `λz.λe.λo.o h` (`Encodings.binaryZero`, `binaryEven`, `binaryOdd`). A
    * natural's canonical digits (`NativeValue.natural`) end in true; a
    * computation that builds constructors digit by digit, as the complement
    * does, may end in false.
    */
  def binary(digits: Vector[Boolean]): DeBruijnTerm =
    digits.foldRight(DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(2)))))(
      (digit, above) =>
        DeBruijnTerm.Lambda(
          DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(if digit then 0 else 1), above)))
        )
    )

/** A site's answer as a native solver computes it, plain data with no
  * lambda term, and the normal form the reading returns for it
  * (`StandardLibraryNormalForms`).
  */
enum NativeValue:

  /** A Boolean. */
  case Truth(value: Boolean)

  /** A unary natural. */
  case Unary(value: Int)

  /** A binary numeral's digits, the least significant first. */
  case Binary(digits: Vector[Boolean])

  /** A natural of the standard library, a tuple of its digits. */
  case LibraryNatural(value: BigInt)

  /** A list of values. */
  case Elements(values: Vector[NativeValue])

  /** A fixed_width word of the width holding the value. */
  case Word(width: Int, value: BigInt)

  /** A Scott option, none `λn s. n` or some k `λn s. s k`, as the CSES
    * problems `minimizing_coins` and `message_route` answer, and
    * `shortest_routes_queries` each query.
    */
  case Optional(value: Option[NativeValue])

  /** The normal form of the value. */
  def normalForm: DeBruijnTerm = this match
    case Truth(value)       => StandardLibraryNormalForms.boolean(value)
    case Unary(value)       => StandardLibraryNormalForms.unary(value)
    case Binary(digits)     => StandardLibraryNormalForms.binary(digits)
    case LibraryNatural(value) => StandardLibraryNormalForms.binary(value)
    case Elements(values)   => StandardLibraryNormalForms.list(values.map(_.normalForm))
    case Word(width, value) => StandardLibraryNormalForms.word(width, value)
    case Optional(value)    => value.fold(CsesEncodings.none)(present => CsesEncodings.some(present.normalForm))

/** The values natives build. */
object NativeValue:

  /** The canonical binary numeral of a natural: its digits, the least
    * significant first, with no false above the most significant true
    * (`Encodings.binary`).
    */
  def natural(value: BigInt): NativeValue =
    require(value >= 0, s"a natural is not negative: $value")
    Binary(Vector.tabulate(value.bitLength)(value.testBit))

/** A repeated family whose reference is computed by a native solver
  * (every family's yardstick is a hand-written native Scala solver, [[gezi.contest.corpora.reductions]]): the
  * solver computes each site's answer from the draws in plain Scala, with no
  * lambda term, and the point's reference is the Scott list of the answers'
  * normal forms, in site order (`Reference.Computed`). The claim names the
  * family's test that checks the reference against tabling(weak_head)'s reading on
  * small draws (`ComputedReferenceSuite`).
  */
trait NativelySolved[Drawn] extends RepeatedFamily[Drawn]:

  /** The test that checks the computed reference against
    * tabling(weak_head)'s reading.
    */
  def claim: String

  /** Each site's answer, in site order, computed from the draws. */
  def solved(drawn: Drawn): Vector[NativeValue]

  /** The trap candidates of the draws whose answers, in site order, are
    * given (`DrawnPoint.trapCandidates`): none unless the family computes
    * them.
    */
  def trapCandidates(drawn: Drawn, answers: Vector[NativeValue]): Vector[DeBruijnTerm] = Vector.empty

  /** The draws of the seed for R repetitions, as the point's program is
    * built from them; the native benchmark times `solved` on them.
    */
  final def drawnAt(group: ReductionGroup, seed: Long, repetitions: Int): Drawn = drawnOf(group, seed, repetitions)

  override final def point(group: ReductionGroup, seed: Long, repetitions: Int): DrawnPoint =
    drawnPoint(group, drawnOf(group, seed, repetitions))

  /** The point of the given draws, its reference computed and its trap
    * candidates computed from the same answers: what `point` builds from the
    * draws of a seed. The claim tests give draws whose parameters they
    * enumerate and whose data they generate (`ComputedReferenceSuite`).
    */
  final def drawnPoint(group: ReductionGroup, drawn: Drawn): DrawnPoint =
    val answers = solved(drawn)
    DrawnPoint(
      repeated(group, drawn),
      Reference.Computed(Vector(NativeValue.Elements(answers).normalForm), claim),
      trapCandidates(drawn, answers)
    )

/** Integer arithmetic the native solvers share. */
object NativeArithmetic:

  /** fib(n), fib(0) = 0 and fib(1) = 1, by iteration. */
  def fibonacci(number: Int): BigInt =
    require(number >= 0, s"fib takes no negative number: $number")
    (1 to number).foldLeft((BigInt(0), BigInt(1)))((pair, _) => (pair._2, pair._1 + pair._2))._1

/** A natively solved family with the draws of one point: what the native
  * benchmark times (`gezi.jmh.pipeline.NativeSolverBenchmark`).
  */
final case class NativeProblem[Drawn](family: NativelySolved[Drawn], drawn: Drawn):

  /** Each site's answer, by the family's native solver. */
  def solved: Vector[NativeValue] = family.solved(drawn)

/** The problems a native benchmark times. */
object NativeProblem:

  /** The family's point at the seed and its nominal top rung, the largest R
    * of its nominal range.
    */
  def topRung[Drawn](family: NativelySolved[Drawn], group: ReductionGroup, seed: Long): NativeProblem[Drawn] =
    NativeProblem(family, family.drawnAt(group, seed, family.nominal.repetitions.end))
