package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** A repeated family of the mixin_builtin problems: programs shaped as MIXINv2's test files over its Builtin
  * library, `problems/mixin_builtin/ThreePlusFour.lambdalattice` the sample.
  * A site is a class that inherits the entries of `Builtin` it uses and
  * the observer `BooleanChurch`, writes its data as nested objects, its
  * members, and is read at a path of labels ending in `church`, whose
  * answer is a Church Boolean. The library is the closed term of the
  * directory tree (`MixinBuiltinLibrary`), bound once around the program,
  * `(λmixin_builtin. …) Library`.
  *
  * The repeated program applies the class's function, written once, to the
  * data of R sites, each a closed fragment of members over the class's self
  * (`Repetition.sites`); a single program writes one site's class with its
  * members written out. Both twins draw their data from the family's name
  * (`drawStem`), and the state after the data is the respelled twin's: from
  * it the twin draws its renaming of the labels and the order of every
  * choice (`MixinBuiltinSpelling`), so that the pair differs only in
  * spelling.
  *
  * The native solver: each site's Boolean, computed from its data
  * (`answer`).
  */
abstract class MixinBuiltinFamily[Site](val spelling: Spelling)
    extends RepeatedFamily[MixinBuiltinFamily.Drawn[Site]]
    with NativelySolved[MixinBuiltinFamily.Drawn[Site]]:

  /** The family's name, the first part of its stem. */
  def family: String

  final def stem: String = s"$family/${Repetition.spellingName(spelling)}"

  /** The family's name alone: the twins draw the same data. */
  final override def drawStem: String = family

  /** A site drawn. */
  protected def site(draws: Draws): (Site, Draws)

  /** The site's answer. */
  def answer(site: Site): Boolean

  /** The entries of `Builtin` the class inherits. */
  protected def inheritedEntries: Vector[String]

  /** The labels the class writes for the site, the library's aside. */
  protected def classLabels(site: Site): Set[String]

  /** The fragments of members the site's data writes over the class's
    * self, each a function of that self.
    */
  protected def fragments(writing: MixinBuiltinWriting, site: Site): Vector[ProblemTerm => ProblemTerm]

  /** The count of the fragments a site writes. */
  protected def fragmentCount: Int

  /** The members of the class after its data, over its self. */
  protected def tail(writing: MixinBuiltinWriting, self: ProblemTerm): Vector[ProblemTerm]

  /** The labels the program reads off the class, the last `church`. */
  protected def readPath: Vector[String]

  final def solved(drawn: MixinBuiltinFamily.Drawn[Site]): Vector[NativeValue] = drawn.sites.map(site => NativeValue.Truth(answer(site)))

  protected final def drawn(group: ReductionGroup, draws: Draws, repetitions: Int): MixinBuiltinFamily.Drawn[Site] =
    val (sites, after) = draws.distinct(repetitions)(site)
    MixinBuiltinFamily.Drawn(sites, after.state)

  /** The class of the fragments: the inherited entries, the observer, the
    * fragments and the tail, over the class's self.
    */
  private def classOf(writing: MixinBuiltinWriting, mixinBuiltin: ProblemTerm, written: Vector[ProblemTerm => ProblemTerm]): ProblemTerm =
    λ(self =>
      choice(
        (inheritedEntries.map(writing.inherited(mixinBuiltin, _, self)) ++
          Vector(writing.observed(mixinBuiltin, self)) ++
          written.map(_(self)) ++
          tail(writing, self))*
      )
    )

  /** The class read at the path: each label projected, then the instance. */
  private def read(writing: MixinBuiltinWriting, mixin: ProblemTerm): ProblemTerm =
    writing.instantiated(readPath.foldLeft(mixin)(writing.projected))

  /** The class's function of the fragments, `λx1 … xk. read (class)`. */
  private def function(writing: MixinBuiltinWriting, mixinBuiltin: ProblemTerm): ProblemTerm =
    abstractions(fragmentCount, arguments => read(writing, classOf(writing, mixinBuiltin, arguments.map(argument => self => argument(self)))))

  /** The site's fragments, each closed, `λself. members`. */
  private def arguments(writing: MixinBuiltinWriting, site: Site): Vector[ProblemTerm] =
    val written = fragments(writing, site)
    assert(written.size == fragmentCount, s"${written.size} fragments, not $fragmentCount")
    written.map(fragment => λ(self => fragment(self)))

  /** The single program of the site, its class written out. */
  private def single(writing: MixinBuiltinWriting, mixinBuiltin: ProblemTerm, site: Site): ProblemTerm =
    read(writing, classOf(writing, mixinBuiltin, fragments(writing, site)))

  /** The direct single program of the site: what a family's point table
    * (`MixinBuiltinPoints`) reads.
    */
  final def directProgram(group: ReductionGroup, site: Site): ProblemTerm = directProgramOver(group.mixinBuiltin.directMixin, site)

  /** The direct single program of the site over another term for the
    * directory `mixin_builtin`: the tests' check that the library the points
    * carry reads as the directory tree's own term does.
    */
  private[reductions] def directProgramOver(mixin: ProblemTerm, site: Site): ProblemTerm =
    λ(mixinBuiltin => single(MixinBuiltinWriting(identity), mixinBuiltin, site))(mixin)

  /** A site drawn from the draws, for the tests' laws. */
  private[reductions] def drawnSite(draws: Draws): (Site, Draws) = site(draws)

  /** The writing of the spelling and the draws a respelling shuffles the
    * choices by, after its renaming.
    */
  private def writingOf(group: ReductionGroup, drawn: MixinBuiltinFamily.Drawn[Site]): (MixinBuiltinWriting, Draws) =
    spelling match
      case Spelling.Direct => (MixinBuiltinWriting(identity), Draws(drawn.spellingState))
      case Spelling.Respelled =>
        val (renaming, after) =
          MixinBuiltinSpelling.renaming(group.mixinBuiltin.labels ++ drawn.sites.flatMap(classLabels), Draws(drawn.spellingState))
        (MixinBuiltinWriting(MixinBuiltinSpelling.renamed(renaming)), after)

  /** The closed term in the spelling: shuffled when respelled. */
  private def spelled(term: ProblemTerm, draws: Draws): (ProblemTerm, Draws) = spelling match
    case Spelling.Direct    => (term, draws)
    case Spelling.Respelled => MixinBuiltinSpelling.shuffled(term, draws)

  /** The library in the spelling. */
  private def library(group: ReductionGroup, writing: MixinBuiltinWriting, draws: Draws): (ProblemTerm, Draws) = spelling match
    case Spelling.Direct    => (group.mixinBuiltin.directMixin, draws)
    case Spelling.Respelled => MixinBuiltinSpelling.shuffled(group.mixinBuiltin.mixinTerm(writing.renamed), draws)

  protected final def repeated(group: ReductionGroup, drawn: MixinBuiltinFamily.Drawn[Site]): ProblemTerm =
    val (writing, draws) = writingOf(group, drawn)
    val (mixin, afterMixin) = library(group, writing, draws)
    val (written, afterFunction) = spelled(λ(mixinBuiltin => function(writing, mixinBuiltin)), afterMixin)
    val (siteArguments, _) = drawn.sites.foldLeft((Vector.empty[Vector[ProblemTerm]], afterFunction)) { case ((found, current), site) =>
      val (spelledArguments, after) = arguments(writing, site).foldLeft((Vector.empty[ProblemTerm], current)) { case ((done, before), argument) =>
        val (spelledArgument, next) = spelled(argument, before)
        (done :+ spelledArgument, next)
      }
      (found :+ spelledArguments, after)
    }
    λ(mixinBuiltin => Repetition.sites(group.attractors, written(mixinBuiltin), siteArguments))(mixin)

  protected final def singles(group: ReductionGroup, drawn: MixinBuiltinFamily.Drawn[Site]): Vector[ProblemTerm] =
    val (writing, draws) = writingOf(group, drawn)
    val (mixin, afterMixin) = library(group, writing, draws)
    drawn.sites
      .foldLeft((Vector.empty[ProblemTerm], afterMixin)) { case ((found, current), site) =>
        val (written, after) = spelled(λ(mixinBuiltin => single(writing, mixinBuiltin, site)), current)
        (found :+ written(mixin), after)
      }
      ._1

/** The draws of the mixin_builtin families. */
object MixinBuiltinFamily:

  /** The sites, and the state of the draws after them, from which the
    * respelled twin draws its spelling.
    */
  final case class Drawn[Site](sites: Vector[Site], spellingState: Long)

  /** The name of the member of a number's `index`-th half: the number's
    * own member for 0, `A_1`, `A_2`, … after it. The sample writes the
    * halves `A_h`, `A_h_h`, …; an index keeps a 128-digit number's labels
    * within a few bytes, where `_h` repeated would make a label's bits, and
    * the steps of each projection, grow with the digit.
    */
  def digitMember(role: String, index: Int): String = if index == 0 then role else s"${role}_$index"

  /** The roles of the operands of `C.Equal(A.Plus(B))`. */
  val roles: Vector[String] = Vector("A", "B", "C")

/** An equation `left + right = result` of the binary or the natural
  * family.
  */
final case class MixinBuiltinEquation(left: BigInt, right: BigInt, result: BigInt):

  /** Whether the equation holds. */
  def holds: Boolean = left + right == result

  /** The operands A, B and C. */
  def operands: Vector[BigInt] = Vector(left, right, result)

/** The members `_sum` and `_check` of the sample: `_sum` is `A.Plus` with
  * the addend `B`, `_check` is `C.Equal` with the other `_sum.sum`.
  */
private[reductions] object MixinBuiltinEquations:

  def tail(writing: MixinBuiltinWriting, self: ProblemTerm): Vector[ProblemTerm] =
    import writing.*
    Vector(
      definition("_sum")(sum => projected(projected(self, "A"), "Plus")(sum) + definition("addend")(addend => keyed(self(self), "B")(addend))),
      definition("_check")(check =>
        projected(projected(self, "C"), "Equal")(check) + definition("other")(other => projected(projected(self, "_sum"), "sum")(other))
      )
    )

  val readPath: Vector[String] = Vector("_check", "equal", "church")

  val tailLabels: Set[String] = Set("_sum", "_check", "Plus", "addend", "sum", "Equal", "other", "equal", "church")

/** `C.Equal(A.Plus(B))` of MIXINv2's BinNatPlus and BinNatEquality, the
  * family `repeated_reduction_mixin_builtin_binary`: A, B and C binary
  * naturals, each written as the sample writes them, a member per half
  * down to Zero (`Odd` with `halfOfPredecessor`, `Even` with `half`). Each
  * operand has b binary digits, b drawn from the parameter `digits`, its
  * most significant digit one; the equation holds or, with even odds,
  * its result is the sum plus the power of two just above it, a new
  * highest bit, as the family's point table writes its failures, so that
  * the comparison reaches the top.
  */
final class MixinBuiltinBinary(spelling: Spelling, val nominal: NominalRanges)
    extends MixinBuiltinFamily[MixinBuiltinEquation](spelling):

  val family: String = MixinBuiltinBinary.name

  val claim: String = "gezi.contest.corpora.reductions.MixinBuiltinBinaryReferenceTest"

  def answer(site: MixinBuiltinEquation): Boolean = site.holds

  protected def site(draws: Draws): (MixinBuiltinEquation, Draws) =
    val (left, afterLeft) = MixinBuiltinBinary.drawnNatural(draws, Repetition.range(nominal, "digits"))
    val (right, afterRight) = MixinBuiltinBinary.drawnNatural(afterLeft, Repetition.range(nominal, "digits"))
    val (holds, afterHolds) = afterRight.chosen(Vector(true, false))
    (MixinBuiltinEquation(left, right, if holds then left + right else MixinBuiltinBinary.missed(left + right)), afterHolds)

  protected val inheritedEntries: Vector[String] = Vector("BinNatEquality", "BinNatPlus")

  protected def classLabels(site: MixinBuiltinEquation): Set[String] =
    MixinBuiltinFamily.roles
      .zip(site.operands)
      .flatMap((role, value) => (0 to value.bitLength).map(MixinBuiltinFamily.digitMember(role, _)))
      .toSet ++ MixinBuiltinEquations.tailLabels ++ Set("BinNatFactory", "Zero", "Odd", "Even", "half", "halfOfPredecessor")

  protected def fragments(writing: MixinBuiltinWriting, site: MixinBuiltinEquation): Vector[ProblemTerm => ProblemTerm] =
    MixinBuiltinFamily.roles.zip(site.operands).map((role, value) => self => MixinBuiltinBinary.members(writing, self, role, value))

  protected val fragmentCount: Int = 3

  protected def tail(writing: MixinBuiltinWriting, self: ProblemTerm): Vector[ProblemTerm] = MixinBuiltinEquations.tail(writing, self)

  protected val readPath: Vector[String] = MixinBuiltinEquations.readPath

/** The numbers and the variants of `MixinBuiltinBinary`. */
object MixinBuiltinBinary:

  val name: String = "repeated_reduction_mixin_builtin_binary"

  /** The members of the number: the member of its `i`-th half for i from
    * 0 to its count of digits, each `Odd` or `Even` with the member of the
    * next half, and the last `Zero`.
    */
  def members(writing: MixinBuiltinWriting, self: ProblemTerm, role: String, value: BigInt): ProblemTerm =
    import writing.*
    choice((0 to value.bitLength).map(index =>
      val digits = value >> index
      val factory = keyed(self(self), "BinNatFactory")
      definition(MixinBuiltinFamily.digitMember(role, index))(number =>
        if digits == 0 then projected(factory, "Zero")(number)
        else
          val (constructor, field) = if digits.testBit(0) then ("Odd", "halfOfPredecessor") else ("Even", "half")
          projected(factory, constructor)(number) +
            definition(field)(half => keyed(self(self), MixinBuiltinFamily.digitMember(role, index + 1))(half))
      )
    )*)

  /** The result of a failing equation: the sum plus the power of two just
    * above it.
    */
  def missed(sum: BigInt): BigInt = sum + (BigInt(1) << sum.bitLength)

  /** A natural of b binary digits, b drawn from the range, its most
    * significant digit one and the others drawn 15 at a time.
    */
  def drawnNatural(draws: Draws, digitsRange: Range.Inclusive): (BigInt, Draws) =
    val (digits, afterDigits) = draws.number(digitsRange)
    require(digits >= 1, s"a natural of $digits digits has no most significant one")
    val chunks = (digits - 1 + 14) / 15
    val (low, after) = (1 to chunks).foldLeft((BigInt(0), afterDigits)) { case ((value, current), _) =>
      val (chunk, next) = current.number(0 to Draws.highBitsCount - 1)
      ((value << 15) | chunk, next)
    }
    ((BigInt(1) << (digits - 1)) | (low & ((BigInt(1) << (digits - 1)) - 1)), after)

  /** The nominal ranges of the round's points: operands of 4 to 32 binary
    * digits, from the smallest sums of `problems/reduction_mixin_binary`
    * (13 + 29) to 32 bits; the 64- and
    * 128-bit sums are rows of the point table. MEASURED 2026-11-21 on
    * 36a4c1554 by a scratch probe (CPUs 4 and 5 of contest.slice, nice 10,
    * the machine loaded), the single direct program of one equation that
    * holds, operands of b digits drawn from the seed 20261031, read by
    * tabling(weak_head) within 20,000,000 steps: under the reference
    * reading's limit of 50,000 tables (`ReadingState.defaultTableLimit`)
    * b = 1 took 72,428 steps and 29,464 tables, b = 3 113,044 steps and
    * 43,264 tables, and from b = 4 every reading stopped at the table limit;
    * with the tables raised to 400,000, b = 4 took 135,742 steps and 50,732
    * tables, b = 8 217,483 and 78,505, b = 16 377,244 and 133,386, b = 32
    * 735,915 and 252,573 (12.9 s on that machine): about 21,000 steps and
    * 7,200 tables a digit over about 50,000 and 22,000 for the library's
    * look-ups. R sites cost about R times one (R = 4 at one or two digits:
    * 353,688 steps and 128,842 tables, against 99,623 and 37,968 at R = 1).
    * So no site of this range is read by the reference reading, which the
    * points do not need (`NativelySolved`); the hypothesis that
    * today's entries answer no sum above 13 + 29 is what
    * the family measures.
    */
  val nominal: NominalRanges = NominalRanges(Repetition.repetitions, Vector(NominalParameter("digits", 4 to 32)))

  /** The family in both spellings. */
  val variants: Vector[MixinBuiltinBinary] = Repetition.spellings.map(MixinBuiltinBinary(_, nominal))

/** `C.Equal(A.Plus(B))` of MIXINv2's NatPlusZero, NatPlusSuccessor,
  * NatEqualityZero and NatEqualitySuccessor, the family
  * `repeated_reduction_mixin_builtin_natural`: A, B and C unary naturals,
  * n `Successor` objects over `Zero`, each a member with `predecessor` the
  * member of the next, as MIXINv2's NatConstants writes them. The operands
  * are drawn from the parameter `operand`; the equation holds or, with
  * even odds, its result is off by one, as the family's point table writes
  * its failures.
  */
final class MixinBuiltinNatural(spelling: Spelling, val nominal: NominalRanges)
    extends MixinBuiltinFamily[MixinBuiltinEquation](spelling):

  val family: String = MixinBuiltinNatural.name

  val claim: String = "gezi.contest.corpora.reductions.MixinBuiltinNaturalReferenceTest"

  def answer(site: MixinBuiltinEquation): Boolean = site.holds

  protected def site(draws: Draws): (MixinBuiltinEquation, Draws) =
    val (left, afterLeft) = Repetition.drawnNumber(draws, nominal, "operand")
    val (right, afterRight) = Repetition.drawnNumber(afterLeft, nominal, "operand")
    val (holds, afterHolds) = afterRight.chosen(Vector(true, false))
    (MixinBuiltinEquation(left, right, BigInt(left) + right + (if holds then 0 else 1)), afterHolds)

  protected val inheritedEntries: Vector[String] =
    Vector("NatPlusZero", "NatPlusSuccessor", "NatEqualityZero", "NatEqualitySuccessor")

  protected def classLabels(site: MixinBuiltinEquation): Set[String] =
    MixinBuiltinFamily.roles
      .zip(site.operands)
      .flatMap((role, value) => (0 to value.toInt).map(MixinBuiltinFamily.digitMember(role, _)))
      .toSet ++ MixinBuiltinEquations.tailLabels ++ Set("NatFactory", "Zero", "Successor", "predecessor")

  protected def fragments(writing: MixinBuiltinWriting, site: MixinBuiltinEquation): Vector[ProblemTerm => ProblemTerm] =
    MixinBuiltinFamily.roles.zip(site.operands).map((role, value) => self => MixinBuiltinNatural.members(writing, self, role, value.toInt))

  protected val fragmentCount: Int = 3

  protected def tail(writing: MixinBuiltinWriting, self: ProblemTerm): Vector[ProblemTerm] = MixinBuiltinEquations.tail(writing, self)

  protected val readPath: Vector[String] = MixinBuiltinEquations.readPath

/** The numbers and the variants of `MixinBuiltinNatural`. */
object MixinBuiltinNatural:

  val name: String = "repeated_reduction_mixin_builtin_natural"

  /** The members of the number n: the member of its `i`-th predecessor for
    * i from 0 to n, each a `Successor` with the member of the next as its
    * `predecessor`, and the last `Zero`.
    */
  def members(writing: MixinBuiltinWriting, self: ProblemTerm, role: String, value: Int): ProblemTerm =
    import writing.*
    choice((0 to value).map(index =>
      val factory = keyed(self(self), "NatFactory")
      definition(MixinBuiltinFamily.digitMember(role, index))(number =>
        if index == value then projected(factory, "Zero")(number)
        else
          projected(factory, "Successor")(number) +
            definition("predecessor")(predecessor => keyed(self(self), MixinBuiltinFamily.digitMember(role, index + 1))(predecessor))
      )
    )*)

  /** The nominal ranges of the round's points: operands from 0 to 64, the
    * size of MIXINv2's BigNatTest. MEASURED 2026-11-21
    * by the probe of `MixinBuiltinBinary.nominal`, the single direct
    * program of n + n = 2n: under the reference reading's 50,000 tables
    * n = 0 took 37,475 steps and 16,925 tables, n = 2 94,963 and 38,181,
    * n = 4 147,805 and 56,866 (past the limit); with the tables raised to
    * 400,000, n = 8 253,745 and 94,366, n = 16 466,728 and 169,742, n = 32
    * 893,587 and 320,729 (8.5 s), and n = 48 stopped at 400,000 tables:
    * about 26,500 steps and 9,400 tables for each unit of n. The reference
    * reading reads operands up to 2 or 3 only, which the points do not
    * need (`NativelySolved`).
    */
  val nominal: NominalRanges = NominalRanges(Repetition.repetitionsWithin(65 * 65 * 2), Vector(NominalParameter("operand", 0 to 64)))

  /** The family in both spellings. */
  val variants: Vector[MixinBuiltinNatural] = Repetition.spellings.map(MixinBuiltinNatural(_, nominal))

/** A Boolean expression over MIXINv2's BooleanAnd, BooleanOr,
  * BooleanNegation and BooleanEquality.
  */
enum MixinBuiltinExpression:
  case Constant(value: Boolean)
  case Negation(operand: MixinBuiltinExpression)
  case Binary(operation: MixinBuiltinOperation, left: MixinBuiltinExpression, right: MixinBuiltinExpression)

  /** The value of the expression. */
  def truth: Boolean = this match
    case Constant(value)               => value
    case Negation(operand)             => !operand.truth
    case Binary(operation, left, right) => operation.applied(left.truth, right.truth)

  /** The count of the binary operations. */
  def binaryCount: Int = this match
    case Constant(_)             => 0
    case Negation(operand)       => operand.binaryCount
    case Binary(_, left, right)  => 1 + left.binaryCount + right.binaryCount

/** A binary operation: the member of the Boolean that makes its object
  * (`And`) and the member of that object that is its value (`and`).
  */
enum MixinBuiltinOperation(val objectLabel: String, val valueLabel: String):
  case And extends MixinBuiltinOperation("And", "and")
  case Or extends MixinBuiltinOperation("Or", "or")
  case Equal extends MixinBuiltinOperation("Equal", "equal")

  def applied(left: Boolean, right: Boolean): Boolean = this match
    case And   => left && right
    case Or    => left || right
    case Equal => left == right

/** An expression tree of depth d, the family
  * `repeated_reduction_mixin_builtin_boolean_depth_d`, read at church: each
  * binary operation an object, a member `_k` of the class as the sample's
  * `_sum` is (`X.And` with the `other` Y), its value the object's member
  * `and`; a negation the operand's member `not`; a constant the factory's
  * `True` or `False`; and `_check` the root's value. A node of depth k > 0
  * is a negation (one in four) or a binary operation, one operand of
  * depth k − 1 and the other of a depth drawn from 0 to the smaller of
  * k − 1 and the parameter `sibling_depth`, the deeper side drawn, so that
  * the tree has depth d. Each depth is a family of its own, as the
  * hotspots' rungs are (`LibraryHotspots.rungs`): the twins of a family
  * draw the same data, which variants of several depths would not.
  */
final class MixinBuiltinBoolean(spelling: Spelling, val nominal: NominalRanges, val depth: Int)
    extends MixinBuiltinFamily[MixinBuiltinExpression](spelling):

  val family: String = MixinBuiltinBoolean.name(depth)

  val claim: String = "gezi.contest.corpora.reductions.MixinBuiltinBooleanReferenceTest"

  def answer(site: MixinBuiltinExpression): Boolean = site.truth

  protected def site(draws: Draws): (MixinBuiltinExpression, Draws) = expression(draws, depth)

  private def expression(draws: Draws, remaining: Int): (MixinBuiltinExpression, Draws) =
    if remaining == 0 then
      val (value, after) = draws.chosen(Vector(true, false))
      (MixinBuiltinExpression.Constant(value), after)
    else
      val (shape, afterShape) = draws.number(0 to 3)
      if shape == 3 then
        val (operand, after) = expression(afterShape, remaining - 1)
        (MixinBuiltinExpression.Negation(operand), after)
      else
        val operation = MixinBuiltinOperation.fromOrdinal(shape)
        val siblings = Repetition.range(nominal, "sibling_depth")
        val (siblingDepth, afterSibling) = afterShape.number(siblings.start to math.min(siblings.end, remaining - 1))
        val (deepLeft, afterSide) = afterSibling.chosen(Vector(true, false))
        val (first, afterFirst) = expression(afterSide, if deepLeft then remaining - 1 else siblingDepth)
        val (second, afterSecond) = expression(afterFirst, if deepLeft then siblingDepth else remaining - 1)
        (MixinBuiltinExpression.Binary(operation, first, second), afterSecond)

  protected val inheritedEntries: Vector[String] = Vector("BooleanAnd", "BooleanOr", "BooleanNegation", "BooleanEquality")

  protected def classLabels(site: MixinBuiltinExpression): Set[String] =
    (1 to site.binaryCount).map(MixinBuiltinBoolean.nodeMember).toSet ++
      MixinBuiltinOperation.values.flatMap(operation => Vector(operation.objectLabel, operation.valueLabel)) ++
      Set("_check", "church", "not", "other", "BooleanFactory", "True", "False")

  protected def fragments(writing: MixinBuiltinWriting, site: MixinBuiltinExpression): Vector[ProblemTerm => ProblemTerm] =
    Vector(self => MixinBuiltinBoolean.members(writing, self, site))

  protected val fragmentCount: Int = 1

  protected def tail(writing: MixinBuiltinWriting, self: ProblemTerm): Vector[ProblemTerm] = Vector.empty

  protected val readPath: Vector[String] = Vector("_check", "church")

/** The writing and the variants of `MixinBuiltinBoolean`. */
object MixinBuiltinBoolean:

  /** The family of the depth. */
  def name(depth: Int): String = s"repeated_reduction_mixin_builtin_boolean_depth_$depth"

  /** The member of the k-th binary operation, in preorder from 1. */
  def nodeMember(index: Int): String = s"_$index"

  /** The members of the expression over the class's self: the object of
    * each binary operation, and `_check`, inheriting the root's value.
    */
  def members(writing: MixinBuiltinWriting, self: ProblemTerm, expression: MixinBuiltinExpression): ProblemTerm =
    val (value, objects, _) = written(writing, self, expression, 1)
    choice((objects :+ writing.definition("_check")(check => value(check)))*)

  /** The value of the expression, a mixin; the members of its binary
    * operations from `next` on, in preorder; and the index after them.
    */
  private def written(
      writing: MixinBuiltinWriting,
      self: ProblemTerm,
      expression: MixinBuiltinExpression,
      next: Int
  ): (ProblemTerm, Vector[ProblemTerm], Int) =
    import writing.*
    expression match
      case MixinBuiltinExpression.Constant(value) =>
        (projected(keyed(self(self), "BooleanFactory"), if value then "True" else "False"), Vector.empty, next)
      case MixinBuiltinExpression.Negation(operand) =>
        val (operandValue, objects, after) = written(writing, self, operand, next)
        (projected(operandValue, "not"), objects, after)
      case MixinBuiltinExpression.Binary(operation, left, right) =>
        val (leftValue, leftObjects, afterLeft) = written(writing, self, left, next + 1)
        val (rightValue, rightObjects, afterRight) = written(writing, self, right, afterLeft)
        val member = nodeMember(next)
        val operationObject = definition(member)(node =>
          projected(leftValue, operation.objectLabel)(node) + definition("other")(other => rightValue(other))
        )
        (projected(keyed(self(self), member), operation.valueLabel), (operationObject +: leftObjects) ++ rightObjects, afterRight)

  /** The depths of the ladder. */
  val depths: Vector[Int] = Vector(8, 12, 16)

  /** The nominal ranges of the round's points: siblings of any depth
    * below their node's (0 to 15, capped at k - 1 for a node of depth k).
    * MEASURED 2026-11-21 by the probe of `MixinBuiltinBinary.nominal`, the
    * repeated direct program of the seed 20261031: siblings of depth at most
    * 2 made trees of 7 to 23 operations at depths 8 to 16, read in about
    * 20,000 steps and 9,000 tables whatever the depth, the library's
    * look-ups, since a reading reads only the operands an operation needs;
    * with the full range, at R = 1, depth 8 (33 operations) took 44,257
    * steps and 16,727 tables, depth 12 (33) 31,399 and 12,293, depth 16
    * (147) 61,767 and 23,821, within the reference reading's 50,000 tables;
    * at R = 16, depth 8 (282 operations in all) 345,047 and 119,317, depth
    * 12 (921) 631,812 and 211,445, depth 16 (2,390) 1,148,652 and 377,660;
    * at R = 64 depths 8 and 12 stopped at 400,000 tables, and depth 16 ran
    * the probe's 2 GB heap out before it.
    */
  val nominal: NominalRanges = NominalRanges(Repetition.repetitions, Vector(NominalParameter("sibling_depth", 0 to 15)))

  /** Each depth's family in both spellings. */
  val families: Vector[Vector[MixinBuiltinBoolean]] = depths.map(depth => Repetition.spellings.map(MixinBuiltinBoolean(_, nominal, depth)))

/** The point tables of `problems/mixin_builtin`, read
  * as the single-point families `contest_mixin_builtin_binary` and
  * `contest_mixin_builtin_natural`: each row's equation written as the
  * repeated family's direct single program, expecting its Boolean.
  */
object MixinBuiltinPoints:

  private def problems(group: ReductionGroup, table: String, family: MixinBuiltinFamily[MixinBuiltinEquation]): Vector[ReductionProblem] =
    group.problems(MixinBuiltinLibrary.family).rows(table).map {
      case Vector(point, left, right, result) =>
        val equation = MixinBuiltinEquation(ProblemData.integer(left), ProblemData.integer(right), ProblemData.integer(result))
        ReductionProblem(
          ProblemData.text(point),
          family.directProgram(group, equation),
          "boolean",
          Expected.One(Scott.booleanTree(equation.holds)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a point of $table: $other")
    }

  /** The problems of `binary_point`. */
  def binary(group: ReductionGroup): Vector[ReductionProblem] =
    problems(group, "binary_point", MixinBuiltinBinary(Spelling.Direct, MixinBuiltinBinary.nominal))

  /** The problems of `natural_point`. */
  def natural(group: ReductionGroup): Vector[ReductionProblem] =
    problems(group, "natural_point", MixinBuiltinNatural(Spelling.Direct, MixinBuiltinNatural.nominal))
