package gezi.contest.corpora.reductions

import gezi.contest.corpora.claims.AttractorKind
import gezi.contest.corpora.claims.AttractorRecursion
import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The Scott data a site of a stage one family takes or answers: unary
  * naturals, binary naturals, lists of Booleans, and Booleans. A site's datum
  * is never a Boolean, since two Booleans give only four distinct pairs.
  */
enum SiteDataType:
  case Unary, Binary, BooleanList, Boolean

/** A datum of a site, drawn from the nominal range of its type. */
enum SiteDatum:
  case UnaryNumber(value: Int)
  case BinaryNumber(value: Int)
  case Booleans(bits: Vector[Int])

  /** The datum's Scott term. */
  def term(attractors: Attractors): ProblemTerm = this match
    case UnaryNumber(value)  => unary(value)
    case BinaryNumber(value) => binary(value)
    case Booleans(bits)      => SetFree.booleanList(attractors, bits)

/** A function of the attractor library (`problems/attractors`) of one input,
  * except merge_binary_increment, which is the standard library's define
  * (`SetFree.standardBinaryArithmetic`), with the Scott types of its input and
  * of its answer.
  */
final case class UnaryFunction(
    name: String,
    input: SiteDataType,
    output: SiteDataType
)

/** A function of the attractor library of two inputs, taken in the order left,
  * right; merge_binary_plus, merge_binary_times and merge_binary_equality are
  * the standard library's defines (`SetFree.standardBinaryArithmetic`).
  */
final case class BinaryFunction(
    name: String,
    left: SiteDataType,
    right: SiteDataType,
    output: SiteDataType
)

/** The library functions the stage one families draw their compositions from,
  * and the data their sites take.
  */
object CompositionLibrary:

  import SiteDataType.*

  /** The functions of one input. */
  val unaryFunctions: Vector[UnaryFunction] = Vector(
    UnaryFunction("natural_double", Unary, Unary),
    UnaryFunction("successor", Unary, Unary),
    UnaryFunction("length", BooleanList, Unary),
    UnaryFunction("binary_to_unary", BooleanList, Unary),
    UnaryFunction("unary_to_binary", Unary, BooleanList),
    UnaryFunction("reverse", BooleanList, BooleanList),
    UnaryFunction("bit_set_full", BooleanList, Boolean),
    UnaryFunction("merge_binary_increment", Binary, Binary),
    UnaryFunction("not", Boolean, Boolean)
  )

  /** The functions of two inputs. */
  val binaryFunctions: Vector[BinaryFunction] = Vector(
    BinaryFunction("natural_equal", Unary, Unary, Boolean),
    BinaryFunction("natural_at_least", Unary, Unary, Boolean),
    BinaryFunction("natural_difference", Unary, Unary, Unary),
    BinaryFunction("append", BooleanList, BooleanList, BooleanList),
    BinaryFunction("bit_set_union", BooleanList, BooleanList, BooleanList),
    BinaryFunction("bits_prefix", BooleanList, BooleanList, Boolean),
    BinaryFunction("merge_binary_plus", Binary, Binary, Binary),
    BinaryFunction("merge_binary_times", Binary, Binary, Binary),
    BinaryFunction("merge_binary_equality", Binary, Binary, Boolean),
    BinaryFunction("and", Boolean, Boolean, Boolean),
    BinaryFunction("or", Boolean, Boolean, Boolean),
    BinaryFunction("exclusive", Boolean, Boolean, Boolean),
    BinaryFunction("merge_symbols_equal", Boolean, Boolean, Boolean)
  )

  /** The types a site's datum may have. */
  val dataTypes: Vector[SiteDataType] = Vector(Unary, Binary, BooleanList)

  /** The nominal ranges of the data: a unary natural up to 255, a binary
    * natural up to 1023 and a list of up to 8 Booleans; each type has at least
    * 256 values, so that 256 sites of one type have distinct data.
    */
  val dataParameters: Vector[NominalParameter] = Vector(
    NominalParameter("unary", 0 to 255),
    NominalParameter("binary", 0 to 1023),
    NominalParameter("list_length", 0 to 8)
  )

  /** A datum of the type, drawn from the nominal ranges. */
  def datum(
      draws: Draws,
      ranges: NominalRanges,
      dataType: SiteDataType
  ): (SiteDatum, Draws) = dataType match
    case Unary =>
      val (value, after) = Repetition.drawnNumber(draws, ranges, "unary")
      (SiteDatum.UnaryNumber(value), after)
    case Binary =>
      val (value, after) = Repetition.drawnNumber(draws, ranges, "binary")
      (SiteDatum.BinaryNumber(value), after)
    case BooleanList =>
      val (length, afterLength) =
        Repetition.drawnNumber(draws, ranges, "list_length")
      val (bits, after) =
        (1 to length).foldLeft((Vector.empty[Int], afterLength))((drawn, _) =>
          val (before, beforeDraws) = drawn
          val (bit, afterBit) = beforeDraws.number(0 to 1)
          (before :+ bit, afterBit)
        )
      (SiteDatum.Booleans(bits), after)
    case Boolean =>
      throw IllegalArgumentException("a site's datum is never a Boolean")

  /** A datum of each type, in order. */
  def data(
      draws: Draws,
      ranges: NominalRanges,
      dataTypes: Vector[SiteDataType]
  ): (Vector[SiteDatum], Draws) =
    dataTypes.foldLeft((Vector.empty[SiteDatum], draws))((drawn, dataType) =>
      val (before, beforeDraws) = drawn
      val (value, after) = datum(beforeDraws, ranges, dataType)
      (before :+ value, after)
    )

  /** A function of one input from the input type to the output type, drawn. */
  def unaryFunction(
      draws: Draws,
      input: SiteDataType => Boolean,
      output: SiteDataType
  ): (UnaryFunction, Draws) =
    draws.chosen(
      unaryFunctions.filter(function =>
        input(function.input) && function.output == output
      )
    )

  /** A function of one input whose answer has the type and whose input is a
    * site's datum, drawn.
    */
  def producer(draws: Draws, output: SiteDataType): (UnaryFunction, Draws) =
    unaryFunction(draws, dataTypes.contains, output)

  /** The datum's value, as a native solver reads it. */
  def nativeDatum(datum: SiteDatum): NativeValue = datum match
    case SiteDatum.UnaryNumber(value)  => NativeValue.Unary(value)
    case SiteDatum.BinaryNumber(value) => NativeValue.natural(value)
    case SiteDatum.Booleans(bits)      =>
      NativeValue.Elements(bits.map(bit => NativeValue.Truth(bit == 1)))

  /** The function named, computed natively on the values of its arguments, as
    * the attractor library defines it (`problems/attractors`): the unary
    * naturals as integers, the binary naturals by their value, the lists of
    * Booleans as vectors. Throws for a function not in the pool or arguments of
    * another shape.
    */
  def nativeApplied(name: String, arguments: Vector[NativeValue]): NativeValue =
    import NativeValue.*
    def booleans(values: Vector[NativeValue]): Vector[Boolean] = values.map {
      case Truth(value) => value
      case other => throw IllegalArgumentException(s"not a Boolean: $other")
    }
    def binaryValue(digits: Vector[Boolean]): BigInt =
      digits.foldRight(BigInt(0))((digit, above) =>
        (if digit then 1 else 0) + 2 * above
      )
    def truths(values: Vector[Boolean]): NativeValue = Elements(
      values.map(Truth(_))
    )
    (name, arguments) match
      case ("natural_double", Vector(Unary(value)))      => Unary(2 * value)
      case ("successor", Vector(Unary(value)))           => Unary(value + 1)
      case ("length", Vector(Elements(values)))          => Unary(values.size)
      case ("binary_to_unary", Vector(Elements(values))) =>
        Unary(binaryValue(booleans(values)).toInt)
      case ("unary_to_binary", Vector(Unary(value))) =>
        truths(Vector.tabulate(BigInt(value).bitLength)(BigInt(value).testBit))
      case ("reverse", Vector(Elements(values))) => Elements(values.reverse)
      case ("bit_set_full", Vector(Elements(values))) =>
        Truth(booleans(values).forall(identity))
      case ("merge_binary_increment", Vector(Binary(digits))) =>
        natural(binaryValue(digits) + 1)
      case ("not", Vector(Truth(value)))                        => Truth(!value)
      case ("natural_equal", Vector(Unary(left), Unary(right))) =>
        Truth(left == right)
      case ("natural_at_least", Vector(Unary(left), Unary(right))) =>
        Truth(left >= right)
      case ("natural_difference", Vector(Unary(left), Unary(right))) =>
        Unary(math.max(left - right, 0))
      case ("append", Vector(Elements(left), Elements(right))) =>
        Elements(left ++ right)
      case ("bit_set_union", Vector(Elements(left), Elements(right))) =>
        val (leftBits, rightBits) = (booleans(left), booleans(right))
        val common = leftBits.zip(rightBits).map(_ || _)
        truths(
          common ++ leftBits.drop(common.size) ++ rightBits.drop(common.size)
        )
      case ("bits_prefix", Vector(Elements(left), Elements(right))) =>
        Truth(booleans(right).startsWith(booleans(left)))
      case ("merge_binary_plus", Vector(Binary(left), Binary(right))) =>
        natural(binaryValue(left) + binaryValue(right))
      case ("merge_binary_times", Vector(Binary(left), Binary(right))) =>
        natural(binaryValue(left) * binaryValue(right))
      case ("merge_binary_equality", Vector(Binary(left), Binary(right))) =>
        Truth(left == right)
      case ("and", Vector(Truth(left), Truth(right))) => Truth(left && right)
      case ("or", Vector(Truth(left), Truth(right)))  => Truth(left || right)
      case ("exclusive", Vector(Truth(left), Truth(right))) =>
        Truth(left != right)
      case ("merge_symbols_equal", Vector(Truth(left), Truth(right))) =>
        Truth(left == right)
      case _ => throw IllegalArgumentException(s"no native $name of $arguments")

  /** The function named applied to the arguments inline: as
    * `function_surface/2` writes it in the spelling, except a binary arithmetic
    * function, which is the standard library define's body in every spelling
    * (`SetFree.libraryFunction`).
    */
  def call(
      group: ReductionGroup,
      spelling: Spelling,
      name: String,
      arguments: Vector[ProblemTerm]
  ): ProblemTerm =
    applied(SetFree.libraryFunction(group, name, spelling), arguments)

  /** The body of the define named applied to the arguments. For a binary
    * arithmetic function (`SetFree.standardBinaryArithmetic`) it is the
    * library's term (`StandardLibraryTerms.binaryArithmetic`, on the Scott
    * numerals the sites hold), closed, applied to the arguments, in every
    * spelling. For any other: the attractor's template (`attractor_surface/2`)
    * given its dependencies, its recursion (the function itself for `fixpoint`,
    * the template for `self_application`) and the arguments, each leading
    * abstraction of the template substituted in the host's syntax, so that the
    * site's head is the define's expanded body over its data, not the define's
    * function applied to it. For a `fixpoint` define the function itself still
    * occurs in the body, as the recursion argument.
    */
  def expandedBody(
      group: ReductionGroup,
      spelling: Spelling,
      name: String,
      arguments: Vector[ProblemTerm]
  ): ProblemTerm =
    if SetFree.standardBinaryArithmetic.contains(name) then
      applied(group.standardLibrary.binaryArithmetic(name), arguments)
    else attractorExpandedBody(group.attractors, spelling, name, arguments)

  private def attractorExpandedBody(
      attractors: Attractors,
      spelling: Spelling,
      name: String,
      arguments: Vector[ProblemTerm]
  ): ProblemTerm =
    val kind = attractors.entries
      .collectFirst { case (`name`, entryKind) => entryKind }
      .getOrElse(throw IllegalArgumentException(s"no attractor $name"))
    kind match
      case AttractorKind.Function(dependencies, recursion) =>
        val template = attractors.attractorSurface(name, spelling)
        val dependencySurfaces =
          dependencies.map(attractors.functionSurface(_, spelling))
        val recursive = recursion match
          case AttractorRecursion.NotRecursive => Vector.empty
          case AttractorRecursion.Fixpoint     =>
            Vector(attractors.functionSurface(name, spelling))
          case AttractorRecursion.SelfApplication =>
            Vector(applied(template, dependencySurfaces))
        substituted(template, dependencySurfaces ++ recursive ++ arguments)
      case AttractorKind.Constructor =>
        throw IllegalArgumentException(s"the constructor $name has no body")

  /** The term applied to the arguments, each leading abstraction's body given
    * its argument in the host's syntax, the arguments left over applied in the
    * object language.
    */
  @scala.annotation.tailrec
  private def substituted(
      term: ProblemTerm,
      arguments: Vector[ProblemTerm]
  ): ProblemTerm =
    (term, arguments) match
      case (_, Vector())                           => term
      case (Term.Abstraction(_), argument +: rest) =>
        substituted(Term.instantiated(term, argument), rest)
      case _ => applied(term, arguments)

/** A stage one family whose sites take data of their own: the repeated variant,
  * and the data of each site.
  */
trait RepeatedComposition extends RepeatedVariant:

  /** The data of each site, each a Scott list of the site's data terms. */
  def siteData(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): Vector[ProblemTerm]

/** A stage one family whose draws are a value of `Drawn`, every library
  * function written in the spelling.
  */
abstract class RepeatedCompositionFamily[Drawn](val spelling: Spelling)
    extends RepeatedFamily[Drawn]
    with RepeatedComposition
    with NativelySolved[Drawn]:

  /** The family's name, the first part of its stem. */
  def family: String

  final def stem: String = s"$family/${Repetition.spellingName(spelling)}"

  /** The family's name alone: the twins of one family draw the same data. */
  final override def drawStem: String = family

  /** The data of each site, in order. */
  protected def data(drawn: Drawn): Vector[Vector[SiteDatum]]

  final def siteData(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): Vector[ProblemTerm] =
    data(drawnOf(group, seed, repetitions)).map(site =>
      SetFree.scottList(group.attractors, site.map(_.term(group.attractors)))
    )

  /** The nominal ranges of the stage one families: R up to 256 and the ranges
    * of the data.
    */
  final val nominal: NominalRanges =
    NominalRanges(Repetition.repetitions, CompositionLibrary.dataParameters)

  /** The program of the sites: their Scott list, each site written out. */
  protected final def listed(
      group: ReductionGroup,
      sites: Vector[ProblemTerm]
  ): ProblemTerm = SetFree.scottList(group.attractors, sites)

  /** `count` distinct draws of the data of the types. */
  protected final def distinctData(
      draws: Draws,
      count: Int,
      dataTypes: Vector[SiteDataType]
  ): Vector[Vector[SiteDatum]] =
    draws.distinct(count)(CompositionLibrary.data(_, nominal, dataTypes))._1

  /** The function named applied to the arguments, inline. */
  protected final def call(
      group: ReductionGroup,
      name: String,
      arguments: ProblemTerm*
  ): ProblemTerm =
    CompositionLibrary.call(group, spelling, name, arguments.toVector)

  /** The one datum of each site. */
  protected final def single(site: Vector[SiteDatum]): SiteDatum = site match
    case Vector(datum) => datum
    case other         =>
      throw IllegalArgumentException(s"not the one datum of a site: $other")

/** The lowest rung of stage one: `[o S d1, ..., o S dR]`, a closed subterm
  * `S = h c` (h a function of one input and c a datum, both drawn) written out
  * identically at every site, combined by a function o of two inputs (drawn)
  * with a datum d_i that differs at every site.
  */
final class RepeatedIdenticalSubterms(spelling: Spelling)
    extends RepeatedCompositionFamily[RepeatedIdenticalSubterms.Drawn](
      spelling
    ):

  import RepeatedIdenticalSubterms.Drawn

  val family: String = "repeated_identical_subterms"

  val claim: String =
    "gezi.contest.corpora.reductions.RepeatedIdenticalSubtermsReferenceTest"

  /** The native solver: o (h c) d_i, each function computed natively
    * (`CompositionLibrary.nativeApplied`).
    */
  def solved(drawn: Drawn): Vector[NativeValue] =
    val shared = CompositionLibrary.nativeApplied(
      drawn.inner.name,
      Vector(CompositionLibrary.nativeDatum(drawn.constant))
    )
    drawn.data.map(datum =>
      CompositionLibrary.nativeApplied(
        drawn.combination.name,
        Vector(shared, CompositionLibrary.nativeDatum(datum))
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (combination, afterCombination) =
      draws.chosen(
        CompositionLibrary.binaryFunctions.filter(function =>
          CompositionLibrary.dataTypes.contains(function.right)
        )
      )
    val (inner, afterInner) =
      CompositionLibrary.producer(afterCombination, combination.left)
    val (constant, afterConstant) =
      CompositionLibrary.datum(afterInner, nominal, inner.input)
    Drawn(
      combination,
      inner,
      constant,
      distinctData(afterConstant, repetitions, Vector(combination.right))
        .map(single)
    )

  private def site(
      group: ReductionGroup,
      drawn: Drawn,
      datum: SiteDatum
  ): ProblemTerm =
    call(
      group,
      drawn.combination.name,
      call(group, drawn.inner.name, drawn.constant.term(group.attractors)),
      datum.term(group.attractors)
    )

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    listed(group, drawn.data.map(site(group, drawn, _)))

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] = drawn.data.map(site(group, drawn, _))

  protected def data(drawn: Drawn): Vector[Vector[SiteDatum]] =
    drawn.data.map(Vector(_))

/** The draws of `RepeatedIdenticalSubterms`. */
object RepeatedIdenticalSubterms:

  /** The combining function o, the shared subterm's function h and datum c, and
    * the data d_i.
    */
  final case class Drawn(
      combination: BinaryFunction,
      inner: UnaryFunction,
      constant: SiteDatum,
      data: Vector[SiteDatum]
  )

  /** The family in both spellings. */
  val variants: Vector[RepeatedIdenticalSubterms] =
    Repetition.spellings.map(RepeatedIdenticalSubterms(_))

/** `[(\c. g (h c) (k c)) c1, ..., (\c. g (h c) (k c)) cR]`: one abstraction
  * whose body is a composition of library functions (g of two inputs, h and k
  * of one input on the captured value's type, all drawn), written out at every
  * site and closed there over a captured value c_i that differs at every site.
  * Each single program is the body with c_i substituted, `g (h c_i) (k c_i)`.
  */
final class RepeatedClosures(spelling: Spelling)
    extends RepeatedCompositionFamily[RepeatedClosures.Drawn](spelling):

  import RepeatedClosures.Drawn

  val family: String = "repeated_closures"

  val claim: String =
    "gezi.contest.corpora.reductions.RepeatedClosuresReferenceTest"

  /** The native solver: g (h c_i) (k c_i), each function computed natively
    * (`CompositionLibrary.nativeApplied`).
    */
  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.captured.map(datum =>
      val value = CompositionLibrary.nativeDatum(datum)
      CompositionLibrary.nativeApplied(
        drawn.outer.name,
        Vector(
          CompositionLibrary.nativeApplied(drawn.left.name, Vector(value)),
          CompositionLibrary.nativeApplied(drawn.right.name, Vector(value))
        )
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (captured, afterCaptured) = draws.chosen(CompositionLibrary.dataTypes)
    def produced(output: SiteDataType): Boolean =
      CompositionLibrary.unaryFunctions.exists(inner =>
        inner.input == captured && inner.output == output
      )
    val (outer, afterOuter) =
      afterCaptured.chosen(
        CompositionLibrary.binaryFunctions.filter(function =>
          produced(function.left) && produced(function.right)
        )
      )
    val (left, afterLeft) =
      CompositionLibrary.unaryFunction(afterOuter, _ == captured, outer.left)
    val (right, afterRight) =
      CompositionLibrary.unaryFunction(afterLeft, _ == captured, outer.right)
    Drawn(
      outer,
      left,
      right,
      distinctData(afterRight, repetitions, Vector(captured)).map(single)
    )

  private def body(
      group: ReductionGroup,
      drawn: Drawn,
      captured: ProblemTerm
  ): ProblemTerm =
    call(
      group,
      drawn.outer.name,
      call(group, drawn.left.name, captured),
      call(group, drawn.right.name, captured)
    )

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    listed(
      group,
      drawn.captured.map(value =>
        λ(captured => body(group, drawn, captured))(
          value.term(group.attractors)
        )
      )
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.captured.map(value =>
      body(group, drawn, value.term(group.attractors))
    )

  protected def data(drawn: Drawn): Vector[Vector[SiteDatum]] =
    drawn.captured.map(Vector(_))

/** The draws of `RepeatedClosures`. */
object RepeatedClosures:

  /** The body's functions g, h and k, and the captured values c_i. */
  final case class Drawn(
      outer: BinaryFunction,
      left: UnaryFunction,
      right: UnaryFunction,
      captured: Vector[SiteDatum]
  )

  /** The family in both spellings. */
  val variants: Vector[RepeatedClosures] =
    Repetition.spellings.map(RepeatedClosures(_))

/** `[B[x1], ..., B[xR]]`: the body B of one library define (drawn), given its
  * dependencies and its recursion, applied at every site to that site's data
  * x_i and written as the expanded body (`CompositionLibrary.expandedBody`),
  * not as a reference to the define. Each single program is the define's
  * function (`function_surface/2`) applied to the site's data, so the law also
  * checks the expansion against the define.
  */
final class RepeatedLibraryCompositions(spelling: Spelling)
    extends RepeatedCompositionFamily[RepeatedLibraryCompositions.Drawn](
      spelling
    ):

  import RepeatedLibraryCompositions.Drawn

  val family: String = "repeated_library_compositions"

  val claim: String =
    "gezi.contest.corpora.reductions.RepeatedLibraryCompositionsReferenceTest"

  /** The native solver: the define's function computed natively on each site's
    * data (`CompositionLibrary.nativeApplied`).
    */
  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.data.map(site =>
      CompositionLibrary.nativeApplied(
        drawn.define,
        site.map(CompositionLibrary.nativeDatum)
      )
    )

  /** The pool's functions, by name with their input types. */
  private val functions: Vector[(String, Vector[SiteDataType])] =
    CompositionLibrary.unaryFunctions.map(function =>
      (function.name, Vector(function.input))
    ) ++
      CompositionLibrary.binaryFunctions.map(function =>
        (function.name, Vector(function.left, function.right))
      )

  /** Whether the attractor named has a body: its entry's kind is a function,
    * not a constructor.
    */
  private def hasBody(group: ReductionGroup, name: String): Boolean =
    group.attractors.entries.collectFirst { case (`name`, kind) => kind } match
      case Some(AttractorKind.Function(_, _)) => true
      case Some(AttractorKind.Constructor)    => false
      case None => throw IllegalArgumentException(s"no attractor $name")

  /** The defines a seed draws from, with their input types: the pool's
    * functions that have a body and take site data only.
    */
  private[reductions] def defines(
      group: ReductionGroup
  ): Vector[(String, Vector[SiteDataType])] =
    functions.filter((name, inputs) =>
      hasBody(group, name) && inputs.forall(
        CompositionLibrary.dataTypes.contains
      )
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (define, afterDefine) = draws.chosen(defines(group))
    val (name, inputs) = define
    Drawn(name, distinctData(afterDefine, repetitions, inputs))

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    val attractors = group.attractors
    listed(
      group,
      drawn.data.map(site =>
        CompositionLibrary.expandedBody(
          group,
          spelling,
          drawn.define,
          site.map(_.term(attractors))
        )
      )
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.data.map(site =>
      call(group, drawn.define, site.map(_.term(group.attractors))*)
    )

  protected def data(drawn: Drawn): Vector[Vector[SiteDatum]] = drawn.data

/** The draws of `RepeatedLibraryCompositions`. */
object RepeatedLibraryCompositions:

  /** The define's name and each site's data. */
  final case class Drawn(define: String, data: Vector[Vector[SiteDatum]])

  /** The family in both spellings. */
  val variants: Vector[RepeatedLibraryCompositions] =
    Repetition.spellings.map(RepeatedLibraryCompositions(_))

/** The composition `g (h x) (k y)` of library functions, g of two inputs, h and
  * k of one input, the same at every site.
  */
final case class GeneralComposition(
    outer: BinaryFunction,
    left: UnaryFunction,
    right: UnaryFunction
):

  /** The composition over a site's two data, written inline: no abstraction
    * binds it and no define names it.
    */
  def site(
      group: ReductionGroup,
      spelling: Spelling,
      leftDatum: SiteDatum,
      rightDatum: SiteDatum
  ): ProblemTerm =
    val attractors = group.attractors
    CompositionLibrary.call(
      group,
      spelling,
      outer.name,
      Vector(
        CompositionLibrary
          .call(group, spelling, left.name, Vector(leftDatum.term(attractors))),
        CompositionLibrary.call(
          group,
          spelling,
          right.name,
          Vector(rightDatum.term(attractors))
        )
      )
    )

  /** The types of a site's two data. */
  def inputs: Vector[SiteDataType] = Vector(left.input, right.input)

  /** The composition over a site's two data, each function computed natively
    * (`CompositionLibrary.nativeApplied`).
    */
  def solved(leftDatum: SiteDatum, rightDatum: SiteDatum): NativeValue =
    CompositionLibrary.nativeApplied(
      outer.name,
      Vector(
        CompositionLibrary.nativeApplied(
          left.name,
          Vector(CompositionLibrary.nativeDatum(leftDatum))
        ),
        CompositionLibrary.nativeApplied(
          right.name,
          Vector(CompositionLibrary.nativeDatum(rightDatum))
        )
      )
    )

/** The general compositions drawn. */
object GeneralComposition:

  /** g, then h and k answering g's inputs from site data. */
  def drawn(draws: Draws): (GeneralComposition, Draws) =
    val (outer, afterOuter) = draws.chosen(CompositionLibrary.binaryFunctions)
    val (left, afterLeft) = CompositionLibrary.producer(afterOuter, outer.left)
    val (right, afterRight) =
      CompositionLibrary.producer(afterLeft, outer.right)
    (GeneralComposition(outer, left, right), afterRight)

/** `[g (h x1) (k y1), ..., g (h xR) (k yR)]`: the general composition
  * (`GeneralComposition`, drawn) written inline at R sites over data x_i and
  * y_i that differ at every site.
  */
final class RepeatedGeneralCompositions(spelling: Spelling)
    extends RepeatedCompositionFamily[RepeatedGeneralCompositions.Drawn](
      spelling
    ):

  import RepeatedGeneralCompositions.Drawn

  val family: String = "repeated_general_compositions"

  val claim: String =
    "gezi.contest.corpora.reductions.RepeatedGeneralCompositionsReferenceTest"

  /** The native solver: g (h x_i) (k y_i), computed natively. */
  def solved(drawn: Drawn): Vector[NativeValue] = drawn.data.map {
    case Vector(left, right) => drawn.composition.solved(left, right)
    case other               =>
      throw IllegalArgumentException(s"not the two data of a site: $other")
  }

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (composition, afterComposition) = GeneralComposition.drawn(draws)
    Drawn(
      composition,
      distinctData(afterComposition, repetitions, composition.inputs)
    )

  private def site(
      group: ReductionGroup,
      drawn: Drawn,
      data: Vector[SiteDatum]
  ): ProblemTerm = data match
    case Vector(left, right) =>
      drawn.composition.site(group, spelling, left, right)
    case other =>
      throw IllegalArgumentException(s"not the two data of a site: $other")

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    listed(group, drawn.data.map(site(group, drawn, _)))

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] = drawn.data.map(site(group, drawn, _))

  protected def data(drawn: Drawn): Vector[Vector[SiteDatum]] = drawn.data

/** The draws of `RepeatedGeneralCompositions`. */
object RepeatedGeneralCompositions:

  /** The composition and each site's data x_i and y_i. */
  final case class Drawn(
      composition: GeneralComposition,
      data: Vector[Vector[SiteDatum]]
  )

  /** The family in both spellings. */
  val variants: Vector[RepeatedGeneralCompositions] =
    Repetition.spellings.map(RepeatedGeneralCompositions(_))

/** Repetition within repetition: `[o C1 C1', ..., o CR CR']`, at each of R
  * outer sites a function o of two inputs (drawn) over two instances of the
  * general composition (`GeneralComposition`, drawn), `C = g (h x) (k y)`, the
  * 2R inner sites with distinct data, everything written inline.
  */
final class RepeatedNestedCompositions(spelling: Spelling)
    extends RepeatedCompositionFamily[RepeatedNestedCompositions.Drawn](
      spelling
    ):

  import RepeatedNestedCompositions.Drawn

  val family: String = "repeated_nested_compositions"

  val claim: String =
    "gezi.contest.corpora.reductions.RepeatedNestedCompositionsReferenceTest"

  /** The native solver: o C C' at each outer site, the inner compositions
    * computed natively.
    */
  def solved(drawn: Drawn): Vector[NativeValue] = drawn.data.map {
    case Vector(firstLeft, firstRight, secondLeft, secondRight) =>
      CompositionLibrary.nativeApplied(
        drawn.combination.name,
        Vector(
          drawn.composition.solved(firstLeft, firstRight),
          drawn.composition.solved(secondLeft, secondRight)
        )
      )
    case other =>
      throw IllegalArgumentException(
        s"not the four data of an outer site: $other"
      )
  }

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (composition, afterComposition) = GeneralComposition.drawn(draws)
    val output = composition.outer.output
    val (combination, afterCombination) =
      afterComposition.chosen(
        CompositionLibrary.binaryFunctions.filter(function =>
          function.left == output && function.right == output
        )
      )
    val innerData =
      distinctData(afterCombination, 2 * repetitions, composition.inputs)
    Drawn(
      composition,
      combination,
      innerData.grouped(2).map(_.flatten).toVector
    )

  private def site(
      group: ReductionGroup,
      drawn: Drawn,
      data: Vector[SiteDatum]
  ): ProblemTerm = data match
    case Vector(firstLeft, firstRight, secondLeft, secondRight) =>
      CompositionLibrary.call(
        group,
        spelling,
        drawn.combination.name,
        Vector(
          drawn.composition.site(group, spelling, firstLeft, firstRight),
          drawn.composition.site(group, spelling, secondLeft, secondRight)
        )
      )
    case other =>
      throw IllegalArgumentException(
        s"not the four data of an outer site: $other"
      )

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    listed(group, drawn.data.map(site(group, drawn, _)))

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] = drawn.data.map(site(group, drawn, _))

  protected def data(drawn: Drawn): Vector[Vector[SiteDatum]] = drawn.data

/** The draws of `RepeatedNestedCompositions`. */
object RepeatedNestedCompositions:

  /** The inner composition, the outer function o, and each outer site's four
    * data: x and y of its first and of its second inner site.
    */
  final case class Drawn(
      composition: GeneralComposition,
      combination: BinaryFunction,
      data: Vector[Vector[SiteDatum]]
  )

  /** The family in both spellings. */
  val variants: Vector[RepeatedNestedCompositions] =
    Repetition.spellings.map(RepeatedNestedCompositions(_))

/** Every repeated family a seed draws, by family name, with its variants: the
  * variants of `Repeated.scala`, each one family, and the stage one families of
  * this file and of `StandardLibraryFamilies.scala`, each in both spellings,
  * the mixin_builtin families of `MixinBuiltinFamilies.scala` and the CSES
  * families of `CsesFamilies.scala`, each in both spellings.
  */
object RepeatedVariants:

  /** The families, by name; a variant's stem starts with its family's name. */
  val families: Vector[(String, Vector[RepeatedVariant])] =
    val single = Vector[RepeatedVariant](
      ReductionMeaningsRepeated,
      ReductionInterpreterRepeated,
      SetFreePremisesRepeated,
      SetFreeScopeRepeated,
      SetFreeListLawsRepeated,
      ReductionProblemsRepeated.Fibonacci,
      ReductionProblemsRepeated.Products,
      ReductionProblemsRepeated.Grids,
      ReductionProblemsRepeated.Sums,
      ReductionMixinBinaryRepeated,
      SetFreeArithmeticRepeated
    ).map(variant => variant.stem -> Vector(variant))
    val spelled =
      (Vector[Vector[RepeatedCompositionFamily[?] | StandardLibraryFamily[?]]](
        RepeatedIdenticalSubterms.variants,
        RepeatedClosures.variants,
        RepeatedLibraryCompositions.variants,
        RepeatedGeneralCompositions.variants,
        RepeatedNestedCompositions.variants,
        LibraryDoublingParities.variants,
        LibraryBinaryParities.variants,
        LibraryUnsharedDoublings.variants,
        LibraryUnsharedBinary.variants,
        LibraryUnsharedDoublings.largeVariants,
        LibraryUnsharedBinary.largeVariants,
        LibraryUnsharedWordPowers.variants,
        LibraryBinaryDomainTraps.variants,
        LibraryLongestCommonSubsequences.variants,
        LibraryLongestCommonSubsequences.smallVariants,
        LibraryBillboards.variants,
        LibraryBillboards.smallVariants,
        LibraryEditDistances.variants,
        LibraryEditDistances.smallVariants,
        LibrarySmallestTeams.variants,
        LibrarySmallestTeams.smallVariants
      ) ++ LibraryHotspots.rungs ++ LibraryHotspots.calibrations ++ LibraryHotspots.shapedRungs)
        .map(variants =>
          variants.map(familyName).distinct match
            case Vector(family) => family -> variants
            case other          =>
              throw IllegalStateException(
                s"the variants of one family name several: $other"
              )
        )
    val mixinBuiltin = (Vector(
      MixinBuiltinBinary.variants,
      MixinBuiltinNatural.variants
    ) ++ MixinBuiltinBoolean.families).map(variants =>
      variants.map(_.family).distinct match
        case Vector(family) => family -> variants
        case other          =>
          throw IllegalStateException(
            s"the variants of one family name several: $other"
          )
    )
    val cses = CsesFamilies.all.map(variants =>
      variants.map(_.family).distinct match
        case Vector(family) => family -> variants
        case other          =>
          throw IllegalStateException(
            s"the variants of one family name several: $other"
          )
    )
    single ++ spelled ++ mixinBuiltin ++ cses

  /** Every variant. */
  val all: Vector[RepeatedVariant] = families.flatMap(_._2)

  /** The family name of a variant written in a spelling. */
  private def familyName(
      variant: RepeatedCompositionFamily[?] | StandardLibraryFamily[?]
  ): String = variant match
    case composition: RepeatedCompositionFamily[?] => composition.family
    case library: StandardLibraryFamily[?]         => library.family
