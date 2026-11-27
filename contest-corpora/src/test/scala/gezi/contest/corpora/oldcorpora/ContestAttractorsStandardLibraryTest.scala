package gezi.contest.corpora.oldcorpora

import gezi.standardlibrary.SplitMix
import gezi.contest.corpora.claims.ClaimsTesting
import gezi.contest.corpora.claims.Spelling
import gezi.contest.corpora.oldcorpora.ReferenceValue.Elements
import gezi.contest.corpora.oldcorpora.ReferenceValue.Natural
import gezi.contest.corpora.oldcorpora.ReferenceValue.Quantified
import gezi.contest.corpora.oldcorpora.ReferenceValue.Truth
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term
import gezi.frontend.Term.λ

/** The port of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_attractors_standard_library.plt`): the
  * standard library entries of the attractor library (`problems/attractors`,
  * `claims.Attractors`): each function, applied to small Scott values,
  * normalises to the value its definition gives, compared as beta eta normal
  * forms (`BetaEtaNormalisation`, the leftmost outermost normaliser, which
  * reaches the normal form of these terminating applications); and the native
  * references (`AttractorReferences`) agree with the definitions.
  *
  * THE FUEL of a normalisation is 1,000,000 beta contractions, as in the Prolog
  * (`normalised(Term, 1000000, Normal)`): the normaliser counts its own
  * contractions in both languages, not SWI-Prolog inferences nor evaluator
  * steps. A normalisation that runs out of fuel fails its test.
  */
class ContestAttractorsStandardLibraryTest
    extends gezi.generatedinputs.FailFastSuite:

  private val attractors = ClaimsTesting.attractors

  private val tautology = ClaimsTesting.group.corpora.tautology

  private val fuel: Long = 1000000

  private def function(name: String): Term =
    attractors.functionSurface(name, Spelling.Direct)

  private def attractor(name: String): Term =
    attractors.attractorSurface(name, Spelling.Direct)

  /** `surface_normal(Surface, Normal)`: the term normalised; the test fails
    * when the fuel runs out.
    */
  private def surfaceNormal(surface: Term): DeBruijnTerm =
    BetaEtaNormalisation
      .normalised(surface.deBruijnTerm(Map.empty), fuel)
      .getOrElse(fail(s"the normalisation ran past $fuel contractions"))

  /** `expect(Name, Arguments, Expected)`: the function applied to the arguments
    * normalises to the expected term's normal form.
    */
  private def expect(
      name: String,
      arguments: Vector[Term],
      expected: Term
  ): Unit =
    val applied =
      arguments.foldLeft(function(name))((term, argument) => term(argument))
    assertEquals(
      (name, surfaceNormal(applied)),
      (name, surfaceNormal(expected))
    )

  private def value(truth: Boolean): Term = attractor(
    if truth then "true" else "false"
  )

  /** `list_surface(Elements, Surface)`: the Scott list of the surfaces. */
  private def listSurface(elements: Vector[Term]): Term =
    elements.foldRight(attractor("nil"))((element, rest) =>
      attractor("cons")(element)(rest)
    )

  /** `booleans(Names, Surface)`: the Scott list of the Booleans. */
  private def booleans(truths: Vector[Boolean]): Term = listSurface(
    truths.map(value)
  )

  /** `unary_surface(Number, Surface)`: the unary numeral. */
  private def unarySurface(number: BigInt): Term =
    if number == 0 then attractor("zero")
    else attractor("successor")(unarySurface(number - 1))

  private def reference(
      name: String,
      arguments: ReferenceValue*
  ): ReferenceValue =
    AttractorReferences
      .attractorReference(name, arguments.toVector)
      .getOrElse(fail(s"no native reference of $name on $arguments"))

  private def truthOf(result: ReferenceValue): Boolean = result match
    case Truth(found) => found
    case other        => fail(s"not a Boolean: $other")

  private def naturalOf(result: ReferenceValue): BigInt = result match
    case Natural(found) => found
    case other          => fail(s"not a natural: $other")

  private def bitsOf(result: ReferenceValue): Vector[Boolean] = result match
    case Elements(values) => values.map(truthOf)
    case other            => fail(s"not a list: $other")

  private def bitsValue(bits: Vector[Boolean]): ReferenceValue = Elements(
    bits.map(Truth(_))
  )

  test("notAnd") {
    expect("not", Vector(value(true)), value(false))
    expect("not", Vector(value(false)), value(true))
    expect("and", Vector(value(true), value(false)), value(false))
    expect("and", Vector(value(true), value(true)), value(true))
  }

  test("exclusive") {
    Vector(
      (true, true, false),
      (true, false, true),
      (false, true, true),
      (false, false, false)
    ).foreach((left, right, result) =>
      expect("exclusive", Vector(value(left), value(right)), value(result))
    )
  }

  // every_assignment f is true exactly when f is true at both Booleans.
  test("everyAssignment") {
    expect("every_assignment", Vector(λ(x => x)), value(false))
    expect("every_assignment", Vector(λ(_ => value(true))), value(true))
    expect("every_assignment", Vector(λ(_ => value(false))), value(false))
    expect(
      "every_assignment",
      Vector(λ(y => function("or")(y)(function("not")(y)))),
      value(true)
    )
  }

  // The Boolean connectives of the tautology family's encoding
  // (the deleted Prolog file, git show 6ab16a338^:lambda_jit/corpora/contest_tautology.pl) have the library's entries as their
  // normal forms, so a reading by content address recognises them.
  test("theTautologyEncodingHasTheLibrarySConnectives") {
    Vector(
      "not" -> "negation",
      "and" -> "conjunction",
      "or" -> "disjunction",
      "exclusive" -> "exclusive",
      "every_assignment" -> "every_assignment"
    ).foreach((name, encoding) =>
      assertEquals(
        (name, surfaceNormal(tautology.connectives(encoding))),
        (name, attractors.attractorFunction(name))
      )
    )
  }

  test("reverse") {
    expect(
      "reverse",
      Vector(booleans(Vector(true, false, false))),
      booleans(Vector(false, false, true))
    )
  }

  test("foldrRebuildsWithCons") {
    expect(
      "foldr",
      Vector(
        attractor("cons"),
        attractor("nil"),
        booleans(Vector(true, false))
      ),
      booleans(Vector(true, false))
    )
  }

  test("foldlReversesWithAFlippedCons") {
    expect(
      "foldl",
      Vector(
        λ(accumulated => λ(x => attractor("cons")(x)(accumulated))),
        attractor("nil"),
        booleans(Vector(true, false))
      ),
      booleans(Vector(false, true))
    )
  }

  test("concat") {
    expect(
      "concat",
      Vector(
        listSurface(
          Vector(booleans(Vector(true)), booleans(Vector(false, true)))
        )
      ),
      booleans(Vector(true, false, true))
    )
  }

  test("flatMapDoubles") {
    expect(
      "flat_map",
      Vector(
        λ(x => attractor("cons")(x)(attractor("cons")(x)(attractor("nil")))),
        booleans(Vector(true, false))
      ),
      booleans(Vector(true, true, false, false))
    )
  }

  test("zipStopsAtTheShorter") {
    expect(
      "zip",
      Vector(booleans(Vector(true, false)), booleans(Vector(false))),
      listSurface(Vector(attractor("pair")(value(true))(value(false))))
    )
  }

  private val upToThree: Vector[BigInt] = Vector.range(0, 4).map(BigInt(_))

  // The native reference of natural_at_least agrees with the definition on
  // the numerals up to 3: m >= n.
  test("naturalAtLeastReference") {
    for left <- upToThree; right <- upToThree do
      val result =
        truthOf(reference("natural_at_least", Natural(left), Natural(right)))
      expect(
        "natural_at_least",
        Vector(unarySurface(left), unarySurface(right)),
        value(result)
      )
  }

  // The native reference of natural_difference agrees with the definition
  // on the numerals up to 3: the truncated difference max(m - n, 0).
  test("naturalDifferenceReference") {
    for left <- upToThree; right <- upToThree do
      val result = naturalOf(
        reference("natural_difference", Natural(left), Natural(right))
      )
      expect(
        "natural_difference",
        Vector(unarySurface(left), unarySurface(right)),
        unarySurface(result)
      )
  }

  /** `bit_lists(Length, Lists)`: every list of the length of Booleans, in the
    * order of the Prolog's findall (true before false at each place).
    */
  private def bitLists(length: Int): Vector[Vector[Boolean]] =
    if length == 0 then Vector(Vector.empty)
    else
      for first <- Vector(true, false); rest <- bitLists(length - 1)
      yield first +: rest

  /** `small_bit_list(List)`: the lists of at most three Booleans. */
  private val smallBitLists: Vector[Vector[Boolean]] =
    Vector.range(0, 4).flatMap(bitLists)

  // The native references of the list functions agree with the definitions
  // on the lists of at most three Booleans and the numerals up to 5.
  test("lengthReference") {
    smallBitLists.foreach(list =>
      val length = naturalOf(reference("length", bitsValue(list)))
      expect("length", Vector(booleans(list)), unarySurface(length))
    )
  }

  test("binaryToUnaryReference") {
    smallBitLists.foreach(list =>
      val number = naturalOf(reference("binary_to_unary", bitsValue(list)))
      expect("binary_to_unary", Vector(booleans(list)), unarySurface(number))
    )
  }

  test("binaryIncrementReference") {
    smallBitLists.foreach(list =>
      val incremented = bitsOf(reference("binary_increment", bitsValue(list)))
      expect("binary_increment", Vector(booleans(list)), booleans(incremented))
    )
  }

  test("unaryToBinaryReference") {
    Vector
      .range(0, 6)
      .map(BigInt(_))
      .foreach(number =>
        val bits = bitsOf(reference("unary_to_binary", Natural(number)))
        expect("unary_to_binary", Vector(unarySurface(number)), booleans(bits))
      )
  }

  test("bitSetReferences") {
    for list <- smallBitLists; index <- upToThree do
      val member =
        truthOf(reference("bit_set_member", bitsValue(list), Natural(index)))
      val inserted =
        bitsOf(reference("bit_set_insert", bitsValue(list), Natural(index)))
      expect(
        "bit_set_member",
        Vector(booleans(list), unarySurface(index)),
        value(member)
      )
      expect(
        "bit_set_insert",
        Vector(booleans(list), unarySurface(index)),
        booleans(inserted)
      )
  }

  test("bitSetFullReference") {
    smallBitLists.foreach(list =>
      val full = truthOf(reference("bit_set_full", bitsValue(list)))
      expect("bit_set_full", Vector(booleans(list)), value(full))
    )
  }

  test("bitsPrefixReference") {
    for left <- smallBitLists; right <- smallBitLists do
      val prefix =
        truthOf(reference("bits_prefix", bitsValue(left), bitsValue(right)))
      expect(
        "bits_prefix",
        Vector(booleans(left), booleans(right)),
        value(prefix)
      )
  }

  test("bitSetUnionReference") {
    for left <- smallBitLists; right <- smallBitLists do
      val union =
        bitsOf(reference("bit_set_union", bitsValue(left), bitsValue(right)))
      expect(
        "bit_set_union",
        Vector(booleans(left), booleans(right)),
        booleans(union)
      )
  }

  /** `random_formula(Depth, Binders, Formula)`: a formula of depth at most
    * Depth over Binders enclosing binders.
    */
  private def randomFormula(
      depth: Int,
      binders: Int,
      random: SplitMix
  ): (QuantifiedFormula, SplitMix) =
    val (choice, afterChoice) =
      if depth <= 0 then random.between(1, 3) else random.between(1, 8)
    choice match
      case 1 =>
        val (index, after) = afterChoice.between(0, binders - 1)
        (QuantifiedFormula.Bound(index), after)
      case 2 => (QuantifiedFormula.Node("true", Vector.empty), afterChoice)
      case 3 => (QuantifiedFormula.Node("false", Vector.empty), afterChoice)
      case 4 =>
        val (operand, after) = randomFormula(depth - 1, binders, afterChoice)
        (QuantifiedFormula.Node("not", Vector(operand)), after)
      case 8 =>
        val (body, after) = randomFormula(depth - 1, binders + 1, afterChoice)
        (
          QuantifiedFormula.Node(
            "every_assignment",
            Vector(QuantifiedFormula.Binder(body))
          ),
          after
        )
      case binary =>
        val name = Vector("and", "or", "exclusive")(binary - 5)
        val (left, afterLeft) = randomFormula(depth - 1, binders, afterChoice)
        val (right, afterRight) = randomFormula(depth - 1, binders, afterLeft)
        (QuantifiedFormula.Node(name, Vector(left, right)), afterRight)

  /** `binder_surface(Binder, Binders, Surface)`: the surface term built from
    * the library's connectives, Binders the variables of the enclosing binders,
    * the innermost first.
    */
  private def binderSurface(
      binder: QuantifiedFormula.Binder,
      binders: List[Term]
  ): Term =
    λ(variable => formulaSurface(binder.body, variable :: binders))

  private def formulaSurface(
      formula: QuantifiedFormula,
      binders: List[Term]
  ): Term = formula match
    case QuantifiedFormula.Bound(index)            => binders(index)
    case QuantifiedFormula.Node("true", Vector())  => value(true)
    case QuantifiedFormula.Node("false", Vector()) => value(false)
    case QuantifiedFormula.Node(
          "every_assignment",
          Vector(binder: QuantifiedFormula.Binder)
        ) =>
      function("every_assignment")(binderSurface(binder, binders))
    case QuantifiedFormula.Node(name, operands)
        if Set("not", "and", "or", "exclusive").contains(name) =>
      operands.foldLeft(function(name))((applied, operand) =>
        applied(formulaSurface(operand, binders))
      )
    case other => fail(s"not a formula of the circuit grammar: $other")

  // The native reference of every_assignment agrees with the definition on
  // 80 random quantified formulas, read as the circuit grammar decodes them.
  test("everyAssignmentReference") {
    (1 to 80).foldLeft(SplitMix(20261001))((random, _) =>
      val (formula, after) = randomFormula(3, 1, random)
      val binder: QuantifiedFormula.Binder = QuantifiedFormula.Binder(formula)
      val result = truthOf(reference("every_assignment", Quantified(binder)))
      expect(
        "every_assignment",
        Vector(binderSurface(binder, List.empty)),
        value(result)
      )
      after
    )
  }

  // An index past the argument's own binders reads nothing.
  test("everyAssignmentReferenceReadsOnlyItsBinders") {
    assertEquals(
      AttractorReferences.attractorReference(
        "every_assignment",
        Vector(Quantified(QuantifiedFormula.Binder(QuantifiedFormula.Bound(1))))
      ),
      None
    )
  }
