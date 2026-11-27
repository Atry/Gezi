package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import io.bullet.borer.Dom
import io.bullet.borer.Tag
import java.nio.charset.StandardCharsets
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.SeededSnapshots
import gezi.ir
import gezi.ir.Code
import gezi.ir.Configured
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.StorageAccess
import gezi.locations.BinderOrigin
import gezi.locations.Location
import gezi.locations.SourceMap
import gezi.locations.Span
import snapshot4s.generated.snapshotConfig

/** The laws of `ReadableText` on generated closed terms, some holding
  * library names and some built with diamonds so that a closed part is
  * written twice:
  *
  *   - the text reads back as the term once its bindings of shared parts are
  *     contracted (two β steps each);
  *   - no application's last argument stands in parentheses unless it is a
  *     chain of + and ∥;
  *   - the text of a tower of diamonds grows with its height, not with the
  *     size of the tree it unfolds to;
  *   - a term holding the bits of literals as arguments and the variable
  *     arguments partial functions of literals reads back as the term too,
  *     and a snapshot records what such terms print as;
  *   - the printed text, read with its locations and printed again, is the
  *     same text: the names its binders' origins give are the names it
  *     writes (the law of reading back);
  *   - the name of a literal's bit is a name, and a snapshot records such
  *     names;
  *   - the readback at each place the printer marks a subterm at is the
  *     subterm's readback, and a snapshot records where the marks stand.
  *
  * Purpose: catch a name that captures another binder or a constant, a
  * binding placed before a binding it refers to, a sharing that drops or
  * duplicates a part, parentheses where the printer's layout writes `λ.` or a
  * bare λ, a printer that writes a shared part as often as the tree holds
  * it, and a literal written back with other bytes, another split of its
  * bits, or a body that reads the bits' binders; a binder named other than
  * its origin says, and a literal's bit named by no name.
  */
class ReadableTextLawTest extends GeneratedProperties with SeededSnapshots:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private type NoFactsTerm = Configured[NoFacts.type]

  private val libraryName: NoFactsTerm = NoFacts.opaque("library_name")

  private val uri: java.net.URI = java.net.URI.create("file:///generated.lambdalattice")

  /** A map of the instruction that gives each binder one written origin,
    * its name one of few chosen by the binder's place in the map, so that
    * names clash with one another and with the helper's `t`.
    */
  private def namedMap(instruction: NoFactsTerm): SourceMap =
    def origins(path: Vector[Int], count: Int): Vector[Set[BinderOrigin]] =
      Vector.tabulate(count)(position =>
        Set(BinderOrigin.Written(Vector("x", "y", "t", "f")(Math.floorMod((path :+ position).hashCode, 4)), Location.Source(uri, Span(0, 0))))
      )
    def codeMap(code: Code, path: Vector[Int]): SourceMap = code.layer match
      case ir.Slot(_)               => SourceMap.unlocated
      case ir.Apply(function, argument) => pair(Vector(codeMap(function, path :+ 0), codeMap(argument, path :+ 1)))
      case ir.Choice(left, right)   => pair(Vector(codeMap(left, path :+ 0), codeMap(right, path :+ 1)))
      case ir.Parallel(left, right) => pair(Vector(codeMap(left, path :+ 0), codeMap(right, path :+ 1)))
      case ir.Thunk(inner, holes, fillings) =>
        SourceMap(
          Set.empty,
          Some(codeMap(inner, path :+ -1)),
          fillings.zipWithIndex.map((filling, index) => codeMap(filling, path :+ index)),
          origins(path, holes.size)
        )
    def instructionMap(at: NoFactsTerm, path: Vector[Int]): SourceMap = at.layer match
      case ir.Apply(function, argument) => pair(Vector(instructionMap(function, path :+ 0), instructionMap(argument, path :+ 1)))
      case ir.Choice(left, right)       => pair(Vector(instructionMap(left, path :+ 0), instructionMap(right, path :+ 1)))
      case ir.Parallel(left, right)     => pair(Vector(instructionMap(left, path :+ 0), instructionMap(right, path :+ 1)))
      case ir.Thunk(code, holes, fillings) =>
        SourceMap(
          Set.empty,
          Some(codeMap(code, path :+ -1)),
          fillings.zipWithIndex.map((filling, index) => instructionMap(filling, path :+ index)),
          origins(path, holes.size)
        )
      case _ => SourceMap.unlocated
    def pair(children: Vector[SourceMap]): SourceMap = SourceMap(Set.empty, None, children, Vector.empty)
    instructionMap(instruction, Vector.empty)

  /** The term printed, its binders named by `namedMap`. */
  private def printedNamed(instruction: NoFactsTerm): ReadableText.Printed[NoFacts.type] =
    ReadableText.printed(instruction, namedMap(instruction))

  /** A closed term over the constants, written twice in a diamond when
    * `diamond` holds: `λf. f c c`.
    */
  private def instructionsOver(constants: Vector[TermOf[NoFactsTerm]]): Gen[NoFactsTerm] =
    for
      term <- HoasGenerators.closedTermOver(constants)
      diamond <- Gen.boolean
    yield
      val written = if diamond then Term.Abstraction(function => function(term)(term)) else term
      Defunctionalization.thunkInstruction[NoFacts.type](written.deBruijnTerm(Map.empty))

  /** A closed term over the library name, in a diamond or not. */
  private val instructions: Gen[NoFactsTerm] = instructionsOver(Vector(Term.closed(libraryName)))

  /** The instruction the text reads back to, its bindings contracted. */
  private def readBack(printed: ReadableText.Printed[NoFacts.type]): NoFactsTerm = readBack(printed, printed.text)

  /** The instruction a text of the printed term reads back to, its
    * bindings contracted.
    */
  private def readBack(printed: ReadableText.Printed[NoFacts.type], text: String): NoFactsTerm =
    val read = Defunctionalization.thunkInstruction[NoFacts.type](
      Lambdalattice.term(text, FreeNames.Allowed),
      Map("library_name" -> libraryName)
    )
    (1 to printed.bindings).foldLeft(read)((term, _) =>
      term.layer match
        case ir.Apply(helper, rest) =>
          Defunctionalization.instructionTerm(helper) match
            case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value)) =>
              Defunctionalization.bodyInstantiated(rest, Defunctionalization.thunkInstruction[NoFacts.type](value))
            case other => throw AssertionError(s"a binding's helper is no λt. t V: $other")
        case other => throw AssertionError(s"a binding is no application: $other")
    )

  property("the text reads back as the term once its bindings are contracted") {
    instructions.forAllWithLog(instruction => printedNamed(instruction).text).map(instruction =>
      val printed = printedNamed(instruction)
      Result.diff(readBack(printed), instruction)(Configured.same(_, _)).log(printed.text)
    )
  }

  /** Purpose: catch an inlined shared instruction
    * that the text
    * still binds, or whose writing in place reads back as another term: of
    * the shared instructions the term binds, a generated subset printed
    * inlined reads back as the term, and none of them is bound.
    */
  property("the text with a subset of its shared instructions inlined reads back as the term and binds none of them") {
    for
      instruction <- instructions.forAllWithLog(instruction => printedNamed(instruction).text)
      selection <- Gen.int(Range.linear(0, Int.MaxValue)).forAll
    yield
      val map = namedMap(instruction)
      val plain = ReadableText.printed(instruction, map, ReadableText.KnownNames.Bound(Map.empty))
      val inlined = plain.sharedValues.zipWithIndex.collect {
        case (value, index) if ((selection >> (index % 31)) & 1) == 1 => value.instruction
      }.toSet
      val printed = ReadableText.printed(instruction, map, ReadableText.KnownNames.Bound(Map.empty), inlined)
      Result.all(
        List(
          Result.diff(readBack(printed), instruction)(Configured.same(_, _)).log(printed.text),
          Result.assert(printed.sharedValues.forall(value => !inlined.contains(value.instruction))).log(s"bound: ${printed.text}")
        )
      )
  }

  /** Purpose: catch a line break of the multi-line CPS layout
    * (`Printed.laidOut`) where the reader reads another term,
    * and a laid-out text the formatter would write otherwise, on widths
    * narrow enough that most generated terms span lines.
    */
  property("the text laid out on lines reads back as the term, and laying it out again changes nothing") {
    val widths = Gen.int(hedgehog.Range.linear(4, 40))
    (for
      instruction <- Gen.choice1(instructions, literalInstructionsOver(Vector.empty))
      width <- widths
    yield (instruction, width)).forAllWithLog((instruction, width) => printedNamed(instruction).laidOut(width)).map((instruction, width) =>
      val printed = printedNamed(instruction)
      val laidOut = printed.laidOut(width)
      val again = LambdalatticeLayout.laidOut(Lambdalattice.lexemes(laidOut), LambdalatticeLayout.ParameterLists.Prefixed).stripTrailing
      Result.all(
        List(
          Result.diff(readBack(printed, laidOut), instruction)(Configured.same(_, _)),
          Result.diff(again, laidOut)(_ == _).log("laid out again")
        )
      ).log(laidOut)
    )
  }

  /** Purpose: show, as a diff, the lines the printer writes a text on
    * (`Printed.laidOut`), an output as complex as the printer and the layout.
    */
  test("texts laid out on lines") {
    assertSeededSnapshot(instructions, 20261119L, 12, "readable-text/laid-out.txt")(
      instruction => printedNamed(instruction).text,
      identity[String]
    )(instruction => printedNamed(instruction).laidOut(24))
  }

  /** A data item for a literal: integers of every size, floating point
    * values, text and byte strings, simple values, which no literal starts
    * with alone, and arrays, maps and tags of them.
    */
  private def element(depth: Int): Gen[Dom.Element] =
    val leaf = Gen.choice1(
      Gen.long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue)).map(value => Literal.integerElement(BigInt(value))),
      Gen.long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .map(value => Literal.integerElement(BigInt(value) * (BigInt(1) << 64))),
      Gen.double(Range.linearFracFrom(0, -1e6, 1e6)).map(DiagnosticNotation.floatingElement),
      Gen.string(Gen.frequency1(4 -> Gen.char('a', 'z'), 1 -> Gen.element1('"', '\\', '\n', 'λ', '\u0000')), Range.linear(0, 6))
        .map(Dom.StringElem(_)),
      Gen.string(Gen.char('\u0000', '\u00ff'), Range.linear(0, 4))
        .map(text => Dom.ByteArrayElem(text.getBytes(StandardCharsets.ISO_8859_1))),
      Gen.element1(Dom.BooleanElem(true), Dom.NullElem, Dom.UndefinedElem)
    )
    if depth == 0 then leaf
    else
      Gen.frequency1(
        4 -> leaf,
        1 -> Gen.list(element(depth - 1), Range.linear(0, 3)).map(items => Dom.ArrayElem.Sized(items.toVector)),
        1 -> Gen.list(element(depth - 1), Range.linear(0, 3)).map(items => Dom.ArrayElem.Unsized(items.toVector)),
        1 -> Gen.list(element(depth - 1), Range.linear(0, 2)).map(keys =>
          Dom.MapElem.Sized[Dom.Element](keys.zipWithIndex.map((key, index) => key -> Literal.integerElement(index))*)
        ),
        1 -> element(depth - 1).map(Dom.TaggedElem(Tag.Other(30), _))
      )

  private val literal: Gen[Literal] = element(2).map(Literal.of)

  /** Where literals stand in a generated term: the literals spread as
    * arguments of the head, the literals the partial functions around it
    * bind, whether the head is the variable an abstraction outside them
    * binds, and a literal whose partial function's body reads the binder
    * of its bit at the index, given as one more argument.
    */
  private final case class LiteralUse(
      arguments: List[Literal],
      binders: List[Literal],
      headOutside: Boolean,
      bitRead: Option[(Literal, Int)]
  ):
    def text: String =
      s"arguments ${arguments.mkString(" ")}; binders ${binders.mkString(" ")}; head outside $headOutside; " +
        s"bit read ${bitRead.fold("none")((literal, index) => s"$literal at $index")}"

  private val literalUses: Gen[LiteralUse] =
    for
      arguments <- Gen.list(literal, Range.linear(0, 2))
      binders <- Gen.list(literal, Range.linear(0, 2))
      headOutside <- Gen.boolean
      bitRead <- Gen.frequency1(
        3 -> Gen.constant(None),
        1 -> literal.flatMap(read => Gen.int(Range.constant(0, 8 * read.bytes.length - 1)).map(index => Some((read, index))))
      )
    yield LiteralUse(arguments, binders, headOutside, bitRead)

  /** The chain of a literal's partial function, as `Literals.partialFunction`
    * writes it, whose body is the variable of the index under the bits'
    * binders, one of them: no literal binder.
    */
  private def bitReading(read: Literal, index: Int): DeBruijnTerm =
    Literals.arguments(read).foldRight(DeBruijnTerm.Variable(index): DeBruijnTerm)((bit, rest) =>
      val isOne = bit eq Literals.one
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), if isOne then rest else Literals.top), if isOne then Literals.top else rest)
      )
    )

  /** The term of the use over the closed head. */
  private def literalTerm(use: LiteralUse, head: DeBruijnTermOf[NoFactsTerm]): DeBruijnTermOf[NoFactsTerm] =
    val applied = (use.arguments.flatMap(Literals.arguments) ++ use.bitRead.map(bitReading))
      .foldLeft(if use.headOutside then DeBruijnTerm.Variable(0) else head)(DeBruijnTerm.Apply(_, _))
    val bound = use.binders.foldRight(applied)(Literals.partialFunction)
    if use.headOutside then DeBruijnTerm.Lambda(bound) else bound

  private def literalInstructionsOver(constants: Vector[TermOf[NoFactsTerm]]): Gen[NoFactsTerm] =
    for
      use <- literalUses
      head <- HoasGenerators.closedTermOver(constants)
      diamond <- Gen.boolean
    yield
      val term = literalTerm(use, head.deBruijnTerm(Map.empty))
      Defunctionalization.thunkInstruction[NoFacts.type](
        if diamond then DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), term), term)) else term
      )

  private val literalInstructions: Gen[NoFactsTerm] = literalInstructionsOver(Vector(Term.closed(libraryName)))

  property("a term with literals reads back as the term once its bindings are contracted") {
    literalInstructions.forAllWithLog(instruction => printedNamed(instruction).text).map(instruction =>
      val printed = printedNamed(instruction)
      Result.diff(readBack(printed), instruction)(Configured.same(_, _)).log(printed.text)
    )
  }

  /** Purpose: show what literals print as, bare or in parentheses, as
    * arguments and as binders, and which bits stay terms.
    */
  test("the text of terms with literals") {
    assertSeededSnapshot(literalUses, 20261119L, 40, "readable-text/literals.txt")(_.text, identity[String])(use =>
      printedNamed(Defunctionalization.thunkInstruction[NoFacts.type](literalTerm(use, Term.closed(libraryName).deBruijnTerm(Map.empty)))).text
    )
  }

  /** The printed structure as a tree. */
  private enum Tree:
    case Token(text: String)
    case Branch(node: ReadableText.Node, children: Vector[Tree])

  private def tree(pieces: Vector[ReadableText.Piece]): Tree =
    val (stack, _) = pieces.foldLeft((List((ReadableText.Node.Spine, Vector.empty[Tree])), ())) {
      case ((stack, _), ReadableText.Piece.Token(text)) =>
        val (node, children) :: rest = stack: @unchecked
        ((node, children :+ Tree.Token(text)) :: rest, ())
      case ((stack, _), ReadableText.Piece.Open(node)) => ((node, Vector.empty) :: stack, ())
      case ((stack, _), ReadableText.Piece.At(_, _))   => (stack, ())
      case ((stack, _), ReadableText.Piece.Source(_))  => (stack, ())
      case ((stack, _), ReadableText.Piece.Close) =>
        val (node, children) :: (parent, siblings) :: rest = stack: @unchecked
        ((parent, siblings :+ Tree.Branch(node, children)) :: rest, ())
    }
    val List((root, children)) = stack: @unchecked
    Tree.Branch(root, children)

  /** The places where a last argument stands in parentheses around anything
    * but a chain: the last expression of a spine whose last part is a
    * parenthesized term holding no chain.
    */
  private def rightAssociativeParentheses(tree: Tree): Vector[String] = tree match
    case Tree.Token(_) => Vector.empty
    case Tree.Branch(node, children) =>
      val here = node match
        case ReadableText.Node.Spine =>
          children.collect { case branch: Tree.Branch => branch }.lastOption match
            case Some(Tree.Branch(ReadableText.Node.Expression, parts)) =>
              parts.collect { case branch: Tree.Branch => branch }.lastOption match
                case Some(Tree.Branch(ReadableText.Node.Parenthesized, inner)) =>
                  val holdsChain = inner.exists {
                    case Tree.Branch(ReadableText.Node.Chain, _) => true
                    case _                                       => false
                  }
                  if holdsChain then Vector.empty else Vector(written(Tree.Branch(node, children)))
                case _ => Vector.empty
            case _ => Vector.empty
        case _ => Vector.empty
      here ++ children.flatMap(rightAssociativeParentheses)

  private def written(tree: Tree): String = tree match
    case Tree.Token(text)          => text
    case Tree.Branch(_, children) => children.map(written).mkString

  property("no last argument stands in parentheses unless it is a chain") {
    instructions.forAllWithLog(instruction => printedNamed(instruction).text).map(instruction =>
      val printed = printedNamed(instruction)
      val found = rightAssociativeParentheses(tree(printed.pieces))
      Result.assert(found.isEmpty).log(found.mkString("\n"))
    )
  }

  /** Purpose: show that a tower of diamonds `λf. f d d`, each level writing
    * the level below twice, prints in a length that grows with the height
    * and not as the 2^height leaves of its tree.
    */
  test("the length of the text of a tower of diamonds") {
    val leaf = Term.Abstraction(x => x)
    val lines = (1 to 12).map(height =>
      val tower = (1 to height).foldLeft(leaf)((below, _) => Term.Abstraction(function => function(below)(below)))
      val printed = printedNamed(Defunctionalization.thunkInstruction[NoFacts.type](tower.deBruijnTerm(Map.empty)))
      s"height $height: ${printed.bindings} bindings, ${printed.text.length} characters"
    )
    assertFileSnapshot(lines.mkString("\n") + "\n", "readable-text/diamond-towers.txt")
  }

  /** Purpose: show that a tower of diamonds `λf. f λy. f y d d` whose level
    * below, `d`, reaches the code that writes it twice through an inner
    * thunk, the abstraction over `y`, which reads `f` and so is no closed
    * instruction of its own, as one filling of that thunk, prints in a
    * length that grows with the height, as the tower of `λf. f d d` does.
    */
  test("the length of the text of a tower of diamonds inside an inner thunk") {
    val leaf = Term.Abstraction(x => x)
    val lines = (1 to 12).map(height =>
      val tower = (1 to height).foldLeft(leaf)((below, _) => Term.Abstraction(function => function(Term.Abstraction(inner => function(inner)(below)(below)))))
      val printed = printedNamed(Defunctionalization.thunkInstruction[NoFacts.type](tower.deBruijnTerm(Map.empty)))
      s"height $height: ${printed.bindings} bindings, ${printed.text.length} characters"
    )
    assertFileSnapshot(lines.mkString("\n") + "\n", "readable-text/inner-diamond-towers.txt")
  }

  property("the printed text, read with its locations and printed again, is the same text") {
    Gen.choice1(instructionsOver(Vector.empty), literalInstructionsOver(Vector.empty))
      .forAllWithLog(instruction => printedNamed(instruction).text)
      .map(instruction =>
        val text = printedNamed(instruction).text
        val read = Lambdalattice.located(text, FreeNames.Rejected)
        val (again, map) = Defunctionalization.locatedThunkInstruction[NoFacts.type](read.term, read.spans, uri)
        Result.diff(ReadableText.printed(again, map).text, text)(_ == _)
      )
  }

  private val literalBits: Gen[(Literal, Int)] =
    literal.flatMap(read => Gen.int(Range.constant(0, 8 * read.bytes.length - 1)).map((read, _)))

  property("the name of a literal's bit is a name") {
    literalBits.forAllWithLog((read, bit) => s"$read at $bit").map((read, bit) =>
      val name = LiteralWriting.bitName(read.bytes.toVector, bit)
      Result.assert(NameSpelling.isName(name)).log(name)
    )
  }

  /** Purpose: show the names literals' bits take, by the kinds of their
    * items.
    */
  test("the names of literals' bits") {
    assertSeededSnapshot(literalBits, 20261119L, 40, "readable-text/literal-bit-names.txt")(
      (read, bit) => s"$read at $bit",
      identity[String]
    )((read, bit) => LiteralWriting.bitName(read.bytes.toVector, bit))
  }

  /** The distinct instructions under the root, the root included. */
  private def subinstructions(root: NoFactsTerm): Vector[NoFactsTerm] =
    @scala.annotation.tailrec
    def walked(pending: List[NoFactsTerm], found: Vector[NoFactsTerm]): Vector[NoFactsTerm] = pending match
      case Nil                                       => found
      case current :: rest if found.exists(Configured.same(_, current)) => walked(rest, found)
      case current :: rest =>
        walked((if current.opaque then Nil else current.layer.children.toList) ++ rest, found :+ current)
    walked(List(root), Vector.empty)

  /** The subterm at the path, by the child positions of `DeBruijnTerm`. */
  private def readbackAt(term: DeBruijnTermOf[NoFactsTerm], path: Vector[Int]): DeBruijnTermOf[NoFactsTerm] =
    path.foldLeft(term)((current, index) =>
      (current, index) match
        case (DeBruijnTerm.Lambda(body), 0)            => body
        case (DeBruijnTerm.Apply(function, _), 0)      => function
        case (DeBruijnTerm.Apply(_, argument), 1)      => argument
        case (DeBruijnTerm.Choice(left, _), 0)         => left
        case (DeBruijnTerm.Choice(_, right), 1)        => right
        case (DeBruijnTerm.Parallel(left, _), 0)       => left
        case (DeBruijnTerm.Parallel(_, right), 1)      => right
        case _ => throw AssertionError(s"the readback $term has no subterm at $path")
    )

  /** The instruction at the path, by the indices of `Layer.children`. */
  private def instructionAt(root: NoFactsTerm, path: Vector[Int]): NoFactsTerm =
    path.foldLeft(root)((current, index) => current.layer.children(index))

  /** Purpose: catch a place (`ReadableText.placed`) at a node of the
    * readback that is not where the readback writes the subterm the place
    * names: a filling put at a read of another slot, the abstractions of a
    * thunk's holes or an inner thunk's not stepped over, or a stop walked
    * into. The readback of each subterm, every IR subterm closed, is the
    * node of the whole readback at each of its places, with the stops
    * chosen at random among the subterms.
    */
  property("the readback at each place of a subterm is the subterm's readback") {
    val withStops = for
      instruction <- instructions
      chosen <- Gen.boolean.list(Range.singleton(subinstructions(instruction).size))
    yield (instruction, subinstructions(instruction).zip(chosen).collect { case (stop, true) => stop }.toSet - instruction)
    withStops.forAllWithLog((instruction, stops) => s"$instruction, stops $stops").map((instruction, stops) =>
      val whole = Defunctionalization.instructionTerm(instruction, stops)
      // A stop is written as its constant, which `instructionTerm` of the stop alone expands.
      def readbackOf(subterm: NoFactsTerm): DeBruijnTermOf[NoFactsTerm] =
        if stops.contains(subterm) then DeBruijnTerm.Constant(subterm) else Defunctionalization.instructionTerm(subterm, stops)
      val wrong = ReadableText.placed(instruction, stops, None).entries.filterNot((readbackPath, place) =>
        readbackAt(whole, readbackPath) == readbackOf(instructionAt(instruction, place.path))
      )
      Result.assert(wrong.isEmpty).log(s"readback $whole, wrong places $wrong")
    )
  }

  /** Purpose: show where the printed text marks the places of the IR's
    * subterms (`ReadableText.Piece.At`), each mark written `⟦binding:path⟧`
    * for a node and `⟦binding:path…⟧` for the rest of a spine, so that a
    * reviewer sees a mark before the node it names and none inside a
    * literal.
    */
  test("the marks of the places of the subterms in the text") {
    assertSeededSnapshot(Gen.choice1(instructions, literalInstructionsOver(Vector.empty)), 20261119L, 20, "readable-text/places.txt")(
      instruction => printedNamed(instruction).text,
      identity[String]
    )(instruction =>
      printedNamed(instruction).pieces.collect {
        case ReadableText.Piece.Token(text)            => text
        case ReadableText.Piece.At(place, false)       => s"⟦${place.key}⟧"
        case ReadableText.Piece.At(place, true)        => s"⟦${place.key}…⟧"
      }.mkString
    )
  }
