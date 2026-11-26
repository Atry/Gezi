package gezi.rewritetrace

import gezi.frontend.Defunctionalization
import gezi.frontend.FreeNames
import gezi.frontend.Lambdalattice
import gezi.frontend.LambdalatticeLayout
import gezi.frontend.NameSpelling
import gezi.frontend.ReadableText
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Literal
import gezi.ir.Instruction
import gezi.ir.Opaque
import gezi.ir.UriNode
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.knowledgereading.Reading
import gezi.locations.BinderOrigin
import gezi.locations.SourceMap
import gezi.weakhead.Value

/** The term a trace's first round starts from, read with its source map: the
  * locations of its places in its text and the origin of each binder
  * (`gezi.locations.BinderOrigin`); and the instructions the text's bindings
  * name for display, each with its name (`TraceStart.written` with `known`),
  * a name the printer synthesized (`NameSpelling.shared`) left out.
  */
final case class LocatedStart(start: Instruction, map: SourceMap, names: Map[Instruction, String])

/** The text of the term a trace starts from. A trace holds no start: the
  * start is a program the front end reads with its locations, written beside the
  * trace's text, in the trace's files and in the player's page, so that a
  * replay is given it.
  *
  * The text is Scott data read as a trace's text is read
  * (`gezi.knowledgereading.KnowledgeReading`), `λstart. start BINDINGS
  * TERM`: TERM the start printed with names and sharing
  * (`gezi.frontend.ReadableText`), which the player's page embeds beside the trace,
  * whose text is linear in the start's distinct instructions where a tree
  * is exponential in the depth of its diamonds, and BINDINGS the number of
  * shared instructions the printer bound at TERM's start, `(λt. t V) λm.
  * BODY`, as a trie of its integer. The reader contracts that many bindings,
  * two β steps each (the printer's law: the printed text, read back by the
  * front end with its lets contracted, is the IR it was printed from):
  * a program's own text may begin with a binding of that shape, as an
  * import of the library does, so the reader is told how many are the
  * printer's. The text is laid out in the multi-line CPS layout of
  * CONTRIBUTING.md, "lambdalattice layout: no right-associative parentheses, CPS one step per line" (`ReadableText.Printed.brokenText`, `LambdalatticeLayout`
  * with `ParameterLists.Prefixed`), TERM on one line when it is no wider
  * than `ReadableText.lineWidth`.
  */
object TraceStart:

  /** The text of the start, its binders named from the program's source
    * when the source is given (the front end's reading of it, with its
    * locations), else printed nameless (`ReadableText.printedNameless`).
    * Throws `TraceTextError` when the front end reads the source as another
    * instruction than the start, or the text back as another.
    */
  def written(start: Instruction, source: Option[String]): String = written(start, source, Map.empty)

  /** `written`, each instruction of `known` bound at TERM's start and named
    * by its name there (`ReadableText.KnownNames.Bound`): the library
    * terms a trace's lemmas name (`TraceText.namesUsed`), so that the start
    * reads as the player shows the steps.
    */
  def written(start: Instruction, source: Option[String], known: Map[Instruction, String]): String =
    val printed = source match
      case Some(text) =>
        val read = Lambdalattice.located(text, FreeNames.Rejected)
        val (instruction, map) = Defunctionalization.locatedThunkInstruction(read.term, read.spans, sourceUri)
        if !(instruction eq start) then
          throw TraceTextError(s"the front end reads the source of the start as $instruction, not as the start $start")
        ReadableText.printed(instruction, map, ReadableText.KnownNames.Bound(known))
      case None => ReadableText.printedNameless(start, ReadableText.KnownNames.Bound(known))
    val broken = printed.brokenText(ReadableText.lineWidth)
    val closing = if broken.contains('\n') then "\n)" else ")"
    val leaves = opaqueLeaves(start)
    val leafBindings = leaves.map(leaf => s"(λt. t ${leafLiteralText(leaf)}) λ${NameSpelling.escaped(leafName(leaf))}.\n").mkString
    val text = LambdalatticeLayout
      .laidOut(
        Lambdalattice.lexemes(s"λstart\n. start (λk. k ${leaves.size + printed.bindings})\n($leafBindings$broken$closing"),
        LambdalatticeLayout.ParameterLists.Prefixed
      )
      .stripTrailing
    val again = readLocated(text, sourceUri).start
    if !(again eq start) then throw TraceTextError(s"the text of the start $start reads back as $again")
    text

  /** The opaque instructions of the start, URI nodes and opaque terms, each
    * once, in the order a walk first meets them. The surface syntax spells
    * neither, and the printer writes each as a name it binds nowhere
    * (`ReadableText`, SHARING), the name `leafName` gives escaped; `written`
    * binds each such name at TERM's start to a literal that says which
    * instruction it is (`leafLiteralText`), which the reader turns back into
    * the instruction (`leafContracted`), so that the text stays a closed term
    * with no free name.
    */
  private def opaqueLeaves(start: Instruction): Vector[Instruction] =
    @scala.annotation.tailrec
    def walked(pending: List[Instruction], visited: Set[Instruction], found: Vector[Instruction]): Vector[Instruction] =
      pending match
        case Nil                                    => found
        case next :: rest if visited.contains(next) => walked(rest, visited, found)
        case next :: rest if next.opaque            => walked(rest, visited + next, found :+ next)
        case next :: rest                           => walked(next.layer.children.toList ++ rest, visited + next, found)
    val leaves = walked(List(start), Set.empty, Vector.empty)
    val names = leaves.map(leaf => NameSpelling.escaped(leafName(leaf)))
    if names.distinct.size != names.size then
      throw TraceTextError(s"two opaque instructions of the start are written as one name: ${names.diff(names.distinct)}")
    leaves

  /** The text the printer names an opaque instruction by: an opaque term's
    * name, a URI node's URI (`ReadableText`'s names of constants).
    */
  private def leafName(leaf: Instruction): String = leaf.layer match
    case Opaque(name) => name
    case UriNode(uri) => uri.toString
    case other        => throw IllegalStateException(s"no opaque instruction: $other")

  /** The literal that says which opaque instruction a leaf is, in CBOR's
    * diagnostic notation: an opaque term's name as a text string, a URI
    * node's URI as a text string under tag 32, the tag RFC 8949 gives a URI
    * (section 3.4.5.3), in parentheses, where a number touching `(` is a tag.
    */
  private def leafLiteralText(leaf: Instruction): String = leaf.layer match
    case Opaque(name) => textNotation(name)
    case UriNode(uri) => s"(32(${textNotation(uri.toString)}))"
    case other        => throw IllegalStateException(s"no opaque instruction: $other")

  /** The text string's notation: the text in double quotes, a double quote,
    * a backslash and a control character escaped. `written` reads its text
    * back and throws if it reads another instruction.
    */
  private def textNotation(text: String): String =
    text
      .map {
        case '"'                         => "\\\""
        case '\\'                        => "\\\\"
        case character if character < ' ' => f"\\u${character.toInt}%04x"
        case character                   => character.toString
      }
      .mkString("\"", "", "\"")

  /** The opaque instruction a literal of `leafLiteralText` says: a text
    * string under tag 32 a URI node of the text, a text string an opaque
    * term of the name. Throws `TraceTextError` for any other literal.
    */
  private def leafOfLiteral(literal: Literal): Instruction =
    val bytes = literal.bytes.toVector
    def textOf(textBytes: Vector[Byte]): String =
      Literal.textRead(Literal(IArray.from(textBytes))).fold(reason => throw TraceTextError(s"a leaf's literal holds no text: $reason"), identity)
    bytes match
      case uriTagFirst +: uriTagSecond +: rest if uriTagFirst == 0xd8.toByte && uriTagSecond == 32.toByte =>
        Instruction.uri(java.net.URI(textOf(rest)))
      case _ => Instruction.opaque(textOf(bytes))

  /** The URI the places of a source of the start are located under while
    * it is printed; the printed text's own places are located when read.
    */
  private val sourceUri: java.net.URI = java.net.URI("trace:source")

  /** The start the text reads as, its bindings contracted, with its source
    * map: the locations of its places, spans of the text under the URI, and
    * its binders' origins, the names the text writes. Throws the front end's
    * errors for a text that is no closed term, `KnowledgeReadingError` for a
    * text of another shape, and `TraceTextError` for a TERM with fewer
    * bindings than BINDINGS.
    */
  def readLocated(text: String, uri: java.net.URI): LocatedStart =
    val read = Lambdalattice.located(text, FreeNames.Rejected)
    val (whole, wholeMap) = Defunctionalization.locatedThunkInstruction(read.term, read.spans, uri)
    val (bindings, term) = KnowledgeReading.run(startRead(whole), readingLimit)
    val termMap = whole match
      case Instruction.Thunk(_, _, fillings) =>
        fillings.indexWhere(_ eq term) match
          case -1    => throw TraceTextError(s"the term of the start is no filling of the text's thunk $whole")
          case index => wholeMap.children.lift(index).getOrElse(SourceMap.unlocated)
      case other => throw TraceTextError(s"the text of a start reads as no thunk: $other")
    (1 to bindings).foldLeft(LocatedStart(term, termMap, Map.empty))((located, _) => contracted(located))

  /** The evaluator steps reading the tuple takes at most: reading it opens
    * the tuple and the trie of BINDINGS and never TERM, so the steps grow
    * with BINDINGS' CBOR bytes alone. Measured 2026-11-19 (a scratch probe,
    * the fewest steps that read the tuple): 41 for BINDINGS 0, 46 for 3 and
    * for 23 (one byte), 70 for 24 (two bytes), 94 for 1000 (three bytes),
    * whatever TERM; 24 steps more for each byte. An Int's CBOR head is at
    * most 5 bytes: 46 + 4 × 24.
    */
  private val readingLimit: Long = 46L + 4L * 24L

  /** BINDINGS and TERM of the text's tuple. */
  private def startRead(value: Value): Reading[(Int, Instruction)] =
    KnowledgeReading.fields(value, 2).flatMap {
      case Vector(bindings, term) =>
        KnowledgeReading.trieInteger(bindings).map(count =>
          if count.isValidInt && count >= 0 then (count.toInt, KnowledgeReading.term(term, Set.empty))
          else throw KnowledgeReadingError(s"the number of a start's bindings $count is no natural Int")
        )
      case other => throw KnowledgeReadingError(s"a tuple of two has ${other.size} fields")
    }

  /** The value of the binding at the start's root, `(λt. t V) λm. BODY`,
    * with the name m is written with, when it is no name the printer
    * synthesized.
    */
  private def bindingName(located: LocatedStart): Option[(Instruction, String)] =
    located.start match
      case Instruction.Apply(Instruction.Thunk(_, Vector(_), Vector(value)), Instruction.Thunk(_, _, _)) =>
        located.map.children
          .lift(1)
          .flatMap(_.binders.headOption)
          .flatMap(_.collectFirst { case BinderOrigin.Written(name, _) => name })
          .filterNot(NameSpelling.sharedParts(_).nonEmpty)
          .map(value -> _)
      case _ => None

  /** The binding at the start's root contracted with its map: a binding of
    * a shared instruction (`ReadableText.contracted`), or else of an opaque
    * leaf (`leafContracted`). Throws `TraceTextError` for a root of another
    * shape.
    */
  private def contracted(located: LocatedStart): LocatedStart =
    ReadableText.contracted(located.start, located.map) match
      case Some((start, map)) => LocatedStart(start, map, located.names ++ bindingName(located))
      case None               => leafContracted(located)

  /** The binding of an opaque leaf at the start's root, `(λt. t LITERAL) λm.
    * BODY` (`opaqueLeaves`), contracted: BODY with the instruction the
    * literal says (`leafOfLiteral`) in place of m, as a shared binding is
    * contracted with its value. The helper of a shared binding applies t to
    * one value, that of a leaf to the bits of a literal, which the printer
    * never shares (`ReadableText`, SHARING), so the two do not meet. Throws
    * `TraceTextError` for a root of another shape.
    */
  private def leafContracted(located: LocatedStart): LocatedStart =
    located.start match
      case Instruction.Apply(helper @ Instruction.Thunk(_, Vector(_), _), body @ Instruction.Thunk(_, _ +: _, _)) =>
        val bits = Defunctionalization.instructionTerm(helper) match
          case DeBruijnTerm.Lambda(applied) => argumentCount(applied, 0)
          case other                         => throw TraceTextError(s"a leaf's helper is no abstraction: $other")
        val literal = KnowledgeReading.run(KnowledgeReading.trieLiteralWritten(helper), leafReadingLimit(bits)) match
          case Some(read) => read
          case None       => throw TraceTextError(s"the start's root is no binding (λt. t V) λm. BODY: ${located.start}")
        val leaf = leafOfLiteral(literal)
        val leafHelper =
          Defunctionalization.thunkInstruction(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Constant(leaf))))
        val map = located.map.copy(children = located.map.children.updated(0, SourceMap.unlocated))
        ReadableText.contracted(Instruction.Apply(leafHelper, body), map) match
          case Some((start, contractedMap)) => LocatedStart(start, contractedMap, located.names)
          case None => throw TraceTextError(s"the binding of the leaf $leaf does not contract: ${located.start}")
      case _ => throw TraceTextError(s"the start's root is no binding (λt. t V) λm. BODY: ${located.start}")

  /** The evaluator steps reading a leaf's literal of the bits takes at most:
    * `readingLimit`'s 46 steps of a tuple and 24 for each byte of a trie
    * (measured 2026-11-19 on BINDINGS' tries), 3 for each bit.
    */
  private def leafReadingLimit(bits: Int): Long = 46L + 3L * bits

  /** The arguments of the term's application spine. */
  @scala.annotation.tailrec
  private def argumentCount(term: DeBruijnTerm, counted: Int): Int = term match
    case DeBruijnTerm.Apply(function, _) => argumentCount(function, counted + 1)
    case _                               => counted
