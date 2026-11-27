package com.yang_bo.gezi.rewritetrace

import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.FreeNames
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.Respelling
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.NonEmptyHoles
import com.yang_bo.gezi.ir.Spine
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.ir.{Apply, Thunk}
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.knowledgereading.KnowledgeReadingError
import com.yang_bo.gezi.knowledgereading.Reading
import com.yang_bo.gezi.locations.BinderOrigin
import com.yang_bo.gezi.locations.LemmaText
import com.yang_bo.gezi.locations.Location
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.locations.Span
import com.yang_bo.gezi.weakhead.Computation
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** A trace read with where each of its lemmas is written
  * (`TraceText.readLocated`), none for a lemma the text writes as closed terms,
  * and the source maps of each lemma's two sides in the trace's text, whose
  * binders' origins are the names the text writes, so that a lemma is printed
  * with its own variable names (`com.yang_bo.gezi.frontend.ReadableText`); and the library
  * terms the lemmas' texts name, each with its name, as the β redex around the
  * trace binds them (`TraceText.namesUsed`), which a view prints by name
  * (`ReadableText.printed` with `known`).
  */
final case class LocatedTrace(
    trace: Trace[NoFacts.type],
    lemmaLocations: Vector[Option[LemmaLocation]],
    lemmaMaps: Vector[(SourceMap, SourceMap)],
    names: Map[Configured[NoFacts.type], String]
):
  require(
    lemmaLocations.size == trace.lemmas.size,
    s"${lemmaLocations.size} locations for ${trace.lemmas.size} lemmas"
  )
  require(
    lemmaMaps.size == trace.lemmas.size,
    s"${lemmaMaps.size} maps for ${trace.lemmas.size} lemmas"
  )

/** Where a trace's lemma is written: its knowledge file and the span, in the
  * file's code points, from its left side's start to its right side's end
  * (`TraceText.writtenWith`).
  */
final case class LemmaLocation(uri: java.net.URI, span: Span)

/** A term the text of a trace writes that its reader does not read back as the
  * same instruction: the front end spells it otherwise.
  */
final case class TraceTextError(reason: String) extends RuntimeException(reason)

/** The text of a trace: a closed lambdalattice term of Scott data, read under
  * the weak head as `KnowledgeReading` reads knowledge, with no semantics of
  * its own, so that a field is opened and never evaluated, and the terms a
  * trace holds keep their spelling.
  *
  * {{{
  * text         TRACE | (λn1. … λnk. TRACE) V1 … Vk
  *              the names the lemmas' texts use, each bound to its value Vi,
  *              a closed TERM, by a β redex of the data
  * TRACE        λt. t (list of LEMMA) (list of VALUE) (list of (list of COMMAND))
  *              a tuple of three; the term the first round starts from is
  *              no part of the trace (`TraceStart`)
  * LEMMA        λs. s LOCATION LEFT RIGHT
  *              LEFT and RIGHT the text the lemma's file writes, or closed TERMs
  * LOCATION     λnone. λsome. none | λnone. λsome. some (λl. l URI INTEGER INTEGER)
  *              the file and the span, in its code points, from the left
  *              side's start to the right side's end
  * URI          λk. k LITERAL, a trie of the URI's CBOR text string
  * VALUE        λv. v SOURCE (list of COMMAND) POSITION
  *              the subterm at POSITION of the term the commands make of
  *              the source's term (`TraceValue`)
  * SOURCE       of two alternatives: round INTEGER | value INTEGER
  *              the term before a round, or an earlier value
  * COMMAND      of four alternatives:
  *              rewrite REASON MOVE DIRECTION BINDINGS
  *            | convert CONVERSION MOVE DIRECTION BINDINGS
  *            | native MOVE TERM
  *            | abstraction MOVE INTEGER (λe1. … λen. list of COMMAND)
  *              the commands of the opened body, n the INTEGER, each ei
  *              standing for an eigenvariable (`Conversions.eigenvariables`)
  * REASON       of five alternatives: lemma INTEGER | equation INTEGER
  *            | fill OPTION | body OPTION | eta OPTION
  * OPTION       λnone. λsome. none | λnone. λsome. some SHAPE
  * SHAPE        λs. s GIVEN (list of HOLE)
  *              the code of the thunk GIVEN gives, and the holes (`ThunkShape`)
  * HOLE         of two alternatives: bound INTEGER | ignored
  * GIVEN        of two alternatives: value INTEGER | written TERM
  *              a value by its place, or (FIXME, `Given`) a term https://github.com/Atry/private-overlay/issues/1982
  * MOVE         λm. m INTEGER POSITION
  *              the command's position: the position of the command before
  *              it in its list (the root for the first) with INTEGER
  *              segments dropped from its end and POSITION's added
  * POSITION     a Scott list of SEGMENT
  * SEGMENT      of five alternatives: function | argument | left | right
  *            | filling INTEGER
  * DIRECTION    λforward. λbackward. forward | … backward
  * BINDINGS     a Scott list of λs. s INTEGER GIVEN
  * CONVERSION   of two alternatives: higher-order INTEGER SIDE INTEGER
  *            | root reverse β INTEGER
  * SIDE         λleft. λright. left | … right
  * INTEGER      λk. k LITERAL, a trie of the integer's CBOR literal
  * }}}
  *
  * A list is the library's Scott list written closed, nil `λn. λc. n` and a
  * cell `λn. λc. c ITEM REST`: a bracket is a CBOR array literal and no list of
  * terms. A constructor of k alternatives is `λh0. … λh(k−1). hi FIELD …`,
  * written here as text, its handlers named `h0` and up.
  *
  * A scalar of the trace's own data, an INTEGER, is a CBOR literal that the
  * host decodes (`KnowledgeReading.trieInteger`), not a Scott value the object
  * language decodes: the player is written in Scala.js, which decodes a scalar
  * into a Scala string or `Int`, so no lambdalattice decoding is needed. A TERM
  * is an object term, never a literal: the closed term of the instruction
  * (`Defunctionalization.instructionTerm`), written by the front end
  * (`Lambdalattice.closedText`; under openings `Lambdalattice.text`, each
  * eigenvariable named `e<depth>_<place>`), so that this module builds no de
  * Bruijn tree (CONTRIBUTING.md, "Types live only in the term": everything but
  * the front end works on the IR). Each lemma and each command is a line of its
  * own, so that a diff of two traces shows the commands that differ.
  */
object TraceText:

  /** The configuration a trace's text is read in: a text holds no storage, a
    * storage written as its view, and its reader is the player's, which knows
    * no facts.
    */
  private type Read = NoFacts.type

  private given Read = NoFacts

  /** The text of the trace. Throws `TraceTextError` when a term it holds is not
    * read back as the same instruction (`readBack`).
    */
  def written[C <: NativeSpecializer & Singleton](
      trace: Trace[C]
  )(using C, StorageAccess): String =
    writtenWith(trace, Map.empty[(Configured[C], Configured[C]), LemmaText[C]])

  /** The text of the trace with each lemma of `lemmaTexts`, keyed by its two
    * sides, written as its file writes it, with its location
    * (`com.yang_bo.gezi.locations.LemmaText`), a CBOR literal in the trace's file, since
    * writing the lemmas as lambdalattice keeps no debugging information but the
    * variable names: the names the lemmas' texts use are bound to their values
    * by one β redex around the trace, each name once. Throws `TraceTextError`
    * when two lemmas give one name two values, when a name is one the text's
    * own data binds, when a lemma's text reads as another term than its sides
    * (the two written as text, a storage as its view, since the text is read
    * with no facts), and as `written` throws.
    */
  def writtenWith[C <: NativeSpecializer & Singleton](
      trace: Trace[C],
      lemmaTexts: Map[(Configured[C], Configured[C]), LemmaText[C]]
  )(using
      C,
      StorageAccess
  ): String =
    val used =
      trace.lemmas.flatMap(lemma => lemmaTexts.get((lemma.left, lemma.right)))
    val names = namesUsed(trace, lemmaTexts)
    names
      .groupBy(_._1)
      .find(_._2.size > 1)
      .foreach((name, values) =>
        throw TraceTextError(
          s"the lemmas' texts give the name $name ${values.size} values"
        )
      )
    names
      .map(_._1)
      .find(dataName)
      .foreach(name =>
        throw TraceTextError(
          s"a lemma's text uses the name $name, which the trace's own data binds"
        )
      )
    val lemmas = trace.lemmas.map(lemma =>
      lemmaTexts.get((lemma.left, lemma.right)) match
        case None =>
          tupleText(
            Vector(
              constructorText(2, 0, Vector.empty),
              closedText(lemma.left),
              closedText(lemma.right)
            )
          )
        case Some(text) =>
          val location = tupleText(
            Vector(
              s"(λk. k ${textLiteral(text.uri.toString)})",
              integerText(text.left.start),
              integerText(text.right.end)
            )
          )
          tupleText(
            Vector(
              constructorText(2, 1, Vector(location)),
              s"(${text.leftText})",
              s"(${text.rightText})"
            )
          )
    )
    val values = trace.values.map(value =>
      tupleText(
        Vector(
          sourceText(value.from),
          inlineListText(
            commandsText(value.commands, 0, Map.empty[Configured[C], String])
          ),
          positionText(value.at)
        )
      )
    )
    val rounds = trace.rounds.map(round =>
      listText(commandsText(round, 0, Map.empty[Configured[C], String]), "    ")
    )
    val body =
      s"λtrace. trace\n  ${listText(lemmas, "  ")}\n  ${listText(values, "  ")}\n  ${listText(rounds, "  ")}\n"
    val written =
      if names.isEmpty then body
      else
        s"(${names.map((name, _) => s"λ$name. ").mkString}$body)\n" +
          names.map((_, value) => s"  ${closedText(value)}\n").mkString
    if used.nonEmpty then
      val read = TraceText.read(written, readingLimit(written))
      read.lemmas
        .zip(trace.lemmas)
        .find((again, lemma) =>
          Lambdalattice.closedText(again.left) != Lambdalattice
            .closedTextViewed(lemma.left) ||
            Lambdalattice.closedText(again.right) != Lambdalattice
              .closedTextViewed(lemma.right)
        )
        .foreach((again, lemma) =>
          throw TraceTextError(s"a lemma's text reads as $again, not as $lemma")
        )
    written

  /** The evaluator steps reading a trace's text may take: one per character,
    * and 32 more per character of a string literal. A reading opens the Scott
    * data of the trace, linear in the text: measured on 2026-11-13 at 0.06 to
    * 0.47 steps per character (strategies' `RewriteTraceLawTest`). The host
    * reads a literal bit by bit (`KnowledgeReading.trieText`): a lemma's
    * location of 82 characters of URI took 1,728 steps more than one of 11,
    * 24.3 per character of the literal (cores 4-7, 2026-11-17,
    * `TraceSourceMapsLawTest`), so 32 per character bounds it with a margin.
    */
  def readingLimit(text: String): Long =
    text.length.toLong + 32L * literalCharacters(text)

  /** The characters of a text inside double quotes, a backslash escaping the
    * character after it.
    */
  private def literalCharacters(text: String): Long =
    text
      .foldLeft((0L, false, false)) {
        case ((count, inside, escaped), character) =>
          if escaped then (count + 1, inside, false)
          else if inside && character == '\\' then (count + 1, inside, true)
          else if character == '"' then (count, !inside, false)
          else (if inside then count + 1 else count, inside, false)
      }
      ._1

  /** Whether a name is one the trace's data binds where a lemma's text stands
    * under it (`listText`, `constructorText`, `integerText` and the trace's own
    * abstraction), so that a lemma's text using it would read the data's
    * variable.
    */
  private def dataName(name: String): Boolean =
    Set("trace", "n", "c", "k").contains(name) || name.matches(
      "h[0-9]+"
    ) || name.matches("e[0-9]+_[0-9]+")

  /** The CBOR diagnostic notation of a text string: its code points in double
    * quotes, a quote and a backslash escaped.
    */
  private def textLiteral(text: String): String =
    "\"" + text.replace("\\", "\\\\").replace("\"", "\\\"") + "\""

  /** The trace of the text, read within the limit of evaluator steps. Throws
    * `KnowledgeReadingError` for a text of another shape or one the budget
    * stops.
    */
  def read(text: String, limit: Long): Trace[Read] =
    val value =
      Defunctionalization.thunkInstruction[Read](Lambdalattice.term(text))
    KnowledgeReading.run(traceRead(Value.of(value)), limit)

  /** The trace of the text, as `read` reads it, with where each of its lemmas
    * is written and the maps of its lemmas' sides: the text read with its
    * spans, the β redex that binds the names the lemmas' texts use contracted
    * with its map, and each side's map the map of its place in the data, the
    * first field of the trace, an item of that list, and the second and third
    * fields of the item (`fields`), where it stands as a closed filling, the
    * instruction the reader reads there. Throws as `read` throws, and
    * `TraceTextError` for data of another shape or a side the reader reads
    * otherwise than its place spells it.
    */
  //
  // A name the β redex binds, a library term a lemma's text uses (`konst` in `λa. λb. konst a b`), is a filling of
  // the contracted text, which a source map does not name; the names are read off the redex's binders
  // (`LocatedTrace.names`), and a view prints each value by its name.
  def readLocated(text: String, limit: Long): LocatedTrace =
    val read = Lambdalattice.located(text, FreeNames.Rejected)
    val (whole, wholeMap) = Defunctionalization
      .locatedThunkInstruction[Read](read.term, read.spans, traceUri)
    val (trace, lemmaLocations) =
      KnowledgeReading.run(locatedTraceRead(Value.of(whole)), limit)
    val (body, bodyMap, names) = namesContracted(whole, wholeMap)
    val Vector((lemmaList, lemmaListMap), _, _) =
      fields(body, bodyMap, 3): @unchecked
    val sides = listItems(lemmaList, lemmaListMap).map((lemma, lemmaMap) =>
      val Vector(_, (left, leftMap), (right, rightMap)) =
        fields(lemma, lemmaMap, 3): @unchecked
      val Vector(_, leftSpans, rightSpans) =
        fieldSpans(lemma, lemmaMap): @unchecked
      (
        (left, writtenWithin(leftMap, leftSpans)),
        (right, writtenWithin(rightMap, rightSpans))
      )
    )
    if sides.size != trace.lemmas.size then
      throw TraceTextError(
        s"the trace's text has ${sides.size} lemmas' sides for ${trace.lemmas.size} lemmas"
      )
    trace.lemmas.zip(sides).foreach { case (lemma, ((left, _), (right, _))) =>
      if !(Configured
          .same(left, lemma.left) && Configured.same(right, lemma.right))
      then
        throw TraceTextError(
          s"the lemma $lemma is read from the sides $left and $right of the trace's text"
        )
    }
    LocatedTrace(
      trace,
      lemmaLocations,
      sides.map((left, right) => (left._2, right._2)),
      names
    )

  /** The names the texts of the trace's lemmas use, each with its value, each
    * once: what `writtenWith` binds around the trace.
    */
  def namesUsed[C <: NativeSpecializer & Singleton](
      trace: Trace[C],
      lemmaTexts: Map[(Configured[C], Configured[C]), LemmaText[C]]
  )(using C): Vector[(String, Configured[C])] =
    trace.lemmas
      .flatMap(lemma => lemmaTexts.get((lemma.left, lemma.right)))
      .flatMap(_.names)
      .distinct

  /** The URI the places of a trace's text are located under. */
  private val traceUri: java.net.URI = java.net.URI("trace:trace")

  /** The text's instruction with the β redex `(λn1. … λnk. TRACE) V1 … Vk` that
    * binds the lemmas' names contracted, with its map: each Vi filling its slot
    * with its own map, the binders' origins of the rest kept, and the residue
    * spelled as the front end spells it (`Defunctionalization.relocatedMap`);
    * and each Vi with the name its binder is written with. The instruction as
    * it is, and no names, when the text binds none. Recursive on the k
    * applications of the redex.
    */
  private def namesContracted(
      instruction: Configured[Read],
      map: SourceMap
  ): (Configured[Read], SourceMap, Map[Configured[Read], String]) =
    def filled(
        at: Configured[Read],
        atMap: SourceMap
    ): (Configured[Read], SourceMap, Map[Configured[Read], String]) =
      at.layer match
        case Apply(function, value) =>
          val (functionFilled, functionMap, names) = filled(
            function,
            atMap.children.lift(0).getOrElse(SourceMap.unlocated)
          )
          val valueMap = atMap.children.lift(1).getOrElse(SourceMap.unlocated)
          functionFilled.layer match
            case Thunk(code, hole +: rest, fillings) =>
              val children =
                functionMap.children.padTo(fillings.size, SourceMap.unlocated)
              val (residueFillings, residueChildren) = hole match
                case Hole.Bound(slot) =>
                  val position = Defunctionalization.fillingPosition(rest, slot)
                  (
                    fillings.patch(position, Vector(value), 0),
                    children.patch(position, Vector(valueMap), 0)
                  )
                case Hole.Ignored => (fillings, children)
              val name =
                functionMap.binders.headOption.toVector.flatten.collectFirst {
                  case BinderOrigin.Written(written, _) => written
                }
              val residue = NonEmptyHoles.of(rest) match
                case Some(present) =>
                  NoFacts.thunk(code, present, residueFillings)
                case None => NoFacts.instance(code, residueFillings)
              (
                residue,
                SourceMap(
                  functionMap.locations,
                  functionMap.code,
                  residueChildren,
                  functionMap.binders.drop(1)
                ),
                name.fold(names)(written => names.updated(value, written))
              )
            case other =>
              throw TraceTextError(
                s"the names of a trace's text are bound by no abstraction: $other"
              )
        case _ => (at, atMap, Map.empty)
    instruction.layer match
      case Apply(_, _) =>
        val (residue, residueMap, names) = filled(instruction, map)
        val spelled = Defunctionalization.thunkInstruction[Read](
          Defunctionalization.instructionTerm(residue)
        )
        (
          spelled,
          Defunctionalization.relocatedMap(residue, residueMap, spelled),
          names
        )
      case _ => (instruction, map, Map.empty)

  /** The fields of a Scott tuple or constructor as the front end spells it,
    * with their maps: a thunk whose code is a spine of one of its holes' slots
    * applied to slots of its fillings, each field the filling of its slot
    * (`Defunctionalization.fillingPosition`), so that two equal fields are told
    * apart by their places, which a search for an equal instruction would not
    * do (a side `λa. λb. a` and a bit `λt. λf. t` of a literal are one
    * instruction). Throws `TraceTextError` for a term of another shape or of
    * another number of fields than `count`.
    */
  private def fields(
      instruction: Configured[Read],
      map: SourceMap,
      count: Int
  ): Vector[(Configured[Read], SourceMap)] =
    val found = constructorFields(instruction, map)
    if found.size != count then
      throw TraceTextError(
        s"the trace's data $instruction has ${found.size} fields, not $count"
      )
    found

  /** `fields` of a constructor of any number of fields. */
  private def constructorFields(
      instruction: Configured[Read],
      map: SourceMap
  ): Vector[(Configured[Read], SourceMap)] =
    instruction.layer match
      case Thunk(code, holes, fillings) =>
        val bound = holes.collect { case Hole.Bound(slot) => slot }.toSet
        val (head, arguments) = Spine.of(code)
        val found = arguments.map(_.layer match
          case com.yang_bo.gezi.ir.Slot(slot) if !bound.contains(slot) =>
            val position = Defunctionalization.fillingPosition(holes, slot)
            (
              fillings(position),
              map.children.lift(position).getOrElse(SourceMap.unlocated)
            )
          case other =>
            throw TraceTextError(
              s"a field of the trace's data is no filling: $other in $instruction"
            ))
        head.layer match
          case com.yang_bo.gezi.ir.Slot(slot) if bound.contains(slot) => found
          case _                                          =>
            throw TraceTextError(
              s"the trace's data $instruction is no constructor"
            )
      case other =>
        throw TraceTextError(s"the trace's data $other is no constructor")

  /** The spans of each field of a constructor (`fields`) where this occurrence
    * of the constructor writes it: the locations of the field's argument in the
    * map of the constructor's code, which are the field's own occurrence's,
    * while the map of its filling holds every occurrence of an equal field (an
    * item's tag `λh0. λh1. h0` and a side `λa. λb. a` are one filling). Throws
    * `TraceTextError` for a constructor whose code map locates no argument,
    * which a text read with its spans always locates.
    */
  private def fieldSpans(
      instruction: Configured[Read],
      map: SourceMap
  ): Vector[Set[Span]] =
    val count = constructorFields(instruction, map).size
    // The spine's arguments, last first: the map of `f a1 … an` holds the map
    // of `f a1 … an-1` first and that of `an` second.
    @scala.annotation.tailrec
    def collected(
        at: Option[SourceMap],
        remaining: Int,
        found: List[Set[Span]]
    ): Vector[Set[Span]] =
      if remaining == 0 then found.toVector
      else
        val argument = spans(
          at.flatMap(_.children.lift(1)).fold(Set.empty[Location])(_.locations)
        )
        if argument.isEmpty then
          throw TraceTextError(
            s"the map of the trace's data $instruction locates no field at ${remaining - 1}"
          )
        collected(
          at.flatMap(_.children.lift(0)),
          remaining - 1,
          argument :: found
        )
    collected(map.code, count, Nil)

  /** The spans of the text's own locations. */
  private def spans(locations: Set[Location]): Set[Span] = locations.collect {
    case Location.Source(_, span) => span
  }

  /** A side's map with each binder's origins narrowed to those written within
    * the side's own occurrence (`fieldSpans`), where it has any: a side equal
    * to another term of the text (`λa. λb. a`, the tag of an item of a lemma
    * with no text, and each nil `λn. λc. n` of its lists) is one interned
    * filling, whose map holds the origins of all its occurrences
    * (`Defunctionalization.relocatedMap`). A binder with no origin within the
    * side, of a value the names' β redex puts in a name's place, keeps its
    * origins.
    */
  private def writtenWithin(map: SourceMap, within: Set[Span]): SourceMap =
    def inside(origin: BinderOrigin): Boolean = origin match
      case BinderOrigin.Written(_, Location.Source(_, span)) =>
        within.exists(_.contains(span))
      case BinderOrigin.LiteralBit(_, _, Location.Source(_, span)) =>
        within.exists(_.contains(span))
      case _ => false
    SourceMap(
      map.locations,
      map.code.map(writtenWithin(_, within)),
      map.children.map(writtenWithin(_, within)),
      map.binders.map(origins =>
        if origins.exists(inside) then origins.filter(inside) else origins
      )
    )

  /** The items of a closed Scott list, nil `λn. λc. n` and a cell
    * `λn. λc. c ITEM REST`, with their maps. A loop, since a list nests as deep
    * as it is long.
    */
  private def listItems(
      list: Configured[Read],
      map: SourceMap
  ): Vector[(Configured[Read], SourceMap)] =
    @scala.annotation.tailrec
    def collected(
        at: Configured[Read],
        atMap: SourceMap,
        items: Vector[(Configured[Read], SourceMap)]
    ): Vector[(Configured[Read], SourceMap)] =
      constructorFields(at, atMap) match
        case Vector()                      => items
        case Vector(item, (rest, restMap)) =>
          collected(rest, restMap, items :+ item)
        case other =>
          throw TraceTextError(s"a list's cell has ${other.size} fields")
    collected(list, map, Vector.empty)

  /** The instruction the reader gives for the closed term of an instruction:
    * the instruction itself for every term the front end spells as it is
    * written. Throws `TraceTextError` otherwise.
    *
    * FIXME (2026-11-13): a term the trace writes (a binding, the thunk of a
    * https://github.com/Atry/private-overlay/issues/1984 step backward, a
    * native value) may be a spelling the e-graph made and the front end never
    * makes, such as `λz. A B` with A and B two fillings (`thunk(apply(slot,
    * slot), [ignored], [A, B])`), which the front end spells with the closed
    * `A B` as one filling; such a trace has no text. No generated round of
    * strategies' `RewriteTraceLawTest` writes one since the β conversions are
    * `Convert` commands, whose replacements are computed. Candidate fix, in the
    * trace's model, where the IR is not part of the trace: a command that
    * computes the term in place of the one that writes it, as `Convert` does
    * for a conversion.
    */
  def readBack[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C, StorageAccess): Configured[C] =
    val again = Defunctionalization.thunkInstruction[C](
      Lambdalattice.term(Lambdalattice.closedTextViewed(instruction))
    )
    if Configured.same(again, instruction) then instruction
    else
      throw TraceTextError(
        s"the front end reads the text of $instruction as $again"
      )

  /** The closed Scott list of the items, each item on a line of its own: each
    * cell opened in turn, nil, and the cells closed, the text built once, not
    * copied into each enclosing cell (a trace of 117,310 commands).
    */
  private def listText(items: Vector[String], indentation: String): String =
    items
      .map(item => s"(λn. λc. c $item\n$indentation  ")
      .mkString + "(λn. λc. n)" + ")" * items.size

  /** The closed Scott list of the items, on one line, built as `listText`. */
  private def inlineListText(items: Vector[String]): String =
    items
      .map(item => s"(λn. λc. c $item ")
      .mkString + "(λn. λc. n)" + ")" * items.size

  /** The text of a closed instruction, in parentheses. */
  private def closedText[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C, StorageAccess): String =
    s"(${Lambdalattice.closedTextViewed(readBack(instruction))})"

  /** The text of an instruction under openings, in parentheses, each
    * eigenvariable of `names` written as the name of its λ. Throws
    * `TraceTextError` when the reader, which reads it at the eigenvariables
    * (`KnowledgeReading.term`, the front end's respelling), would read another
    * instruction.
    */
  private def termText[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      names: Map[Configured[C], String]
  )(using
      C,
      StorageAccess
  ): String =
    if !Conversions.holds(instruction, names.keySet) then
      closedText(instruction)
    else
      val again = Respelling.respelled(instruction, Set.empty)
      if Configured.same(again, instruction) then
        s"(${Lambdalattice.text(Defunctionalization.instructionTermViewed(instruction), names)})"
      else
        throw TraceTextError(
          s"the front end respells $instruction under its eigenvariables as $again"
        )

  /** The alternative of a Scott constructor of `count` alternatives, from 0:
    * `count` abstractions, the handler of the alternative applied to the
    * fields, each field a text in parentheses.
    */
  private def constructorText(
      count: Int,
      alternative: Int,
      fields: Vector[String]
  ): String =
    val handlers = Vector.tabulate(count)(place => s"h$place")
    s"(${handlers.map(handler => s"λ$handler. ").mkString}${(handlers(alternative) +: fields).mkString(" ")})"

  private def tupleText(fields: Vector[String]): String =
    constructorText(1, 0, fields)

  /** The trie of the integer's CBOR literal, in the diagnostic notation. */
  private def integerText(value: Int): String = s"(λk. k $value)"

  private def optionText[C <: NativeSpecializer & Singleton](
      named: Option[ThunkShape[C]],
      names: Map[Configured[C], String]
  )(using C, StorageAccess): String = named match
    case None        => constructorText(2, 0, Vector.empty)
    case Some(shape) =>
      val holes = inlineListText(shape.holes.map {
        case Hole.Bound(slot) =>
          constructorText(2, 0, Vector(integerText(slot)))
        case Hole.Ignored => constructorText(2, 1, Vector.empty)
      })
      constructorText(
        2,
        1,
        Vector(tupleText(Vector(givenText(shape.codeOf, names), holes)))
      )

  private def givenText[C <: NativeSpecializer & Singleton](
      named: Given[C],
      names: Map[Configured[C], String]
  )(using C, StorageAccess): String = named match
    case Given.Value(index) => constructorText(2, 0, Vector(integerText(index)))
    case Given.Written(term) =>
      constructorText(2, 1, Vector(termText(term, names)))

  private def sourceText(source: ValueSource): String = source match
    case ValueSource.RoundStart(round) =>
      constructorText(2, 0, Vector(integerText(round)))
    case ValueSource.Value(index) =>
      constructorText(2, 1, Vector(integerText(index)))

  /** The text of a command under `depth` openings, `names` the names of their
    * eigenvariables. An abstraction's commands are written under one λ per
    * eigenvariable of its thunk, named by its depth and place, and the reader
    * applies them to its own eigenvariables.
    */
  private def commandText[C <: NativeSpecializer & Singleton](
      command: TraceCommand[C],
      depth: Int,
      names: Map[Configured[C], String],
      move: String
  )(using C, StorageAccess): String =
    command match
      case TraceCommand.Rewrite(reason, _, direction, bindings) =>
        constructorText(
          4,
          0,
          Vector(
            reasonText(reason, names),
            move,
            directionText(direction),
            bindingsText(bindings, names)
          )
        )
      case TraceCommand.Convert(conversion, _, direction, bindings) =>
        constructorText(
          4,
          1,
          Vector(
            conversionText(conversion),
            move,
            directionText(direction),
            bindingsText(bindings, names)
          )
        )
      case TraceCommand.Native(_, value) =>
        constructorText(4, 2, Vector(move, termText(value, names)))
      case TraceCommand.Abstraction(_, count, commands) =>
        val variables = Vector.tabulate(count)(place => s"e${depth}_$place")
        val inner =
          names ++ Conversions.eigenvariables(depth, count).zip(variables)
        val opened =
          s"(${variables.map(variable => s"λ$variable. ").mkString}${inlineListText(commandsText(commands, depth + 1, inner))})"
        constructorText(4, 3, Vector(move, integerText(count), opened))

  /** The texts of a list of commands, each command's position written as a move
    * from the position of the command before it (`moveText`), the first's from
    * the root.
    */
  private def commandsText[C <: NativeSpecializer & Singleton](
      commands: Vector[TraceCommand[C]],
      depth: Int,
      names: Map[Configured[C], String]
  )(using C, StorageAccess): Vector[String] =
    val (texts, _) =
      commands.foldLeft((Vector.empty[String], Vector.empty[PositionSegment])) {
        case ((written, previous), command) =>
          (
            written :+ commandText(
              command,
              depth,
              names,
              moveText(previous, command.at)
            ),
            command.at
          )
      }
    texts

  /** A position written as a move from the previous one: how many segments of
    * the previous position to drop, and the segments that follow. The steps of
    * a proof are local, so that a move is short where the position is deep:
    * written whole, the positions of the 117,310 commands of
    * `contest-entries-solo`'s repeated_library_hotspots calls_1000 point were
    * 16,901,930 segments, and the text did not fit a heap of 4.5 GB.
    */
  private def moveText(
      previous: Vector[PositionSegment],
      position: Vector[PositionSegment]
  ): String =
    val shared = previous.zip(position).takeWhile(_ == _).size
    tupleText(
      Vector(
        integerText(previous.size - shared),
        positionText(position.drop(shared))
      )
    )

  private def directionText(direction: RewriteDirection): String =
    constructorText(2, direction.ordinal, Vector.empty)

  private def bindingsText[C <: NativeSpecializer & Singleton](
      bindings: Vector[(Int, Given[C])],
      names: Map[Configured[C], String]
  )(using C, StorageAccess): String =
    inlineListText(
      bindings.map((place, named) =>
        tupleText(Vector(integerText(place), givenText(named, names)))
      )
    )

  private def conversionText(conversion: Conversion): String = conversion match
    case Conversion.HigherOrder(lemma, side, occurrence) =>
      constructorText(
        2,
        0,
        Vector(
          integerText(lemma),
          constructorText(2, side.ordinal, Vector.empty),
          integerText(occurrence)
        )
      )
    case Conversion.RootReverseBeta(lemma) =>
      constructorText(2, 1, Vector(integerText(lemma)))

  private def reasonText[C <: NativeSpecializer & Singleton](
      reason: ProvedReason[C],
      names: Map[Configured[C], String]
  )(using C, StorageAccess): String = reason match
    case ProvedReason.Lemma(index) =>
      constructorText(5, 0, Vector(integerText(index)))
    case ProvedReason.Equation(number) =>
      constructorText(5, 1, Vector(integerText(number)))
    case ProvedReason.Fill(written) =>
      constructorText(5, 2, Vector(optionText(written, names)))
    case ProvedReason.Body(written) =>
      constructorText(5, 3, Vector(optionText(written, names)))
    case ProvedReason.Eta(written) =>
      constructorText(5, 4, Vector(optionText(written, names)))

  private def positionText(position: Vector[PositionSegment]): String =
    inlineListText(position.map {
      case PositionSegment.Function       => constructorText(5, 0, Vector.empty)
      case PositionSegment.Argument       => constructorText(5, 1, Vector.empty)
      case PositionSegment.Left           => constructorText(5, 2, Vector.empty)
      case PositionSegment.Right          => constructorText(5, 3, Vector.empty)
      case PositionSegment.Filling(index) =>
        constructorText(5, 4, Vector(integerText(index)))
    })

  private def traceRead(value: Value[Read]): Reading[Read, Trace[Read]] =
    locatedTraceRead(value).map(_._1)

  /** The trace and the location of each of its lemmas, none for a lemma the
    * text writes as closed terms.
    */
  private def locatedTraceRead(
      value: Value[Read]
  ): Reading[Read, (Trace[Read], Vector[Option[LemmaLocation]])] =
    KnowledgeReading.fields(value, 3).flatMap {
      case Vector(lemmas, values, rounds) =>
        for
          lemmasRead <- listRead(lemmas)(lemmaRead)
          valuesRead <- listRead(values)(valueRead)
          roundsRead <- listRead(rounds)(commandsRead(_, 0))
        yield (
          Trace(lemmasRead.map(_._1), valuesRead, roundsRead),
          lemmasRead.map(_._2)
        )
      case other =>
        throw KnowledgeReadingError(
          s"a tuple of three has ${other.size} fields"
        )
    }

  private def valueRead(value: Value[Read]): Reading[Read, TraceValue[Read]] =
    KnowledgeReading.fields(value, 3).flatMap {
      case Vector(source, commands, at) =>
        for
          sourceRead <- KnowledgeReading.alternative(source, 2).flatMap {
            case (0, Vector(round)) =>
              integerRead(round).map(ValueSource.RoundStart(_))
            case (1, Vector(index)) =>
              integerRead(index).map(ValueSource.Value(_))
            case (alternative, fields) =>
              throw KnowledgeReadingError(
                s"a source's alternative $alternative has ${fields.size} fields"
              )
          }
          commandsRead <- this.commandsRead(commands, 0)
          atRead <- positionRead(at)
        yield TraceValue(sourceRead, commandsRead, atRead)
      case other =>
        throw KnowledgeReadingError(
          s"a tuple of three has ${other.size} fields"
        )
    }

  private def givenRead(value: Value[Read]): Reading[Read, Given[Read]] =
    KnowledgeReading.alternative(value, 2).flatMap {
      case (0, Vector(index)) => integerRead(index).map(Given.Value[Read](_))
      case (1, Vector(term))  => Computation.pure(Given.Written(termRead(term)))
      case (alternative, fields) =>
        throw KnowledgeReadingError(
          s"a given term's alternative $alternative has ${fields.size} fields"
        )
    }

  private def listRead[Item](value: Value[Read])(
      item: Value[Read] => Reading[Read, Item]
  ): Reading[Read, Vector[Item]] =
    KnowledgeReading.items(value).flatMap(Computation.traversed(_)(item))

  private def termRead(value: Value[Read]): Configured[Read] =
    KnowledgeReading.term(value, Set.empty)

  private def lemmaRead(
      value: Value[Read]
  ): Reading[Read, (TraceLemma[Read], Option[LemmaLocation])] =
    KnowledgeReading.fields(value, 3).flatMap {
      case Vector(location, left, right) =>
        locationRead(location)
          .map(read => (TraceLemma(termRead(left), termRead(right)), read))
      case other =>
        throw KnowledgeReadingError(
          s"a tuple of three has ${other.size} fields"
        )
    }

  /** A lemma's location: none, or its file's URI, a trie of its text, and the
    * span, decoded by the host.
    */
  private def locationRead(
      value: Value[Read]
  ): Reading[Read, Option[LemmaLocation]] =
    KnowledgeReading.alternative(value, 2).flatMap {
      case (0, Vector())         => Computation.pure(None)
      case (1, Vector(location)) =>
        KnowledgeReading.fields(location, 3).flatMap {
          case Vector(uri, start, end) =>
            for
              uriRead <- KnowledgeReading.trieText(uri)
              startRead <- integerRead(start)
              endRead <- integerRead(end)
            yield Some(
              LemmaLocation(java.net.URI(uriRead), Span(startRead, endRead))
            )
          case other =>
            throw KnowledgeReadingError(
              s"a tuple of three has ${other.size} fields"
            )
        }
      case (alternative, fields) =>
        throw KnowledgeReadingError(
          s"a location's alternative $alternative has ${fields.size} fields"
        )
    }

  /** The integer of a trie of its CBOR literal, decoded by the host. */
  private def integerRead(value: Value[Read]): Reading[Read, Int] =
    KnowledgeReading
      .trieInteger(value)
      .map(read =>
        if read.isValidInt then read.toInt
        else throw KnowledgeReadingError(s"the integer $read is no Int")
      )

  /** A command as its text gives it before the list it is in places it: the
    * segments its move drops from the position before it, the segments it adds,
    * and the command at the position the two make.
    */
  private final case class Moved(
      dropped: Int,
      added: Vector[PositionSegment],
      placed: Vector[PositionSegment] => TraceCommand[Read]
  )

  /** The commands of a list under `depth` openings, each placed at the position
    * its move makes of the position before it, the first's from the root
    * (`moveText`). Throws `KnowledgeReadingError` for a move that drops more
    * segments than the position before it has.
    */
  private def commandsRead(
      value: Value[Read],
      depth: Int
  ): Reading[Read, Vector[TraceCommand[Read]]] =
    listRead(value)(commandRead(_, depth)).map(moved =>
      val (commands, _) = moved.foldLeft(
        (Vector.empty[TraceCommand[Read]], Vector.empty[PositionSegment])
      ) { case ((placed, previous), Moved(dropped, added, command)) =>
        if dropped > previous.size then
          throw KnowledgeReadingError(
            s"a move drops $dropped segments of a position of ${previous.size}"
          )
        val position = previous.dropRight(dropped) ++ added
        (placed :+ command(position), position)
      }
      commands
    )

  /** A move: the segments dropped and the segments added. */
  private def moveRead(
      value: Value[Read]
  ): Reading[Read, (Int, Vector[PositionSegment])] =
    KnowledgeReading.fields(value, 2).flatMap {
      case Vector(dropped, added) =>
        for
          droppedRead <- integerRead(dropped)
          addedRead <- positionRead(added)
        yield (droppedRead, addedRead)
      case other =>
        throw KnowledgeReadingError(s"a tuple of two has ${other.size} fields")
    }

  /** The command of a value under `depth` openings, before its list places it
    * (`Moved`): an abstraction's commands applied to the eigenvariables of its
    * depth and read under one more.
    */
  private def commandRead(
      value: Value[Read],
      depth: Int
  ): Reading[Read, Moved] =
    KnowledgeReading.alternative(value, 4).flatMap {
      case (0, Vector(reason, move, direction, bindings)) =>
        for
          reasonRead <- this.reasonRead(reason)
          (dropped, added) <- moveRead(move)
          directionRead <- this.directionRead(direction)
          bindingsRead <- this.bindingsRead(bindings)
        yield Moved(
          dropped,
          added,
          TraceCommand.Rewrite[Read](reasonRead, _, directionRead, bindingsRead)
        )
      case (1, Vector(conversion, move, direction, bindings)) =>
        for
          conversionRead <- this.conversionRead(conversion)
          (dropped, added) <- moveRead(move)
          directionRead <- this.directionRead(direction)
          bindingsRead <- this.bindingsRead(bindings)
        yield Moved(
          dropped,
          added,
          TraceCommand
            .Convert[Read](conversionRead, _, directionRead, bindingsRead)
        )
      case (2, Vector(move, written)) =>
        moveRead(move).map((dropped, added) =>
          Moved(dropped, added, TraceCommand.Native[Read](_, termRead(written)))
        )
      case (3, Vector(move, count, commands)) =>
        for
          (dropped, added) <- moveRead(move)
          countRead <- integerRead(count)
          leaves = Conversions.eigenvariables(depth, countRead)
          applied = leaves.foldLeft(commands)((function, leaf) =>
            Value.Apply(function, Value.of(leaf))
          )
          commandsRead <- this.commandsRead(applied, depth + 1)
        yield Moved(
          dropped,
          added,
          TraceCommand.Abstraction[Read](_, countRead, commandsRead)
        )
      case (alternative, fields) =>
        throw KnowledgeReadingError(
          s"a command's alternative $alternative has ${fields.size} fields"
        )
    }

  private def directionRead(
      value: Value[Read]
  ): Reading[Read, RewriteDirection] =
    KnowledgeReading
      .alternative(value, 2)
      .map((alternative, _) => RewriteDirection.fromOrdinal(alternative))

  private def bindingsRead(
      value: Value[Read]
  ): Reading[Read, Vector[(Int, Given[Read])]] =
    listRead(value)(binding =>
      KnowledgeReading.fields(binding, 2).flatMap {
        case Vector(place, bound) =>
          for
            placeRead <- integerRead(place)
            boundRead <- givenRead(bound)
          yield (placeRead, boundRead)
        case other =>
          throw KnowledgeReadingError(
            s"a tuple of two has ${other.size} fields"
          )
      }
    )

  private def conversionRead(value: Value[Read]): Reading[Read, Conversion] =
    KnowledgeReading.alternative(value, 2).flatMap {
      case (0, Vector(lemma, side, occurrence)) =>
        for
          lemmaRead <- integerRead(lemma)
          sideRead <- KnowledgeReading.alternative(side, 2)
          occurrenceRead <- integerRead(occurrence)
        yield Conversion.HigherOrder(
          lemmaRead,
          LemmaSide.fromOrdinal(sideRead._1),
          occurrenceRead
        )
      case (1, Vector(lemma)) =>
        integerRead(lemma).map(Conversion.RootReverseBeta(_))
      case (alternative, fields) =>
        throw KnowledgeReadingError(
          s"a conversion's alternative $alternative has ${fields.size} fields"
        )
    }

  private def reasonRead(
      value: Value[Read]
  ): Reading[Read, ProvedReason[Read]] =
    KnowledgeReading.alternative(value, 5).flatMap {
      case (0, Vector(index)) =>
        integerRead(index).map(ProvedReason.Lemma[Read](_))
      case (1, Vector(number)) =>
        integerRead(number).map(ProvedReason.Equation[Read](_))
      case (2, Vector(written)) => optionRead(written).map(ProvedReason.Fill(_))
      case (3, Vector(written)) => optionRead(written).map(ProvedReason.Body(_))
      case (4, Vector(written)) => optionRead(written).map(ProvedReason.Eta(_))
      case (alternative, fields) =>
        throw KnowledgeReadingError(
          s"a reason's alternative $alternative has ${fields.size} fields"
        )
    }

  private def optionRead(
      value: Value[Read]
  ): Reading[Read, Option[ThunkShape[Read]]] =
    KnowledgeReading.alternative(value, 2).flatMap {
      case (0, Vector())      => Computation.pure(None)
      case (1, Vector(shape)) =>
        KnowledgeReading.fields(shape, 2).flatMap {
          case Vector(codeOf, holes) =>
            for
              codeOfRead <- givenRead(codeOf)
              holesRead <- listRead(holes)(hole =>
                KnowledgeReading.alternative(hole, 2).flatMap {
                  case (0, Vector(slot)) => integerRead(slot).map(Hole.Bound(_))
                  case (1, Vector())     => Computation.pure(Hole.Ignored)
                  case (alternative, fields) =>
                    throw KnowledgeReadingError(
                      s"a hole's alternative $alternative has ${fields.size} fields"
                    )
                }
              )
            yield Some(ThunkShape(codeOfRead, holesRead))
          case other =>
            throw KnowledgeReadingError(
              s"a tuple of two has ${other.size} fields"
            )
        }
      case (alternative, fields) =>
        throw KnowledgeReadingError(
          s"an option's alternative $alternative has ${fields.size} fields"
        )
    }

  private def positionRead(
      value: Value[Read]
  ): Reading[Read, Vector[PositionSegment]] =
    listRead(value)(segment =>
      KnowledgeReading.alternative(segment, 5).flatMap {
        case (0, Vector())      => Computation.pure(PositionSegment.Function)
        case (1, Vector())      => Computation.pure(PositionSegment.Argument)
        case (2, Vector())      => Computation.pure(PositionSegment.Left)
        case (3, Vector())      => Computation.pure(PositionSegment.Right)
        case (4, Vector(index)) =>
          integerRead(index).map(PositionSegment.Filling(_))
        case (alternative, fields) =>
          throw KnowledgeReadingError(
            s"a segment's alternative $alternative has ${fields.size} fields"
          )
      }
    )
