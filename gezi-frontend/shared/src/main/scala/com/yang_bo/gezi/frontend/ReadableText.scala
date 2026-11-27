package com.yang_bo.gezi.frontend

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.IrLayer
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.NativeStorage
import com.yang_bo.gezi.ir.ScottReading
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.locations.BinderOrigin
import com.yang_bo.gezi.locations.Location
import com.yang_bo.gezi.locations.MadeBy
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.locations.Span
import scala.jdk.StreamConverters.*
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import scala.util.hashing.MurmurHash3

/** The printer: a closed IR term written as lambdalattice text with names and
  * with sharing, in the layout of `CONTRIBUTING.md`, "lambdalattice layout: no
  * right-associative parentheses, CPS one step per line", as one line.
  *
  *   - SHARING. A closed instruction the term refers to more than once (a child
  *     of two layers, or a filling whose slot its code reads twice) is written
  *     once, bound by the library's import form `(λt. t V) λm. BODY` which is
  *     `BODY[m := V]` after two β steps; the bindings stand outermost, an
  *     instruction after those it refers to, so the text is linear in the
  *     number of distinct instructions where a tree is exponential in the depth
  *     of its diamonds. An opaque instruction or a URI node is a name and is
  *     never bound. Only closed instructions are shared: a subterm repeated
  *     inside one code, which reads the code's binders, is written as often as
  *     it occurs. The references counted are those the text writes: an
  *     instruction the text refers to once is written in place, and one it
  *     never refers to is not bound, as top is when every top is inside
  *     complete literals (LITERALS).
  *   - NAMES. A binder is named from its origin in the term's map
  *     (`com.yang_bo.gezi.locations.BinderOrigin`): a written binder and an enclosing name
  *     by their names, the bit of a literal by the literal and the bit's place
  *     (`number_42_digit_5`, `LiteralWriting.bitName`), a binder a trace's step
  *     made by the kind of the step (`eta`, `native`), spelled by
  *     `NameSpelling`, with `_2`, `_3` and so on appended while it would equal
  *     a name in scope or a name of the text's constants, so that no binder
  *     shadows another and the text reads back as the term. Of several origins,
  *     which the map of several occurrences holds, the least name is taken. A
  *     binder with no origin is an error: there is no fallback name such as
  *     `x_N`. A shared instruction's binders are named from the maps of its
  *     occurrences. A shared instruction is named in the JVM's convention for a
  *     synthesized name (`NameSpelling.shared`): the head of its application
  *     spine when the head is an opaque instruction, a URI node or a known
  *     instruction, then `$merkle$` and its content hash,
  *     `cons$merkle$89abcdef`, `$merkle$89abcdef`, and `$2`, `$3` and so on
  *     appended while it would equal a name of the text's constants, a
  *     collision of hashes; an opaque instruction by its name; a URI node by
  *     its URI; a known instruction, one a caller names for display
  *     (`KnownNames`), by that name, bound however often it occurs or written
  *     as a name and never bound; each escaped by `NameSpelling`.
  *   - NO RIGHT-ASSOCIATIVE PARENTHESES. The last argument of an application is
  *     never in parentheses unless it is a chain of + and ∥: an abstraction
  *     stands bare, `f λx. M`, and an application after `λ.`, `f λ. g x`.
  *     Adjacent binders merge, `λb a r.`, and `λ.` is written only before an
  *     application.
  *   - CHAINS. A choice or a parallel whose left side is one is written as one
  *     chain, left associative; a right side that is one stands in parentheses.
  *   - LITERALS. A complete literal is written back as its CBOR diagnostic
  *     notation (`LiteralWriting`): a run of bit arguments of an application
  *     (`Literals.arguments`), and a chain of abstractions that is the variable
  *     arguments partial function of a literal (`Literals.partialFunction`),
  *     whose body does not read the bits' binders. A bit is never shared, and
  *     neither is an application whose last argument is a bit, so that sharing
  *     never cuts a literal of arguments in two; the literal's notation writes
  *     no top of its bits, so that top is bound only when the text outside
  *     complete literals refers to it twice (SHARING). The binders of a partial
  *     function's bits that no complete literal takes are named by their
  *     literal and bit, as NAMES says.
  *   - STORAGES. A native storage is read one layer at a time as the printer
  *     recurses, the one place a storage's content is read recursively: the
  *     printer is a formatter that writes text and builds no term. Two readings
  *     (`Reading`). The display reading writes a storage as its view
  *     `value ∥ criterion` (the specializer's `viewOf`), the text of the term
  *     the storage stands for, every `∥ T` kept. The Scott ADT reading writes
  *     it as its untyped Scott ADT layer `λc1 … ck. ci f1 … fn`
  *     (`scottReadingOf`), its fields written recursively, and a parallel node
  *     `v ∥ E` as v; the layer is spelled as `Defunctionalization` spells the
  *     same term (equal fields one slot), so that its name and sharing are
  *     those of that term.
  *   - THE TABLE OF A WRITE. A storage's layer is no interned object, so the
  *     printer counts, hashes and names the nodes of a table of its own for the
  *     one write (`Table`): objects whose layers hold the same parts are one
  *     node, as in the interned term the text stands for, so a storage and the
  *     parallel or thunk it is written as are one, and two storages of one view
  *     are one. A write may hold terms read under both readings (the line of
  *     Scott ADT values and a remainder): a node is the reading and the object,
  *     so a storage met under both is two nodes.
  *
  * The text is a sequence of pieces, each a token or the opening or closing of
  * a node of the structure the player's view draws (`Node`): the right spine of
  * a term as a sequence of expressions and parameter lists, an expression's
  * head and arguments, a chain's operands, a parenthesized term. `text` joins
  * the tokens.
  *
  * A piece `At` marks where the text of a subterm of the IR starts, with the
  * subterm's place (`Place`): the binding it is written in, the body's or a
  * shared instruction's, and its path in the IR from there, so that the
  * player's view highlights and animates the node a step rewrote. A subterm
  * that stands as a node of its own (`suffix` false) is the node whose opening
  * follows the mark; one that continues an open spine (`suffix` true) is the
  * rest of that spine from the mark, its k-th sibling to the end, a parameter
  * list of binders merged from the abstractions around it included. A subterm
  * the text writes inside another's piece has no mark: the inner applications
  * of a spine, the inner links of a chain, an abstraction whose binders merge
  * into those of the abstraction around it, the bits of a complete literal, and
  * the parts of a shared instruction that the text never writes; a view takes
  * the nearest place above it.
  */
object ReadableText:

  /** The place of a subterm of the printed instruction: the name of the shared
    * instruction whose binding writes it, none for the body, and its path from
    * that instruction in the IR, by the indices of `Layer.children`.
    */
  final case class Place(binding: Option[String], path: Vector[Int]):

    /** The place as one string, distinct for distinct places, for a view's
      * attribute.
      */
    def key: String = s"${binding.getOrElse("")}:${path.mkString(".")}"

  /** A node of the printed structure. */
  enum Node:

    /** The right spine of a term: expressions and parameter lists in turn. */
    case Spine

    /** A head and the arguments before the last, or a lone atom. */
    case Expression

    /** `λb a r.`, the binders of adjacent abstractions, each an atom, or `λ.`.
      */
    case Parameters

    /** A chain of + and ∥: its first operand, then each step. */
    case Chain

    /** An operator of a chain and its operand. */
    case Step

    /** A term in parentheses. */
    case Parenthesized

    /** A name or a literal. */
    case Atom

  /** A piece of the printed text. */
  enum Piece:
    case Token(text: String)
    case Open(node: Node)
    case Close

    /** Where the text of the subterm at the place starts. */
    case At(place: Place, suffix: Boolean)

    /** Where a name or a literal starts that the source text spells at the code
      * point offset `start`, written by `writtenBack` only, for a formatter to
      * put the source's comments back by it.
      */
    case Source(start: Int)

  /** A shared instruction the text binds: its name, the instruction, and the
    * map of its occurrences merged, from which its binders are named. The
    * instruction is the first object of the shared node in the walk, under the
    * reading the node was met under (a node is a class of objects whose layers,
    * as written, have the same parts), so that a storage written as its view is
    * the storage itself. For display and provenance only: nothing is chosen by
    * it.
    */
  final case class SharedValue[C <: NativeSpecializer & Singleton](
      name: String,
      instruction: Configured[C],
      map: SourceMap
  )

  /** The printed term: its pieces, the number of shared instructions bound at
    * its start, the instruction printed, the name of each shared instruction,
    * and the shared instructions in the order the text binds them, each after
    * those it refers to.
    */
  final case class Printed[C <: NativeSpecializer & Singleton](
      pieces: Vector[Piece],
      bindings: Int,
      root: Configured[C],
      sharedNames: Map[Configured[C], String],
      sharedValues: Vector[SharedValue[C]]
  ):

    /** The text the tokens spell, on one line. */
    def text: String = pieces.collect { case Piece.Token(token) =>
      token
    }.mkString

    /** The text in the multi-line CPS layout of CONTRIBUTING.md, "lambdalattice
      * layout: no right-associative parentheses, CPS one step per line", the
      * printer's default: `brokenText`, a text that spans lines wrapped in
      * parentheses unless it is a right spine (`LambdalatticeLayout.isSpine`),
      * and laid out by `LambdalatticeLayout` with `ParameterLists.Prefixed`,
      * which sets the columns; one line when the text is no wider than `width`,
      * laid out too, so that a λ starting it is written as the layout writes a
      * λ starting a line, `λ f. f`.
      */
    def laidOut(width: Int): String =
      val broken = brokenText(width)
      val wrapped =
        if broken.contains('\n') && !LambdalatticeLayout.isSpine(
            Lambdalattice.lexemes(broken)
          )
        then s"($broken\n)"
        else broken
      LambdalatticeLayout
        .laidOut(
          Lambdalattice.lexemes(wrapped),
          LambdalatticeLayout.ParameterLists.Prefixed
        )
        .stripTrailing

    /** The pieces with the layout of `laidOut(width)`, for a view that draws
      * the printed structure as the layout writes it: the same openings,
      * closings and marks in the same order, the pieces' own white space
      * dropped, each token spelled as the laid out text spells it (an operator
      * without its spaces, `λ.` with the line break the layout may put between
      * its two tokens), and what the layout writes between two tokens of the
      * pieces written as a token of its own where `brokenText` puts a break:
      * after the token before it and the closings right after that token,
      * before the openings and marks that lead to it. What the layout writes
      * between two tokens is white space and the tokens it adds: the `λ` line
      * that opens a right spine starting with an expression, and the
      * parentheses `laidOut` puts around a text that spans lines and is no
      * right spine. So the tokens' texts are `laidOut(width)` in order. Throws
      * `IllegalStateException` when the laid out text holds a token the pieces
      * do not and the layout does not add.
      */
    def laidOutPieces(width: Int): Vector[Piece] =
      val text = laidOut(width)
      // Each token of the laid out text with its start and its end.
      val (_, tokens) = Lambdalattice
        .lexemes(text)
        .foldLeft((0, Vector.empty[(String, Int, Int)])) {
          case ((offset, found), lexeme) =>
            val end = offset + lexeme.written.length
            lexeme match
              case Lexeme.Token(_, written) =>
                (end, found :+ (written, offset, end))
              case Lexeme.Space(_)         => (end, found)
              case Lexeme.Comment(written) =>
                throw IllegalStateException(
                  s"the printer writes no comment: $written"
                )
        }
      // The index of the laid out token that spells the expected token, at or
      // after the cursor, the tokens skipped being ones the layout adds.
      def matched(expected: String, cursor: Int): Int =
        val index = tokens.indexWhere(_._1 == expected, cursor)
        if index < 0 then
          throw IllegalStateException(
            s"the laid out text has no $expected where the pieces write it: $text"
          )
        tokens
          .slice(cursor, index)
          .find((written, _, _) => !layoutTokens.contains(written))
          .foreach((written, _, _) =>
            throw IllegalStateException(
              s"the laid out text writes $written, which the pieces do not and the layout does not add: $text"
            )
          )
        index
      // The cursor among the laid out tokens, the end of the last token
      // matched, the position after the token before and its closings,
      // whether a node opened since, what stands before each position, and
      // each token's laid out text.
      val (cursor, lastEnd, _, _, before, respelled) =
        pieces.zipWithIndex.foldLeft(
          (0, 0, 0, false, Map.empty[Int, String], Map.empty[Int, String])
        ) {
          case (
                (cursor, lastEnd, after, _, before, respelled),
                (Piece.Token(token), position)
              ) if tokenCount(token) > 0 =>
            val (leading, following) = if token == "λ." then ("λ", Vector("."))
            else (token.trim, Vector.empty)
            val first = matched(leading, cursor)
            val last = following.foldLeft(first)((previous, next) =>
              if tokens.lift(previous + 1).exists(_._1 == next) then
                previous + 1
              else
                throw IllegalStateException(
                  s"the laid out text splits $token: $text"
                )
            )
            val (_, start, _) = tokens(first)
            val (_, _, end) = tokens(last)
            (
              last + 1,
              end,
              position + 1,
              false,
              before.updated(after, text.substring(lastEnd, start)),
              respelled.updated(position, text.substring(start, end))
            )
          case (
                (cursor, lastEnd, _, false, before, respelled),
                (Piece.Close, position)
              ) =>
            (cursor, lastEnd, position + 1, false, before, respelled)
          case (
                (cursor, lastEnd, after, _, before, respelled),
                (Piece.Open(_), _)
              ) =>
            (cursor, lastEnd, after, true, before, respelled)
          case (state, _) => state
        }
      tokens
        .drop(cursor)
        .find((written, _, _) => !layoutTokens.contains(written))
        .foreach((written, _, _) =>
          throw IllegalStateException(
            s"the laid out text ends in $written, which the pieces do not write: $text"
          )
        )
      val body = pieces.zipWithIndex.flatMap { (piece, position) =>
        val added =
          before.get(position).filter(_.nonEmpty).map(Piece.Token(_)).toVector
        piece match
          case Piece.Token(_) =>
            added ++ respelled.get(position).map(Piece.Token(_))
          case other => added :+ other
      }
      body ++ Vector(text.substring(lastEnd))
        .filter(_.nonEmpty)
        .map(Piece.Token(_))

    /** The text with a line break wherever the multi-line CPS layout puts one,
      * before the layout sets the columns: a spine wider than `width` breaks
      * before each parameter list's `λ` and its `.` until the rest of it, from
      * an expression or a parameter list on, is no wider than `width`, which
      * stays on one line (widths are counted without the columns the layout
      * indents by); in such a spine, an expression wider than `width` puts each
      * parenthesized argument on a line of its own; parentheses wider than
      * `width` close on a line of their own; a chain wider than `width` breaks
      * before each operator. Each part no wider than `width` is written on one
      * line.
      */
    def brokenText(width: Int): String = brokenText(width, Set.empty)

    /** `brokenText` with a break before each token whose index (`tokenCount`)
      * is among the breaks, where the formatter puts back a comment of the
      * source or keeps a line break of it (`SourceFormatting`): no part with a
      * break inside, a part with a token before the break and one after it, is
      * written on one line, as no part wider than the width is; so a spine
      * breaks at least until the rest of it holds no break.
      */
    def brokenText(width: Int, breaks: Set[Int]): String =
      ReadableText.broken(pieces, width, breaks)

    /** The place of the subterm of `root` at the path, by the indices of
      * `Layer.children`: in the binding of the last shared instruction on the
      * way down, else in the body. Throws `IllegalArgumentException` for a path
      * that leads below a leaf.
      */
    def place(path: Vector[Int])(using C, StorageAccess): Place =
      path
        .foldLeft((root, Place(None, Vector.empty))) {
          case ((current, found), index) =>
            val child = Option
              .unless(current.opaque)(childrenOf(current))
              .flatMap(_.lift(index))
              .getOrElse(
                throw IllegalArgumentException(
                  s"the path $path leads below the term $current"
                )
              )
            (
              child,
              sharedNames
                .get(child)
                .fold(found.copy(path = found.path :+ index))(name =>
                  Place(Some(name), Vector.empty)
                )
            )
        }
        ._2

  /** The term printed, its binders named from the origins `map` gives them,
    * `map` being the map of an occurrence of the instruction. Throws
    * `IllegalArgumentException` for an instruction that is no closed term
    * (`Defunctionalization.instructionTerm`'s errors) and for a binder the map
    * gives no origin.
    */
  def printed[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap
  )(using C, StorageAccess): Printed[C] =
    printedWith(
      instruction,
      map,
      None,
      true,
      KnownNames.Bound(Map.empty),
      Set.empty,
      Reading.Display
    )

  /** `printed`, each instruction `known` names called by its name there
    * (`KnownNames`).
    */
  def printed[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      known: KnownNames[C]
  )(using
      C,
      StorageAccess
  ): Printed[C] =
    printedWith(instruction, map, None, true, known, Set.empty, Reading.Display)

  /** `printed` with the instructions `inlined` holds written in place wherever
    * they occur, not bound, though the term refers to them more than once: a
    * view's choice of the shared instructions a person has β-reduced into their
    * occurrences. The other shared instructions are chosen as SHARING says, so
    * an empty set prints as `printed(instruction, map, known)` does. An
    * instruction that `known` binds stays bound.
    */
  def printed[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      known: KnownNames[C],
      inlined: Set[Configured[C]]
  )(using C, StorageAccess): Printed[C] =
    printedWith(instruction, map, None, true, known, inlined, Reading.Display)

  /** The names a caller gives instructions for a person to read: the library
    * terms a trace's lemmas name (`com.yang_bo.gezi.rewritetrace.TraceText`, the names the
    * lemmas' texts use) or a start's bindings name, so that a step reads
    * `type_of x` where the term holds the library term type_of. The names
    * decide nothing. Each is a name (`NameSpelling.isName`), spelled as the
    * text that gave it writes it (a binder's `BinderOrigin.Written`, a lemma
    * text's names), and the printer writes it as it is. The escape turns a text
    * into a name, as `com.yang_bo.gezi.directorysugar.DirectoryTree` spells a file's name
    * (`NameSpelling.escaped`); a name is not escaped again, since a name is no
    * arbitrary text: an identifier allows no arbitrary character, as on the
    * JVM, and only a text is escaped into one, so that `$marker$name_at` is
    * never escaped twice into `$u0024marker$u0024name_at`.
    */
  enum KnownNames[C <: NativeSpecializer & Singleton]:

    /** Each instruction bound at the text's start by its name, as a shared
      * instruction is, however often the term refers to it: the text stays a
      * closed term that reads back as the instruction.
      */
    case Bound(names: Map[Configured[C], String])

    /** Each instruction written by its name where it occurs and never bound, as
      * an opaque instruction is: a text for a person, whose names a reader
      * would have to bind.
      */
    case Written(names: Map[Configured[C], String])

  /** The term printed with no names to name its binders from: a term no text
    * wrote, such as a program given as a de Bruijn term, whose every binder is
    * named `x` (with `_2`, `_3` and so on, as NAMES says, where it would equal
    * a name in scope). Not a fallback of `printed`, which names a binder from
    * its origin or throws: a term printed here has no origins, and the text it
    * gives is where its binders' names come from once read
    * (`com.yang_bo.gezi.locations.BinderOrigin.Written`). Throws `IllegalArgumentException`
    * for an instruction that is no closed term.
    */
  def printedNameless[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C, StorageAccess): Printed[C] =
    printedWith(
      instruction,
      SourceMap.unlocated,
      Some("x"),
      true,
      KnownNames.Bound(Map.empty),
      Set.empty,
      Reading.Display
    )

  /** `printedNameless`, each instruction `known` names called by its name there
    * (`KnownNames`).
    */
  def printedNameless[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      known: KnownNames[C]
  )(using
      C,
      StorageAccess
  ): Printed[C] =
    printedWith(
      instruction,
      SourceMap.unlocated,
      Some("x"),
      true,
      known,
      Set.empty,
      Reading.Display
    )

  /** `printedNameless` with no mark of a subterm's place (`Piece.At`): the text
    * of the exchange format (`ExchangeText`), which no view reads, so that the
    * places are not computed. The text, the bindings and the names are
    * `printedNameless`'s.
    */
  def printedNamelessUnmarked[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C, StorageAccess): Printed[C] =
    printedWith(
      instruction,
      SourceMap.unlocated,
      Some("x"),
      false,
      KnownNames.Bound(Map.empty),
      Set.empty,
      Reading.Display
    )

  /** `printedNamelessUnmarked` with the storages read as `reading` says
    * (`Reading`): the exchange format's text of a term under the display
    * reading, `ExchangeText.line`'s, and under the Scott ADT reading, the line
    * of a Scott ADT value's members, `ExchangeText.scottADTLine`'s.
    */
  private[frontend] def printedNamelessUnmarked[
      C <: NativeSpecializer & Singleton
  ](instruction: Configured[C], reading: Reading)(using
      C,
      StorageAccess
  ): Printed[C] =
    printedWith(
      instruction,
      SourceMap.unlocated,
      Some("x"),
      false,
      KnownNames.Bound(Map.empty),
      Set.empty,
      reading
    )

  /** The text of the answer line that holds both the Scott ADT values of an
    * output and its remainder: the choice of the `members`, read as Scott ADT
    * values (`Reading.ScottADT`), and the `remainder`, read as a display
    * (`Reading.Display`, every `∥ T` kept), the members first, one table for
    * the write, so that what the two parts refer to more than once is bound
    * once. A storage that both parts hold is two nodes, its Scott ADT layer and
    * its view. The members are given in the order the line writes them.
    */
  private[frontend] def printedMixedUnmarked[
      C <: NativeSpecializer & Singleton
  ](members: Vector[Configured[C]], remainder: Configured[C])(using
      C,
      StorageAccess
  ): Printed[C] =
    val table = tabled(
      members.map((Reading.ScottADT, _)) :+ ((Reading.Display, remainder)),
      true
    )
    printedOver(
      table,
      remainder,
      SourceMap.unlocated,
      Some("x"),
      false,
      KnownNames.Bound(Map.empty),
      Set.empty
    )

  /** The lambdalattice text of one Scott ADT value written alone, each storage
    * in it read as its untyped Scott ADT layer and each parallel node `v ∥ E`
    * as v, every occurrence written where it occurs (no sharing): the key the
    * members of a line are ordered by, `Lambdalattice.text` of the term the
    * front end's readback gives for the member. It is the text of the member's
    * own term, which a caller that holds the member as a tree sorts by.
    */
  def scottADTText[C <: NativeSpecializer & Singleton](
      member: Configured[C]
  )(using C, StorageAccess): String =
    val table = tabled(member, Reading.ScottADT)
    val term = spelledReadback(
      table.objectOf(table.roots.head),
      SourceMap.unlocated,
      Set.empty,
      Writing(Reading.ScottADT, table.passedUnder(Reading.ScottADT))
    )._1
    Lambdalattice.text(term, Map.empty)

  /** The term read from the source text written back in the printer's layout,
    * for a formatter: as `printed`, but every occurrence written where it
    * occurs, no instruction bound however often it occurs, since whether a
    * repetition is bound is part of the text a formatter keeps, each binder
    * named by the name the text writes at that occurrence, renamed for no other
    * binder, and each literal spelled as the text spells it, a bit or a partial
    * function's level that no literal of the text spells written as a term, so
    * that every character-level choice of the text, its names and its comments
    * included, is kept. `map` is the map of the instruction's occurrence in the
    * text (`Defunctionalization.locatedThunkInstruction`), whose readback is
    * the text's own tree; its first `enclosing` abstractions are those of the
    * names the text is read under (`Lambdalattice.locatedInScope`), not
    * written, their names in scope. Each name and literal the text spells is
    * marked where the text spells it (`Piece.Source`). Throws
    * `IllegalArgumentException` for a term with fewer than `enclosing`
    * abstractions at its root and for a binder with no origin.
    */
  def writtenBack[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      source: SourceText,
      enclosing: Int
  )(using C, StorageAccess): Printed[C] =
    val (readback, binders, _) =
      Defunctionalization.locatedInstructionTerm(instruction, map, Set.empty)
    val term =
      constantsConverted(readback, Map.empty[Configured[C], NodeId]).result
    val context = Context[C](
      Map.empty,
      Set.empty,
      topWritten[C](
        None,
        Defunctionalization.instructionTerm(topInstruction(summon[C])),
        Map.empty
      ),
      None,
      Some(source)
    )
    val (body, path, scope) = (1 to enclosing).foldLeft(
      (
        term,
        TermPath.root(PlaceTree.Empty, binders),
        Scope[C](Vector.empty, Set.empty, Set.empty)
      )
    ) {
      // An enclosing name keeps its spelling where a nearer enclosing name
      // has it too (a directory named as one it is under): the text sees the
      // nearer one only, as it was read.
      case ((DeBruijnTerm.Lambda(inner), at, outer), _) =>
        (
          inner,
          at.below(0),
          outer.bound(
            binderName(
              originNames(at.binders.nodeOrigins, at.steps),
              outer.copy(taken = Set.empty)
            )._1
          )
        )
      case ((other, at, _), _) =>
        throw IllegalArgumentException(
          s"no enclosing abstraction at ${at.steps}: $other"
        )
    }
    val pieces = rendered(
      body,
      path,
      scope,
      Position.Whole,
      false,
      Vector.empty,
      List.empty,
      context
    ).result.reverse.toVector
    Printed[C](pieces, 0, instruction, Map.empty, Vector.empty)

  /** The binding the printer writes at the root of a text, `(λt. t V) λm.
    * BODY`, read back and contracted with its map (two β steps): BODY with V in
    * place of m, its binders' origins kept and V's places taking V's map, as
    * the defunctionalized β rule leaves the residue and the front end spells it
    * (`Defunctionalization.relocatedMap`); none for a root of another shape.
    */
  def contracted[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap
  )(using
      specializer: C
  ): Option[(Configured[C], SourceMap)] =
    instruction match
      case AppliedTerm(
            helper @ ThunkTerm(_, Vector(_), Vector(value)),
            ThunkTerm(code, Hole.Bound(slot) +: rest, fillings)
          )
          if Defunctionalization.instructionTerm(helper) ==
            DeBruijnTerm.Lambda(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Variable(0),
                Defunctionalization.instructionTerm(value)
              )
            ) =>
        val helperMap = map.children.lift(0).getOrElse(SourceMap.unlocated)
        val valueMap = helperMap.children.lift(0).getOrElse(SourceMap.unlocated)
        val bodyMap = map.children.lift(1).getOrElse(SourceMap.unlocated)
        val position = Defunctionalization.fillingPosition(rest, slot)
        val residue = thunkOrInstance(
          code,
          rest,
          fillings.patch(position, Vector(value), 0)
        )
        val residueMap = SourceMap(
          bodyMap.locations,
          bodyMap.code,
          bodyMap.children
            .padTo(fillings.size, SourceMap.unlocated)
            .patch(position, Vector(valueMap), 0),
          bodyMap.binders.drop(1)
        )
        // The readback keeps a storage as a constant and every parallel it holds is the residue's own.
        val spelled = Defunctionalization.thunkInstruction[C](
          Defunctionalization.instructionTerm(residue)
        )
        Some(
          (
            spelled,
            Defunctionalization.relocatedMap(residue, residueMap, spelled)
          )
        )
      case _ => None

  /** The application of a term of the configuration, and its two parts. */
  private object AppliedTerm:
    def unapply[C <: NativeSpecializer & Singleton](
        term: Configured[C]
    ): Option[(Configured[C], Configured[C])] = term.layer match
      case com.yang_bo.gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                 => None

  /** The thunk of a term of the configuration, and its parts. */
  private object ThunkTerm:
    def unapply[C <: NativeSpecializer & Singleton](
        term: Configured[C]
    ): Option[(Code, Vector[Hole], Vector[Configured[C]])] =
      term.layer match
        case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
          Some((code, holes, fillings))
        case _ => None

  /** The thunk of the code over the holes, or, with no hole, the instance of
    * the code over its fillings: a term has no thunk without holes.
    */
  private def thunkOrInstance[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Configured[C]]
  )(using specializer: C): Configured[C] =
    specializer.thunkOrInstance(code, holes, fillings)

  /** `printed`, a binder with no origin named `unnamed` when it is given, each
    * subterm's place marked when `marked` holds, the instructions `inlined`
    * holds never chosen as shared, the storages read as `reading` says. The
    * instructions are counted, hashed and named as the nodes of the table of
    * this one write (`tabled`), not as the objects they are.
    */
  private def printedWith[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      unnamed: Option[String],
      marked: Boolean,
      known: KnownNames[C],
      inlined: Set[Configured[C]],
      reading: Reading
  )(using C, StorageAccess): Printed[C] =
    printedOver(
      tabled(instruction, reading),
      instruction,
      map,
      unnamed,
      marked,
      known,
      inlined
    )

  /** `printedWith` over the table of the write, `instruction` the term
    * `Printed.root` names.
    */
  private def printedOver[C <: NativeSpecializer & Singleton](
      table: Table[C],
      instruction: Configured[C],
      map: SourceMap,
      unnamed: Option[String],
      marked: Boolean,
      known: KnownNames[C],
      inlined: Set[Configured[C]]
  )(using C, StorageAccess): Printed[C] =
    val (boundNames, writtenNames) = known match
      case KnownNames.Bound(names) => (names, Map.empty[Configured[C], String])
      case KnownNames.Written(names) =>
        (Map.empty[Configured[C], String], names)
    val bound = boundNames.flatMap((term, name) =>
      table.representativeOf(term).map(_ -> name)
    )
    val written = writtenNames.flatMap((term, name) =>
      table.representativeOf(term).map(_ -> name)
    )
    val inlinedNodes = inlined.flatMap(table.representativeOf)
    val inner = innerLevels(table)
    val shared = table.order.filter(node =>
      (table.counts.getOrElse(node, 0) > 1 || bound.contains(node)) && !table
        .named(node) &&
        !written.contains(node) && !table.literalParts.contains(node) && !inner
          .contains(node) &&
        !(inlinedNodes.contains(node) && !bound.contains(node))
    )
    printedSharing(
      instruction,
      map,
      table,
      shared,
      contentHashes(table),
      unnamed,
      marked,
      bound,
      written
    )

  /** The origins and locations of a readback's nodes: `Unknown` for the
    * readback of an unlocated map, whose every node has none, so that looking a
    * node up does not walk its path from the root.
    */
  private def readbackBinders(map: SourceMap, binders: TermMap): TermMap =
    if map == SourceMap.unlocated then TermMap.Unknown else binders

  /** The term printed with the shared instructions bound, where the written
    * text refers to each of them more than once; else printed again with those
    * it refers to once written in place. Such an instruction is top, which the
    * IR refers to inside complete literals as well, references the literals'
    * notation does not write. The shared instructions only decrease, so the
    * printing ends. `shared`, `bound` and `written` are nodes of the table,
    * each standing for all the objects of its class.
    */
  @scala.annotation.tailrec
  private def printedSharing[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      table: Table[C],
      shared: Vector[NodeId],
      hashes: Map[NodeId, Int],
      unnamed: Option[String],
      marked: Boolean,
      bound: Map[NodeId, String],
      written: Map[NodeId, String]
  )(using C, StorageAccess): Printed[C] =
    val sharedSet = shared.toSet
    // The instructions written as names: the shared ones and the known ones
    // written by name, each a constant of the terms the renderer writes, a
    // node of the table.
    val stopNodes = sharedSet ++ written.keySet
    def stopsUnder(reading: Reading): Set[Configured[C]] =
      table.objectsOf(reading, stopNodes)
    val nodeNames = constantsNamed(table, shared, hashes, bound, written)
    val reserved = nodeNames.values.toSet
    // The readback of a node under the reading it was met under, its stops
    // the nodes written as names, its constants renamed to nodes.
    def read(
        node: NodeId,
        nodeMap: SourceMap
    ): (Term[C], TermMap, Map[NodeId, SourceMap]) =
      val (reading, source) = table.origins(node)
      val (term, binders, stopMaps) = spelledReadback(
        source,
        nodeMap,
        stopsUnder(reading),
        Writing(reading, table.passedUnder(reading))
      )
      (
        constantsConverted(term, table.renaming(reading)).result,
        binders,
        table.nodeMaps(reading, stopMaps)
      )
    val parts = table.roots.map(root =>
      if table.roots.size > 1 && stopNodes.contains(root) then
        (
          DeBruijnTerm.Constant(root): Term[C],
          TermMap.Unknown,
          Map.empty[NodeId, SourceMap]
        )
      else read(root, map)
    )
    val body = parts
      .map(_._1)
      .reduceRight((left, right) => DeBruijnTerm.Choice(left, right))
    val bodyBinders = if parts.size == 1 then parts.head._2 else TermMap.Unknown
    val bodyNodeMaps = parts.foldLeft(Map.empty[NodeId, SourceMap]) {
      case (found, (_, _, partMaps)) =>
        partMaps.foldLeft(found) { case (joined, (stop, stopMap)) =>
          joined.updated(
            stop,
            joined.get(stop).fold(stopMap)(_.merged(stopMap))
          )
        }
    }
    // A shared instruction is referred to only by the body and by the shared
    // instructions bound after it, so its maps are all known once those are
    // read.
    val (boundValues, _) =
      shared.foldRight((List.empty[Bound[C]], bodyNodeMaps)) {
        case (value, (later, maps)) =>
          val valueMap = maps.getOrElse(value, SourceMap.unlocated)
          val (term, binders, stopMaps) = read(value, valueMap)
          val joined = stopMaps.foldLeft(maps) {
            case (found, (stop, stopMap)) =>
              found.updated(
                stop,
                found.get(stop).fold(stopMap)(_.merged(stopMap))
              )
          }
          val name = nodeNames(value)
          val places = if marked then
            placed(
              table.objectOf(value),
              stopsUnder(table.defaultReading),
              Some(name)
            )
          else PlaceTree.Empty
          (
            Bound(
              name,
              term,
              readbackBinders(valueMap, binders),
              places,
              table.objectOf(value),
              valueMap
            ) :: later,
            joined
          )
      }
    val bodyPlaces = if marked then
      placed(instruction, stopsUnder(table.defaultReading), None)
    else PlaceTree.Empty
    val top = topInstruction(summon[C]: C)
    val topTerms = topWritten[C](
      table.representativeOf(top).filter(stopNodes.contains),
      Defunctionalization
        .instructionTerm(top, stopsUnder(table.defaultReading)),
      table.renaming(table.defaultReading)
    )
    val context = Context[C](nodeNames, reserved, topTerms, unnamed, None)
    val bodyRoot = TermPath.root(bodyPlaces, readbackBinders(map, bodyBinders))
    val (kept, references) =
      referenced(boundValues.toVector, body, bodyRoot.binders, context)
    val once = shared.filter(value =>
      !bound.contains(value) && references.get(nodeNames(value)).contains(1)
    )
    if once.nonEmpty then
      printedSharing(
        instruction,
        map,
        table,
        shared.filterNot(once.toSet),
        hashes,
        unnamed,
        marked,
        bound,
        written
      )
    else
      val pieces = bindingsWritten(
        kept,
        fresh("t", reserved),
        body,
        bodyRoot,
        context
      ).result.reverse.toVector
      Printed[C](
        pieces,
        kept.size,
        instruction,
        table.objectNames(
          nodeNames.filter((node, _) => sharedSet.contains(node))
        ),
        kept.map(binding =>
          SharedValue[C](binding.name, binding.instruction, binding.map)
        )
      )

  // ---- the table of one write ----

  /** How the printer reads a native storage, which is a leaf of its term's
    * layer (`Configured.layer`): the one place a storage's content is read, one
    * layer at a time, as the formatter that writes text recurses.
    */
  private[frontend] enum Reading:

    /** A storage is written as its view `value ∥ criterion` (`viewOf`), the
      * term it stands for, every `∥ T` kept: the display of any term, the
      * remainder of an output.
      */
    case Display

    /** A storage is written as its untyped Scott ADT layer
      * `λc1 … ck. ci f1 … fn` (`scottReadingOf`), its fields written
      * recursively, and a parallel node `v ∥ E` as v: a Scott ADT value of the
      * line's members. The layer of a storage is the layer
      * `Defunctionalization` spells for the same term (the code, the holes and
      * the closed fields as fillings, equal fields one slot), so that it has
      * the content hash and the name the same term spelled by the front end
      * has.
      */
    case ScottADT

  /** A node of the table of one write: the formatter's own value, the index of
    * the node among the nodes of the table, not a term of the IR. Every count,
    * hash, name and sharing of a write is that of a node, and the constants of
    * the terms the renderer writes are nodes.
    */
  private final case class NodeId(number: Int)

  /** One layer as the printer writes it, over parts of type `Child` (the
    * objects of the walk, then the nodes of the table): the layer of an
    * instruction, a storage's view as the parallel it is written as
    * (`Reading.Display`), or a storage's Scott ADT layer (`Fielded`, which the
    * table respells as the thunk it stands for).
    */
  private enum WrittenLayer[C <: NativeSpecializer & Singleton, Child]:
    case Leaf(term: Configured[C])
    case Applied(function: Child, argument: Child)
    case Chosen(left: Child, right: Child)
    case Paralleled(left: Child, right: Child)
    case Abstracted(code: Code, holes: Vector[Hole], fillings: Vector[Child])

    /** A storage read as `λc1 … ck. ci f1 … fn`: k cases, the chosen case i
      * from 0, the fields in order.
      */
    case Fielded(cases: Int, chosen: Int, fields: Vector[Child])

    /** Every part the layer holds, whether the text refers to it or not. */
    def allChildren: Vector[Child] = this match
      case Leaf(_)                     => Vector.empty
      case Applied(function, argument) => Vector(function, argument)
      case Chosen(left, right)         => Vector(left, right)
      case Paralleled(left, right)     => Vector(left, right)
      case Abstracted(_, _, fillings)  => fillings
      case Fielded(_, _, fields)       => fields

    /** The layer over the parts the function gives for the ones it holds. */
    def mapped[Other](change: Child => Other): WrittenLayer[C, Other] =
      this match
        case Leaf(term)                  => Leaf(term)
        case Applied(function, argument) =>
          Applied(change(function), change(argument))
        case Chosen(left, right)     => Chosen(change(left), change(right))
        case Paralleled(left, right) => Paralleled(change(left), change(right))
        case Abstracted(code, holes, fillings) =>
          Abstracted(code, holes, fillings.map(change))
        case Fielded(cases, chosen, fields) =>
          Fielded(cases, chosen, fields.map(change))

  /** What two nodes of the table have in common when they are one: the kind of
    * layer and the numbers of its parts, so that two layers over the same parts
    * are one node whichever objects they are. A leaf is its own number.
    */
  private enum NodeKey:
    case Leaf(number: Int)
    case Applied(function: Int, argument: Int)
    case Chosen(left: Int, right: Int)
    case Paralleled(left: Int, right: Int)
    case Abstracted(code: Code, holes: Vector[Hole], fillings: Vector[Int])

  /** The table of one write: the nodes of the terms the printer writes,
    * identified by their layer and their parts, so that the count of the
    * references to a closed instruction, its content hash and its name are
    * those of the interned term the text stands for, whether its parts are
    * storages or the terms the storages are written as. It is the interning of
    * the layers the formatter reads and gives, private to the write (the
    * formatter builds no IR). A node is named by a `NodeId` and read from the
    * first object of its class in the order of the walk, under the reading it
    * was met under. A write may hold roots read under both readings (the line
    * of Scott ADT values and a remainder); an object is then met under each
    * reading and a node is the pair of the reading and the object, so that a
    * storage both parts hold is two nodes.
    *
    * @param defaultReading
    *   the reading of the first root, for the callers that give the objects of
    *   one reading only
    * @param roots
    *   the node of each root, in order
    * @param representative
    *   the node each object met under a reading stands for, a parallel node the
    *   Scott ADT reading passes through standing for the node of its left side
    * @param origins
    *   the reading and the first object each node is read from
    * @param nodes
    *   the layer of each node over nodes; a storage's Scott ADT layer as the
    *   thunk the front end spells for it
    * @param order
    *   the nodes, each after those its layer refers to
    * @param counts
    *   the times each node is referred to by the nodes above it, a filling
    *   counted as often as its code writes its slot, and each root once more
    *   when the roots are the members of a choice
    * @param passed
    *   the parallel nodes the Scott ADT reading passed through
    * @param literalParts
    *   the nodes that are a bit or an application whose last argument is a bit
    */
  private final case class Table[C <: NativeSpecializer & Singleton](
      defaultReading: Reading,
      roots: Vector[NodeId],
      representative: Map[(Reading, Configured[C]), NodeId],
      origins: Map[NodeId, (Reading, Configured[C])],
      nodes: Map[NodeId, WrittenLayer[C, NodeId]],
      order: Vector[NodeId],
      counts: Map[NodeId, Int],
      passed: Map[Reading, Set[Configured[C]]],
      literalParts: Set[NodeId]
  ):

    /** Whether the node is written as a name of the term itself: an opaque term
      * of the IR.
      */
    def named(node: NodeId): Boolean = nodes(node) match
      case WrittenLayer.Leaf(_) => true
      case _                    => false

    /** The first object the node is read from, under its own reading. */
    def objectOf(node: NodeId): Configured[C] = origins(node)._2

    /** The parallel nodes passed through under the reading. */
    def passedUnder(reading: Reading): Set[Configured[C]] =
      passed.getOrElse(reading, Set.empty)

    /** The node an object stands for under the default reading, none for an
      * object the walk did not meet.
      */
    def representativeOf(term: Configured[C]): Option[NodeId] =
      representative.get((defaultReading, term))

    /** The objects met under the reading that stand for one of the nodes. */
    def objectsOf(reading: Reading, selected: Set[NodeId]): Set[Configured[C]] =
      representative.collect {
        case ((read, term), node)
            if read == reading && selected.contains(node) =>
          term
      }.toSet

    /** The node each object met under the reading stands for. */
    def renaming(reading: Reading): Map[Configured[C], NodeId] =
      representative.collect {
        case ((read, term), node) if read == reading => term -> node
      }

    /** The name of each object of the default reading that stands for a named
      * node.
      */
    def objectNames(names: Map[NodeId, String]): Map[Configured[C], String] =
      representative.collect {
        case ((read, term), node)
            if read == defaultReading && names.contains(node) =>
          term -> names(node)
      }

    /** The maps of the objects joined by their nodes, the maps of one node
      * merged.
      */
    def nodeMaps(
        reading: Reading,
        maps: Map[Configured[C], SourceMap]
    ): Map[NodeId, SourceMap] =
      maps.foldLeft(Map.empty[NodeId, SourceMap]) { case (found, (term, map)) =>
        val node = representative((reading, term))
        found.updated(node, found.get(node).fold(map)(_.merged(map)))
      }

  /** The table of the write of the roots, each under its reading (a choice's
    * members when `chained`). Each distinct object is walked once under each
    * reading, depth first, in the order the references are written, a storage
    * read one layer when it is met; each is then given the node of the first
    * object whose layer has the same parts, its parts being nodes already given
    * (the objects are met after their parts). A storage read as a Scott ADT
    * layer is respelled as the front end spells it: its distinct fields, in
    * order of first occurrence, the fillings, the code reading the field's slot
    * at each occurrence.
    */
  private def tabled[C <: NativeSpecializer & Singleton](
      roots: Vector[(Reading, Configured[C])],
      chained: Boolean
  )(using
      specializer: C,
      access: StorageAccess
  ): Table[C] =
    val readings = roots.map(_._1).distinct
    val resolvedRoots = roots.map((reading, root) =>
      (reading, resolvedThrough(root, reading, Vector.empty))
    )
    // Phase one, under each reading: the objects, each after those it refers to, and the layer of each over the objects
    // it refers to.
    @scala.annotation.tailrec
    def walked(
        reading: Reading,
        pending: List[(Configured[C], Boolean)],
        visited: Set[Configured[C]],
        found: Vector[Configured[C]],
        layers: Map[Configured[C], WrittenLayer[C, Configured[C]]],
        through: Map[Configured[C], Configured[C]]
    ): (
        Vector[Configured[C]],
        Map[Configured[C], WrittenLayer[C, Configured[C]]],
        Map[Configured[C], Configured[C]]
    ) =
      pending match
        case Nil                  => (found, layers, through)
        case (term, true) :: rest =>
          walked(reading, rest, visited, found :+ term, layers, through)
        case (term, false) :: rest if visited.contains(term) =>
          walked(reading, rest, visited, found, layers, through)
        case (term, false) :: rest =>
          val (layer, passed) = layerRead(term, reading)
          val children = referred(layer).map((child, _) => (child, false))
          walked(
            reading,
            children.toList ++ ((term, true) :: rest),
            visited + term,
            found,
            layers.updated(term, layer),
            through ++ passed
          )
    val walks = readings.map { reading =>
      val starts = resolvedRoots.filter(_._1 == reading).map(_._2)
      val startPassed =
        starts.flatMap((start, passed) => passed.map(_ -> start)).toMap
      reading -> walked(
        reading,
        starts.map((start, _) => (start, false)).toList,
        Set.empty,
        Vector.empty,
        Map.empty,
        startPassed
      )
    }.toMap
    // Phase two: the nodes, the readings one after the other.
    val entries = readings.flatMap(reading =>
      walks(reading)._1.map(term => (reading, term))
    )
    val classes = entries.foldLeft(Classes.empty[C]) {
      case (sofar, (reading, term)) =>
        val layer = respelled(
          walks(reading)
            ._2(term)
            .mapped(child => sofar.representative((reading, child)))
        )
        // An opaque term met under both readings is one node.
        val key = layer match
          case WrittenLayer.Leaf(leaf) =>
            NodeKey.Leaf(
              sofar.leaves.get(leaf).fold(sofar.order.size)(_.number)
            )
          case other => keyOf(other)
        sofar.byKey.get(key) match
          case Some(node) =>
            sofar.copy(representative =
              sofar.representative.updated((reading, term), node)
            )
          case None =>
            val node = NodeId(sofar.order.size)
            Classes(
              sofar.representative.updated((reading, term), node),
              sofar.byKey.updated(key, node),
              sofar.keys.updated(node, key),
              sofar.nodes.updated(node, layer),
              sofar.order :+ node,
              sofar.origins.updated(node, (reading, term)),
              layer match
                case WrittenLayer.Leaf(leaf) => sofar.leaves.updated(leaf, node)
                case _                       => sofar.leaves
            )
    }
    val representative = classes.representative ++ readings.flatMap(reading =>
      walks(reading)._3.map((parallel, target) =>
        (reading, parallel) -> classes.representative((reading, target))
      )
    )
    val rootNodes = resolvedRoots.map((reading, resolution) =>
      representative((reading, resolution._1))
    )
    val referenceCounts = classes.order.foldLeft(Map.empty[NodeId, Int]) {
      (sofar, node) =>
        referred(classes.nodes(node)).foldLeft(sofar) {
          case (before, (child, times)) =>
            before.updated(child, before.getOrElse(child, 0) + times)
        }
    }
    val counts = if chained then
      rootNodes.foldLeft(referenceCounts)((sofar, node) =>
        sofar.updated(node, sofar.getOrElse(node, 0) + 1)
      )
    else referenceCounts
    val bitKeys: Set[NodeKey] = bitInstructions(specializer).flatMap(bit =>
      bit.layer match
        case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) if fillings.isEmpty =>
          Some(NodeKey.Abstracted(code, holes, Vector.empty))
        case _ => None
    )
    val bitNumbers = classes.order
      .filter(node => bitKeys.contains(classes.keys(node)))
      .map(_.number)
      .toSet
    val literalParts = classes.order
      .filter(node =>
        classes.keys(node) match
          case key if bitKeys.contains(key) => true
          case NodeKey.Applied(_, argument) => bitNumbers.contains(argument)
          case _                            => false
      )
      .toSet
    Table(
      readings.head,
      rootNodes,
      representative,
      classes.origins,
      classes.nodes,
      classes.order,
      counts,
      walks.view.mapValues(_._3.keySet).toMap,
      literalParts
    )

  /** The table of the write of one root under the reading. */
  private def tabled[C <: NativeSpecializer & Singleton](
      root: Configured[C],
      reading: Reading
  )(using C, StorageAccess): Table[C] =
    tabled(Vector((reading, root)), false)

  /** The nodes given so far, by the numbers of their parts. */
  private final case class Classes[C <: NativeSpecializer & Singleton](
      representative: Map[(Reading, Configured[C]), NodeId],
      byKey: Map[NodeKey, NodeId],
      keys: Map[NodeId, NodeKey],
      nodes: Map[NodeId, WrittenLayer[C, NodeId]],
      order: Vector[NodeId],
      origins: Map[NodeId, (Reading, Configured[C])],
      leaves: Map[Configured[C], NodeId]
  )

  private object Classes:
    def empty[C <: NativeSpecializer & Singleton]: Classes[C] =
      Classes(
        Map.empty,
        Map.empty,
        Map.empty,
        Map.empty,
        Vector.empty,
        Map.empty,
        Map.empty
      )

  /** The term the reading reads the term as, and the parallel nodes it passes
    * through: under the Scott ADT reading a parallel node `v ∥ E` is v; the
    * display reads every term as itself.
    */
  @scala.annotation.tailrec
  private def resolvedThrough[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      reading: Reading,
      passed: Vector[Configured[C]]
  ): (Configured[C], Vector[Configured[C]]) =
    reading match
      case Reading.Display  => (term, passed)
      case Reading.ScottADT =>
        term.layer match
          case com.yang_bo.gezi.ir.Parallel(left, _) =>
            resolvedThrough(left, reading, passed :+ term)
          case _ => (term, passed)

  /** The layer of the object as the reading writes it, over the terms the
    * reading reads its parts as, and each parallel node passed through on the
    * way to a part, with the part it stands for. A storage is read one layer
    * here and nowhere else.
    */
  private def layerRead[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      reading: Reading
  )(using
      specializer: C,
      access: StorageAccess
  ): (WrittenLayer[C, Configured[C]], Vector[(Configured[C], Configured[C])]) =
    val layer: WrittenLayer[C, Configured[C]] =
      if term.opaque then WrittenLayer.Leaf(term)
      else
        term.layer match
          case storage: NativeStorage =>
            reading match
              case Reading.Display =>
                val view = (specializer: C).viewOf(storage)
                WrittenLayer.Paralleled(view.value, view.criterion)
              case Reading.ScottADT =>
                (specializer: C).scottReadingOf(storage) match
                  case ScottReading.Layer(cases, chosen, fields) =>
                    WrittenLayer.Fielded(cases, chosen, fields)
                  case ScottReading.Members(_) =>
                    throw IllegalStateException(
                      s"a group of storages stands below the top of a member: `ScottADTChoices.of` splits a group and never leaves one under a constructor, so this member is no `ScottADTChoices` member: $term"
                    )
          case com.yang_bo.gezi.ir.Apply(function, argument) =>
            WrittenLayer.Applied(function, argument)
          case com.yang_bo.gezi.ir.Choice(left, right)   => WrittenLayer.Chosen(left, right)
          case com.yang_bo.gezi.ir.Parallel(left, right) =>
            WrittenLayer.Paralleled(left, right)
          case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
            WrittenLayer.Abstracted(code, holes, fillings)
          case other => throw IllegalStateException(s"no layer to walk: $other")
    val resolutions = layer.allChildren.map(child =>
      child -> resolvedThrough(child, reading, Vector.empty)
    )
    val targets =
      resolutions.map((child, resolution) => child -> resolution._1).toMap
    (
      layer.mapped(targets),
      resolutions.flatMap((_, resolution) =>
        resolution._2.map(_ -> resolution._1)
      )
    )

  /** The layer of a node over nodes: a storage's Scott ADT layer respelled as
    * the thunk the front end spells for `λc1 … ck. ci f1 … fn`, whose code
    * applies the slot of the chosen case's binder, slot 0, to the slot of each
    * field in turn, a field's slot numbered by its first occurrence, one slot
    * for equal fields, the chosen case's binder the only one read and so the
    * only hole that is not ignored (`Defunctionalization.thunkInstruction`).
    * The fields are already nodes.
    */
  private def respelled[C <: NativeSpecializer & Singleton](
      layer: WrittenLayer[C, NodeId]
  ): WrittenLayer[C, NodeId] =
    layer match
      case WrittenLayer.Fielded(cases, chosen, fields) =>
        val (fillings, slots) =
          fields.foldLeft((Vector.empty[NodeId], Map.empty[NodeId, Int])) {
            case ((kept, numbered), field) =>
              if numbered.contains(field) then (kept, numbered)
              else (kept :+ field, numbered.updated(field, kept.size + 1))
          }
        val code = fields.foldLeft(Code.Slot(0): Code)((function, field) =>
          Code.Apply(function, Code.Slot(slots(field)))
        )
        val holes = Vector.tabulate(cases)(position =>
          if position == chosen then Hole.Bound(0) else Hole.Ignored
        )
        WrittenLayer.Abstracted(code, holes, fillings)
      case other => other

  /** The key of a node that is no leaf, from the numbers of its parts. */
  private def keyOf[C <: NativeSpecializer & Singleton](
      layer: WrittenLayer[C, NodeId]
  ): NodeKey = layer match
    case WrittenLayer.Leaf(_) =>
      throw IllegalStateException("a leaf is keyed by the table")
    case WrittenLayer.Applied(function, argument) =>
      NodeKey.Applied(function.number, argument.number)
    case WrittenLayer.Chosen(left, right) =>
      NodeKey.Chosen(left.number, right.number)
    case WrittenLayer.Paralleled(left, right) =>
      NodeKey.Paralleled(left.number, right.number)
    case WrittenLayer.Abstracted(code, holes, fillings) =>
      NodeKey.Abstracted(code, holes, fillings.map(_.number))
    case WrittenLayer.Fielded(_, _, _) =>
      throw IllegalStateException(
        "a storage's Scott ADT layer is respelled as a thunk before it is keyed"
      )

  /** The parts the layer refers to, each with the times the text writes it. A
    * storage refers to the two parts of its view, as the parallel the printer
    * writes for it does, or to its fields, as the thunk it is written as does.
    */
  private def referred[C <: NativeSpecializer & Singleton, Child](
      layer: WrittenLayer[C, Child]
  ): Vector[(Child, Int)] =
    layer match
      case WrittenLayer.Leaf(_)                     => Vector.empty
      case WrittenLayer.Applied(function, argument) =>
        Vector((function, 1), (argument, 1))
      case WrittenLayer.Chosen(left, right)     => Vector((left, 1), (right, 1))
      case WrittenLayer.Paralleled(left, right) => Vector((left, 1), (right, 1))
      case WrittenLayer.Fielded(_, _, fields)   => fields.map((_, 1))
      case WrittenLayer.Abstracted(code, holes, fillings) =>
        val reads = slotReads(code)
        val filledSlots =
          (0 until (holes.count(_ != Hole.Ignored) + fillings.size))
            .filterNot(slot => holes.contains(Hole.Bound(slot)))
        filledSlots
          .zip(fillings)
          .map((slot, filling) => (filling, reads.getOrElse(slot, 0)))
          .filter((_, times) => times > 0)
          .toVector

  // ---- sharing ----

  /** The term the renderer writes: its constants are the nodes of the table of
    * the write, which carry the names. The configuration `C` the term was read
    * under no longer shows in it.
    */
  private type Term[C <: NativeSpecializer & Singleton] = DeBruijnTermOf[NodeId]

  /** The readback of an instruction, its constants the objects of the walk
    * (`Defunctionalization.instructionTerm`).
    */
  private type Readback[C <: NativeSpecializer & Singleton] =
    DeBruijnTermOf[Configured[C]]

  /** A storage written out as its view `value ∥ criterion`, a parallel of its
    * two parts: the layer the printer writes for a storage, which is no layer
    * of the IR.
    */
  private final case class StoredParallel[+Child](
      value: Child,
      criterion: Child
  )

  /** The term's layer as the printer writes it: a storage is the parallel of
    * its view's two parts, every other term its own layer. The one place a
    * storage's view is read, one layer at a time, as the formatter that writes
    * text recurses over views.
    */
  private def layerOf[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): IrLayer[Configured[C]] | StoredParallel[Configured[C]] =
    term.layer match
      case storage: NativeStorage =>
        val view = (specializer: C).viewOf(storage)
        StoredParallel(view.value, view.criterion)
      case other => other

  /** The terms the layer written by the printer holds, in the order of
    * `Layer.children`.
    */
  private[frontend] def childrenOf[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using C, StorageAccess): Vector[Configured[C]] =
    term.layer match
      case storage: NativeStorage =>
        val view = (summon[C]: C).viewOf(storage)
        Vector(view.value, view.criterion)
      case other => other.children

  /** The terms the term holds under the reading: under `Reading.Display` those
    * of `childrenOf`; under `Reading.ScottADT` those of the term it is read as
    * (a parallel node `v ∥ E` is v), a storage's fields in order, a group of
    * storages its members.
    */
  private[frontend] def childrenOf[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      reading: Reading
  )(using
      specializer: C,
      access: StorageAccess
  ): Vector[Configured[C]] =
    reading match
      case Reading.Display  => childrenOf(term)
      case Reading.ScottADT =>
        val (read, _) = resolvedThrough(term, reading, Vector.empty)
        read.layer match
          case storage: NativeStorage =>
            (specializer: C).scottReadingOf(storage) match
              case ScottReading.Layer(_, _, fields) => fields
              case ScottReading.Members(members)    => members
          case other => other.children

  /** The parts of a parallel the printer writes: a parallel layer or a
    * storage's view.
    */
  private object WrittenParallel:
    def unapply[C <: NativeSpecializer & Singleton](
        layer: IrLayer[Configured[C]] | StoredParallel[Configured[C]]
    ): Option[(Configured[C], Configured[C])] =
      layer match
        case StoredParallel(value, criterion) => Some((value, criterion))
        case com.yang_bo.gezi.ir.Parallel(left, right)    => Some((left, right))
        case _                                => None

  /** What the readback writes out besides the instructions of the IR: how the
    * storages are read, and the parallel nodes the Scott ADT reading passes
    * through (a parallel node `v ∥ E` is read as v), each a constant of the
    * readback that the writer replaces by what it stands for.
    */
  private final case class Writing[C <: NativeSpecializer & Singleton](
      reading: Reading,
      passed: Set[Configured[C]]
  )

  /** The readback of the instruction with each storage that is no stop written
    * out as the reading says (its view `StoredParallel` under
    * `Reading.Display`, its untyped Scott ADT layer under `Reading.ScottADT`),
    * the term, its map and the maps of the stops met. A storage's parts have no
    * map.
    */
  private def spelledReadback[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      map: SourceMap,
      stops: Set[Configured[C]],
      writing: Writing[C]
  )(using
      C,
      StorageAccess
  ): (Readback[C], TermMap, Map[Configured[C], SourceMap]) =
    instruction.layer match
      case _: NativeStorage =>
        (
          storageWritten(instruction, stops, writing).result,
          TermMap.Unknown,
          Map.empty
        )
      case _ =>
        val (term, binders, stopMaps) = Defunctionalization
          .locatedInstructionTerm(instruction, map, stops ++ writing.passed)
        (storagesWritten(term, stops, writing).result, binders, stopMaps)

  /** The term with each constant that is a storage, or a parallel node the
    * reading passes through, and no stop replaced by what the reading writes
    * for it.
    */
  private def storagesWritten[C <: NativeSpecializer & Singleton](
      term: Readback[C],
      stops: Set[Configured[C]],
      writing: Writing[C]
  )(using
      C,
      StorageAccess
  ): TailRec[Readback[C]] =
    term match
      case DeBruijnTerm.Constant(constant) if stops.contains(constant) =>
        done(term)
      case DeBruijnTerm.Constant(constant) =>
        constant.layer match
          case _: NativeStorage =>
            tailcall(storageWritten(constant, stops, writing))
          case _ if writing.passed.contains(constant) =>
            tailcall(partWritten(constant, stops, writing))
          case _ => done(term)
      case DeBruijnTerm.Lambda(body) =>
        tailcall(storagesWritten(body, stops, writing)).map(
          DeBruijnTerm.Lambda(_)
        )
      case DeBruijnTerm.Apply(left, right) =>
        for
          leftWritten <- tailcall(storagesWritten(left, stops, writing));
          rightWritten <- tailcall(storagesWritten(right, stops, writing))
        yield DeBruijnTerm.Apply(leftWritten, rightWritten)
      case DeBruijnTerm.Choice(left, right) =>
        for
          leftWritten <- tailcall(storagesWritten(left, stops, writing));
          rightWritten <- tailcall(storagesWritten(right, stops, writing))
        yield DeBruijnTerm.Choice(leftWritten, rightWritten)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          leftWritten <- tailcall(storagesWritten(left, stops, writing));
          rightWritten <- tailcall(storagesWritten(right, stops, writing))
        yield DeBruijnTerm.Parallel(leftWritten, rightWritten)
      case _ => done(term)

  /** The term with each constant replaced by the node the names give it: the
    * readback's constants are the objects the walk met under the reading, and
    * the renderer writes nodes. Throws `IllegalStateException` for a constant
    * that is no object the walk met, which has no name.
    */
  private def constantsConverted[C <: NativeSpecializer & Singleton](
      term: Readback[C],
      nodes: Map[Configured[C], NodeId]
  ): TailRec[Term[C]] =
    term match
      case DeBruijnTerm.Constant(constant) =>
        done(
          DeBruijnTerm.Constant(
            nodes.getOrElse(
              constant,
              throw IllegalStateException(s"no name for $constant")
            )
          )
        )
      case DeBruijnTerm.Lambda(body) =>
        tailcall(constantsConverted(body, nodes)).map(DeBruijnTerm.Lambda(_))
      case DeBruijnTerm.Apply(left, right) =>
        for
          leftConverted <- tailcall(constantsConverted(left, nodes));
          rightConverted <- tailcall(constantsConverted(right, nodes))
        yield DeBruijnTerm.Apply(leftConverted, rightConverted)
      case DeBruijnTerm.Choice(left, right) =>
        for
          leftConverted <- tailcall(constantsConverted(left, nodes));
          rightConverted <- tailcall(constantsConverted(right, nodes))
        yield DeBruijnTerm.Choice(leftConverted, rightConverted)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          leftConverted <- tailcall(constantsConverted(left, nodes));
          rightConverted <- tailcall(constantsConverted(right, nodes))
        yield DeBruijnTerm.Parallel(leftConverted, rightConverted)
      case DeBruijnTerm.Variable(index) =>
        done(DeBruijnTerm.Variable[NodeId](index))
      case DeBruijnTerm.Free(name) => done(DeBruijnTerm.Free(name))

  /** A part of a storage, or a parallel node the Scott ADT reading passes
    * through, written out: a stop a constant, a storage as the reading writes
    * it, a parallel node (under the Scott ADT reading) as its left side, any
    * other instruction by its readback with every storage in it written out in
    * turn.
    */
  private def partWritten[C <: NativeSpecializer & Singleton](
      side: Configured[C],
      stops: Set[Configured[C]],
      writing: Writing[C]
  )(using
      C,
      StorageAccess
  ): TailRec[Readback[C]] =
    if stops.contains(side) then done(DeBruijnTerm.Constant(side))
    else
      side.layer match
        case _: NativeStorage => tailcall(storageWritten(side, stops, writing))
        case com.yang_bo.gezi.ir.Parallel(left, _) if writing.reading == Reading.ScottADT =>
          tailcall(partWritten(left, stops, writing))
        case _ =>
          tailcall(
            storagesWritten(
              Defunctionalization
                .instructionTerm(side, stops ++ writing.passed),
              stops,
              writing
            )
          )

  /** The storage written out as the reading says, each part's readback with
    * every storage in it written out in turn, a part that is a stop a constant.
    * Under `Reading.Display` the parallel of its view's two parts. Under
    * `Reading.ScottADT` its untyped Scott ADT layer `λc1 … ck. ci f1 … fn`,
    * read one layer from its native data (`scottReadingOf`), its fields written
    * recursively: the term the front end's readback gives the thunk of that
    * layer (`Defunctionalization.instructionTerm`), a field being closed and so
    * standing as it is under the binders.
    */
  private def storageWritten[C <: NativeSpecializer & Singleton](
      storage: Configured[C],
      stops: Set[Configured[C]],
      writing: Writing[C]
  )(using
      specializer: C,
      access: StorageAccess
  ): TailRec[Readback[C]] =
    writing.reading match
      case Reading.Display =>
        childrenOf(storage) match
          case Vector(value, criterion) =>
            for
              valueWritten <- tailcall(partWritten(value, stops, writing));
              criterionWritten <- tailcall(
                partWritten(criterion, stops, writing)
              )
            yield DeBruijnTerm.Parallel(valueWritten, criterionWritten)
          case other =>
            throw IllegalStateException(
              s"a storage's view has two parts, found $other"
            )
      case Reading.ScottADT =>
        storage.layer match
          case held: NativeStorage =>
            (specializer: C).scottReadingOf(held) match
              case ScottReading.Layer(cases, chosen, fields) =>
                Trampoline
                  .traversed(fields)(field =>
                    partWritten(field, stops, writing)
                  )
                  .map(parts =>
                    val applied = parts.foldLeft(
                      DeBruijnTerm.Variable[Configured[C]](
                        cases - 1 - chosen
                      ): Readback[C]
                    )(DeBruijnTerm.Apply(_, _))
                    (0 until cases).foldLeft(applied)((inner, _) =>
                      DeBruijnTerm.Lambda(inner)
                    )
                  )
              case ScottReading.Members(_) =>
                throw IllegalStateException(
                  s"a group of storages stands below the top of a member: `ScottADTChoices.of` splits a group and never leaves one under a constructor, so this member is no `ScottADTChoices` member: $storage"
                )
          case other =>
            throw IllegalStateException(s"no storage to write: $other")

  /** Whether the instruction is a bit or an application whose last argument is
    * a bit: part of a literal of arguments, never shared.
    */
  private[frontend] def literalPart[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using specializer: C): Boolean =
    val bits = bitInstructions(specializer: C)
    bits.contains(instruction) || (instruction.layer match
      case com.yang_bo.gezi.ir.Apply(_, argument) => bits.contains(argument)
      case _                          => false)

  /** The levels of the variable arguments partial functions under the root that
    * are the rest of another level: never shared, so that sharing never cuts a
    * partial function's literal in two (two literals that end alike end in one
    * level, as `"$name"` and `"$closure"` before the body `λv. v`). A partial
    * function's first level is the whole function and is shared as any
    * instruction.
    */
  private def innerLevels[C <: NativeSpecializer & Singleton](
      table: Table[C]
  )(using C): Set[NodeId] =
    table.order
      .flatMap(node =>
        val (reading, source) = table.origins(node)
        levelRest(source).collect {
          case DeBruijnTerm.Constant(rest) if levelRest(rest).nonEmpty =>
            table.representative.get((reading, rest))
        }.flatten
      )
      .toSet

  /** The rest of a level of a variable arguments partial function,
    * `λx. x REST top` or `λx. x top REST`, as the level's term holds it: a
    * filling when it is closed.
    */
  private def levelRest[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C): Option[Readback[C]] =
    instruction.layer match
      case com.yang_bo.gezi.ir.Thunk(code, Vector(Hole.Bound(slot)), fillings)
          if levelShaped(code, slot) =>
        Defunctionalization.instructionTerm(instruction, fillings.toSet) match
          case DeBruijnTerm.Lambda(
                DeBruijnTerm.Apply(
                  DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), first),
                  second
                )
              ) =>
            if isTopForm(second) then Some(first)
            else if isTopForm(first) then Some(second)
            else None
          case _ => None
      case _ => None

  /** Whether the code of a thunk with one hole, bound to the slot, has a
    * level's shape `λx. x A B` at its root: the slot applied to two arguments.
    * A level's readback `λx. x REST top` has that shape, so a code without it
    * is no level, and `levelRest` reads it back only when it has it:
    * `innerLevels` asks for every instruction of the printed term, and reading
    * each back was 9.1% of TrapJudgmentsLawTest's JFR samples on 2026-11-20.
    */
  private def levelShaped(code: Code, slot: Int): Boolean = code.layer match
    case com.yang_bo.gezi.ir.Apply(applied, _) =>
      applied.layer match
        case com.yang_bo.gezi.ir.Apply(head, _) => head.layer == com.yang_bo.gezi.ir.Slot(slot)
        case _                      => false
    case _ => false

  /** top as a level of a partial function holds it: a filling, or written in
    * the level's code.
    */
  private def isTopForm[C <: NativeSpecializer & Singleton](term: Readback[C])(
      using specializer: C
  ): Boolean =
    term match
      case DeBruijnTerm.Constant(constant) =>
        Configured.same(constant, topInstruction(specializer))
      case other => other == topReadback

  /** The readback of top, which holds no constant, so that it is the same term
    * under every configuration.
    */
  private lazy val topReadback
      : DeBruijnTermOf[Configured[com.yang_bo.gezi.ir.NoFacts.type]] =
    Defunctionalization.instructionTerm[com.yang_bo.gezi.ir.NoFacts.type](
      Configured.fromPure(com.yang_bo.gezi.ir.NoFacts)(topPure)
    )(using com.yang_bo.gezi.ir.NoFacts)

  /** The pure term of top, the miss of a partial function's bit. */
  private lazy val topPure: com.yang_bo.gezi.ir.Pure =
    Defunctionalization.pure(Literals.top)

  /** The pure terms of the bits, `λt. λf. t` and `λt. λf. f`. */
  private lazy val bitPures: Set[com.yang_bo.gezi.ir.Pure] =
    Set(Literals.one, Literals.zero).map(Defunctionalization.pure(_))

  /** The instructions of the bits under the configuration. */
  private def bitInstructions[C <: NativeSpecializer & Singleton](
      specializer: C
  ): Set[Configured[C]] =
    bitPures.map(Configured.fromPure(specializer)(_))

  /** The instruction of top under the configuration. */
  private def topInstruction[C <: NativeSpecializer & Singleton](
      specializer: C
  ): Configured[C] =
    Configured.fromPure(specializer)(topPure)

  /** The terms top is written as: the constant of its node when top is one of
    * the shared nodes (`shared` gives that node), else its readback, whose
    * constants the renaming gives their nodes.
    */
  private def topWritten[C <: NativeSpecializer & Singleton](
      shared: Option[NodeId],
      readback: => Readback[C],
      renaming: Map[Configured[C], NodeId]
  ): Set[Term[C]] =
    shared match
      case Some(node) => Set(DeBruijnTerm.Constant(node))
      case None       => Set(constantsConverted(readback, renaming).result)

  /** The bindings some written text refers to: the body's, or a kept later
    * binding's, a binding referring only to those before it; and the times the
    * written text refers to each name of a constant. `bodyBinders` is the map
    * of the body's readback.
    */
  private def referenced[C <: NativeSpecializer & Singleton](
      bound: Vector[Bound[C]],
      body: Term[C],
      bodyBinders: TermMap,
      context: Context[C]
  ): (Vector[Bound[C]], Map[String, Int]) =
    def names(term: Term[C], binders: TermMap): Map[String, Int] =
      rendered(
        term,
        TermPath.root(PlaceTree.Empty, binders),
        Scope[C](Vector.empty, context.reserved, Set.empty),
        Position.Whole,
        false,
        Vector.empty,
        List.empty,
        context
      ).result
        .collect {
          case Piece.Token(token) if context.reserved.contains(token) => token
        }
        .groupMapReduce(identity)(_ => 1)(_ + _)
    def added(
        counts: Map[String, Int],
        more: Map[String, Int]
    ): Map[String, Int] =
      more.foldLeft(counts) { case (sum, (name, times)) =>
        sum.updated(name, sum.getOrElse(name, 0) + times)
      }
    val (references, kept) = bound.foldRight(
      (names(body, bodyBinders), List.empty[Bound[C]])
    ) { case (binding, (needed, kept)) =>
      if needed.contains(binding.name) then
        (added(needed, names(binding.value, binding.binders)), binding :: kept)
      else (needed, kept)
    }
    (kept.toVector, references)

  /** A shared instruction bound at the text's start: its name, its term, the
    * origins of its term's binders, the places of its subterms in its term's
    * shape (`placed`), the instruction, and the map of its occurrences merged.
    */
  private final case class Bound[C <: NativeSpecializer & Singleton](
      name: String,
      value: Term[C],
      binders: TermMap,
      places: PlaceTree,
      instruction: Configured[C],
      map: SourceMap
  )

  // ---- places ----

  /** The places of a term's subterms in the term's readback's shape: the place
    * of the subterm the node writes, if it writes one, and the trees of the
    * nodes below it by the child positions of `DeBruijnTerm` (an abstraction's
    * body on the left); `Empty` for a node, and all below it, that writes no
    * subterm's place.
    */
  private[frontend] enum PlaceTree:
    case Empty
    case Branch(place: Option[Place], left: PlaceTree, right: PlaceTree)

    /** The place of the subterm the node writes. */
    def here: Option[Place] = this match
      case Empty               => None
      case Branch(place, _, _) => place

    /** The tree of the node below this one at the step. */
    def below(step: Int): PlaceTree = this match
      case Empty                  => Empty
      case Branch(_, left, right) => if step == 0 then left else right

    /** Each place of the tree with the path of its node, by the child positions
      * of `DeBruijnTerm`.
      */
    def entries: Vector[(Vector[Int], Place)] =
      @scala.annotation.tailrec
      def walked(
          pending: List[(PlaceTree, Vector[Int])],
          found: Vector[(Vector[Int], Place)]
      ): Vector[(Vector[Int], Place)] =
        pending match
          case Nil                                        => found
          case (Empty, _) :: rest                         => walked(rest, found)
          case (Branch(place, left, right), path) :: rest =>
            walked(
              (left, path :+ 0) :: (right, path :+ 1) :: rest,
              found ++ place.map((path, _))
            )
      walked(List((this, Vector.empty)), Vector.empty)

  /** A node of the term rendered, with what the rendering reads of it: its path
    * from the root, by the child positions of `DeBruijnTerm`, for an error's
    * message; the places of the subterms at and below it (`placed`); and its
    * map, the origins of its binders and its locations. The rendering takes the
    * node below by one step, so that reading a node's place or map costs no
    * walk from the root.
    */
  private final case class TermPath(
      steps: Vector[Int],
      places: PlaceTree,
      binders: TermMap
  ):
    def below(step: Int): TermPath =
      TermPath(steps :+ step, places.below(step), binders.below(step))
    def descended(more: Vector[Int]): TermPath = more.foldLeft(this)(_.below(_))

  private object TermPath:

    /** The root of a term with the places and the map given. */
    def root(places: PlaceTree, binders: TermMap): TermPath =
      TermPath(Vector.empty, places, binders)

  /** The place of each subterm of the instruction at each node where the
    * instruction's readback with the stops
    * (`Defunctionalization.instructionTerm`) writes the subterm's: the
    * instruction itself at the root, each layer below it at its own nodes, a
    * stop or an opaque instruction a leaf. The readback writes a thunk as the
    * abstractions of its holes over its code, each slot's filling where the
    * code reads the slot, so that a filling stands at each node of a read and
    * at none for a slot its code never reads; a thunk of no holes writes its
    * code at its own node, where the place of a filling the code is a read of
    * is the one kept. `binding` is the binding the instruction is written in.
    * One walk in the readback's shape, each node's tree made from those below
    * it, so that the cost is the readback's size; a trampoline, since an
    * instruction is as deep as a term.
    */
  private[frontend] def placed[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      stops: Set[Configured[C]],
      binding: Option[String]
  )(using C, StorageAccess): PlaceTree =
    def walked(current: Configured[C], path: Vector[Int]): TailRec[PlaceTree] =
      val here = Some(Place(binding, path))
      if current.opaque || (stops.contains(current) && path.nonEmpty) then
        done(PlaceTree.Branch(here, PlaceTree.Empty, PlaceTree.Empty))
      else
        layerOf(current) match
          case com.yang_bo.gezi.ir.Apply(left, right)   => paired(left, right, here, path)
          case com.yang_bo.gezi.ir.Choice(left, right)  => paired(left, right, here, path)
          case WrittenParallel(left, right) => paired(left, right, here, path)
          case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
            val slots = Defunctionalization.slotValues(
              holes,
              Vector.fill(holes.size)(SlotReading.Unfilled),
              fillings.zipWithIndex.map((filling, position) =>
                SlotReading.Filled(filling, path :+ position)
              )
            )
            codeWalked(code, slots).map(body =>
              if holes.isEmpty then
                body match
                  case PlaceTree.Empty =>
                    PlaceTree.Branch(here, PlaceTree.Empty, PlaceTree.Empty)
                  case PlaceTree.Branch(None, left, right) =>
                    PlaceTree.Branch(here, left, right)
                  case filled => filled
              else abstractions(holes.size, here, body)
            )
          case other => throw IllegalStateException(s"no layer to walk: $other")
    def paired(
        left: Configured[C],
        right: Configured[C],
        here: Option[Place],
        path: Vector[Int]
    ): TailRec[PlaceTree] =
      for
        leftTree <- tailcall(walked(left, path :+ 0))
        rightTree <- tailcall(walked(right, path :+ 1))
      yield PlaceTree.Branch(here, leftTree, rightTree)
    // The tree of a code's readback, a read of a slot the tree of what the
    // slot holds; a node of the code writes no place. An inner thunk's slots
    // hold what its fillings read, a filling that is a slot what that slot
    // of the outer code holds, found once for the thunk as the readback
    // finds them (`Defunctionalization.codeTermOf`), so that a read costs no
    // walk through the thunks around it.
    def codeWalked(
        code: Code,
        slots: Vector[SlotReading[Configured[C]]]
    ): TailRec[PlaceTree] = code match
      case Code.Slot(index) =>
        slots(index) match
          case SlotReading.Unfilled              => done(PlaceTree.Empty)
          case SlotReading.Filled(filling, path) =>
            tailcall(walked(filling, path))
          case SlotReading.Written(filling, outer) =>
            tailcall(codeWalked(filling, outer))
      case Code.Apply(left, right)            => codePaired(left, right, slots)
      case Code.Choice(left, right)           => codePaired(left, right, slots)
      case Code.Parallel(left, right)         => codePaired(left, right, slots)
      case Code.Thunk(inner, holes, fillings) =>
        val innerSlots = Defunctionalization.slotValues(
          holes,
          Vector.fill(holes.size)(SlotReading.Unfilled),
          fillings.map {
            case Code.Slot(index) => slots(index)
            case filling          => SlotReading.Written(filling, slots)
          }
        )
        tailcall(codeWalked(inner, innerSlots)).map(
          abstractions(holes.size, None, _)
        )
      case other =>
        throw IllegalStateException(s"no code layer to walk: $other")
    def codePaired(
        left: Code,
        right: Code,
        slots: Vector[SlotReading[Configured[C]]]
    ): TailRec[PlaceTree] =
      for
        leftTree <- tailcall(codeWalked(left, slots))
        rightTree <- tailcall(codeWalked(right, slots))
      yield PlaceTree.Branch(None, leftTree, rightTree)
    walked(instruction, Vector.empty).result

  /** What a slot of a code holds, for `placed`: a hole's binder, an
    * instruction's filling with its path in the IR, or the code of an inner
    * thunk's filling with what the slots of the code around it hold.
    */
  private enum SlotReading[+Term]:
    case Unfilled
    case Filled(filling: Term, path: Vector[Int])
    case Written(filling: Code, slots: Vector[SlotReading[Term]])

  /** The tree of `count` abstractions over the body, the first writing the
    * place given.
    */
  private def abstractions(
      count: Int,
      here: Option[Place],
      body: PlaceTree
  ): PlaceTree =
    (count - 1 to 0 by -1).foldLeft(body)((inner, position) =>
      PlaceTree.Branch(
        if position == 0 then here else None,
        inner,
        PlaceTree.Empty
      )
    )

  /** The times each instruction under the root is referred to by the
    * instructions above it, a filling counted as often as its code writes its
    * slot; and the instructions in an order where each comes after those it
    * refers to. Each distinct instruction is walked once. The instructions are
    * the nodes of the display's table (`tabled`): of the objects with one layer
    * over the same parts, the first stands for them.
    */
  private[frontend] def counted[C <: NativeSpecializer & Singleton](
      root: Configured[C]
  )(using
      C,
      StorageAccess
  ): (Map[Configured[C], Int], Vector[Configured[C]]) =
    val table = tabled(root, Reading.Display)
    (
      table.counts.map((node, times) => table.objectOf(node) -> times),
      table.order.map(table.objectOf)
    )

  /** The times the code's readback writes each of its slots, counted up to 2: a
    * slot read where the code reads it, and as often as an inner thunk's code
    * reads the inner slot whose filling reads it, since the readback writes a
    * filling at each read of its slot. A trampoline: codes nest as deep as a
    * term.
    */
  private def slotReads(code: Code): Map[Int, Int] = slotReadsOf(code).result

  private def slotReadsOf(root: Code): TailRec[Map[Int, Int]] =
    // The codes still to read, each with the times the readback writes it,
    // up to 2, and the reads found.
    def walked(
        pending: List[(Code, Int)],
        reads: Map[Int, Int]
    ): TailRec[Map[Int, Int]] = pending match
      case Nil                      => done(reads)
      case (current, times) :: rest =>
        current match
          case Code.Slot(index) =>
            tailcall(
              walked(
                rest,
                reads.updated(index, (reads.getOrElse(index, 0) + times).min(2))
              )
            )
          case Code.Apply(function, argument) =>
            tailcall(
              walked((function, times) :: (argument, times) :: rest, reads)
            )
          case Code.Choice(left, right) =>
            tailcall(walked((left, times) :: (right, times) :: rest, reads))
          case Code.Parallel(left, right) =>
            tailcall(walked((left, times) :: (right, times) :: rest, reads))
          case Code.Thunk(inner, holes, fillings) =>
            tailcall(slotReadsOf(inner)).flatMap(innerReads =>
              val filled = Defunctionalization
                .slotValues(
                  holes,
                  Vector.fill(holes.size)(Option.empty[Code]),
                  fillings.map(Some(_))
                )
                .zipWithIndex
                .collect {
                  case (Some(filling), slot) if innerReads.contains(slot) =>
                    (filling, (times * innerReads(slot)).min(2))
                }
              tailcall(walked(filled.toList ++ rest, reads))
            )
          case other =>
            throw IllegalStateException(s"no code layer to walk: $other")
    walked(List((root, 1)), Map.empty)

  // ---- names of constants ----

  /** The name of each opaque instruction, URI node, known instruction written
    * by name and shared instruction under the root, distinct from one another:
    * a known instruction, written or bound, named by its known name, taken
    * before the shared ones' so that it keeps it, the others as SHARING and
    * NAMES say, the head of their spine named by its name when it is one of
    * these.
    */
  private def constantsNamed[C <: NativeSpecializer & Singleton](
      table: Table[C],
      shared: Vector[NodeId],
      hashes: Map[NodeId, Int],
      bound: Map[NodeId, String],
      written: Map[NodeId, String]
  ): Map[NodeId, String] =
    val order = table.order
    val leaves = order
      .filter(table.named)
      .map(node =>
        node -> NameSpelling.escaped(table.objectOf(node).layer match
          case com.yang_bo.gezi.ir.Opaque(name) => name
          case com.yang_bo.gezi.ir.UriNode(uri) => uri.toString
          case other => throw IllegalStateException(s"no name for $other"))
      )
    val leafNames = leaves.toMap
    val (knownShared, unknownShared) = shared.partition(bound.contains)
    val known =
      order.filter(written.contains).map(value => value -> written(value)) ++
        knownShared.map(value => value -> bound(value))
    val withKnown = known.foldLeft((leafNames, leafNames.values.toSet)) {
      case ((names, taken), (value, knownName)) =>
        require(
          NameSpelling.isName(knownName),
          s"the known name $knownName is no name"
        )
        val name = fresh(knownName, taken)
        (names.updated(value, name), taken + name)
    }
    val headNames = withKnown._1
    unknownShared
      .foldLeft(withKnown) { case ((names, taken), value) =>
        val head = headName(value, table, headNames)
        val name = LazyList
          .from(1)
          .map(ordinal =>
            NameSpelling.shared(
              NameSpelling.Shared(head, hashes(value), ordinal)
            )
          )
          .find(!taken.contains(_))
          .get
        (names.updated(value, name), taken + name)
      }
      ._1

  /** The name of the head of the node's application spine when it is one of
    * `leafNames`.
    */
  @scala.annotation.tailrec
  private def headName[C <: NativeSpecializer & Singleton](
      node: NodeId,
      table: Table[C],
      leafNames: Map[NodeId, String]
  ): Option[String] =
    if leafNames.contains(node) then Some(leafNames(node))
    else
      table.nodes(node) match
        case WrittenLayer.Applied(function, _) =>
          headName(function, table, leafNames)
        case _ => None

  /** The base, or the base with `_2`, `_3` and so on, the first not taken. */
  private def fresh(base: String, taken: Set[String]): String =
    if !taken.contains(base) then base
    else
      LazyList
        .from(2)
        .map(number => s"${base}_$number")
        .find(!taken.contains(_))
        .get

  // ---- content hashes ----

  /** The content hash of each node of the table, which puts each after its
    * parts, from its layer and the hashes of its parts, never from an
    * identity's hash code, so that the JVM and Scala.js give one name to one
    * term in every process.
    */
  private def contentHashes[C <: NativeSpecializer & Singleton](
      table: Table[C]
  ): Map[NodeId, Int] =
    table.order
      .foldLeft((Map.empty[NodeId, Int], Map.empty[Code, Int])) {
        case ((hashes, codeHashes), node) =>
          val (hash, updatedCodes) =
            layerHash(table.nodes(node), hashes, codeHashes)
          (hashes.updated(node, hash), updatedCodes)
      }
      ._1

  private def layerHash[C <: NativeSpecializer & Singleton](
      layer: WrittenLayer[C, NodeId],
      hashes: Map[NodeId, Int],
      codeHashes: Map[Code, Int]
  ): (Int, Map[Code, Int]) =
    def mixed(tag: Int, parts: Seq[Int]): Int =
      MurmurHash3.finalizeHash(
        parts.foldLeft(MurmurHash3.mix(0x6a1e5, tag))(MurmurHash3.mix),
        parts.size + 1
      )
    layer match
      case WrittenLayer.Leaf(term) =>
        term.layer match
          case com.yang_bo.gezi.ir.Opaque(name) =>
            (mixed(1, Seq(MurmurHash3.stringHash(name))), codeHashes)
          case com.yang_bo.gezi.ir.UriNode(uri) =>
            (mixed(2, Seq(MurmurHash3.stringHash(uri.toString))), codeHashes)
          case other => throw IllegalStateException(s"no layer to hash: $other")
      case WrittenLayer.Applied(function, argument) =>
        (mixed(3, Seq(hashes(function), hashes(argument))), codeHashes)
      case WrittenLayer.Chosen(left, right) =>
        (mixed(4, Seq(hashes(left), hashes(right))), codeHashes)
      // A storage hashes as the parallel its view is, so that its name is the one of the term written out.
      case WrittenLayer.Paralleled(left, right) =>
        (mixed(5, Seq(hashes(left), hashes(right))), codeHashes)
      case WrittenLayer.Abstracted(code, holes, fillings) =>
        val (codeHash, updatedCodes) = codeHashOf(code, codeHashes)
        (
          mixed(
            6,
            Seq(codeHash) ++ holes.map(holeHash) ++ fillings.map(hashes)
          ),
          updatedCodes
        )
      case WrittenLayer.Fielded(_, _, _) =>
        throw IllegalStateException(
          "a storage's Scott ADT layer is respelled as a thunk before it is hashed"
        )

  private def holeHash(hole: Hole): Int = hole match
    case Hole.Bound(slot) => slot + 1
    case Hole.Ignored     => 0

  /** The content hash of the code, each distinct code hashed once, its parts
    * before it.
    */
  private def codeHashOf(
      root: Code,
      known: Map[Code, Int]
  ): (Int, Map[Code, Int]) =
    def mixed(tag: Int, parts: Seq[Int]): Int =
      MurmurHash3.finalizeHash(
        parts.foldLeft(MurmurHash3.mix(0xc0de5, tag))(MurmurHash3.mix),
        parts.size + 1
      )
    def parts(code: Code): Vector[Code] = code match
      case Code.Slot(_)                   => Vector.empty
      case Code.Apply(function, argument) => Vector(function, argument)
      case Code.Choice(left, right)       => Vector(left, right)
      case Code.Parallel(left, right)     => Vector(left, right)
      case Code.Thunk(inner, _, fillings) => inner +: fillings
      case other                          =>
        throw IllegalStateException(s"no code layer to hash: $other")
    @scala.annotation.tailrec
    def walked(
        pending: List[(Code, Boolean)],
        hashes: Map[Code, Int]
    ): Map[Code, Int] = pending match
      case Nil                                        => hashes
      case (code, _) :: rest if hashes.contains(code) => walked(rest, hashes)
      case (code, false) :: rest                      =>
        walked(
          parts(code).map((_, false)).toList ++ ((code, true) :: rest),
          hashes
        )
      case (code, true) :: rest =>
        val hash = code match
          case Code.Slot(index)               => mixed(1, Seq(index))
          case Code.Apply(function, argument) =>
            mixed(2, Seq(hashes(function), hashes(argument)))
          case Code.Choice(left, right) =>
            mixed(3, Seq(hashes(left), hashes(right)))
          case Code.Parallel(left, right) =>
            mixed(4, Seq(hashes(left), hashes(right)))
          case Code.Thunk(inner, holes, fillings) =>
            mixed(
              5,
              Seq(hashes(inner)) ++ holes.map(holeHash) ++ fillings.map(hashes)
            )
          case other =>
            throw IllegalStateException(s"no code layer to hash: $other")
        walked(rest, hashes.updated(code, hash))
    val hashes = walked(List((root, false)), known)
    (hashes(root), hashes)

  // ---- rendering ----

  /** What the rendering reads besides the node rendered (`TermPath`): the names
    * of the constants, the names no binder may take, the terms top is written
    * as, the name of a binder with no origin when the term is printed nameless
    * (`printedNameless`), and the text the term was read from when it is
    * written back (`writtenBack`).
    */
  private final case class Context[C <: NativeSpecializer & Singleton](
      constantNames: Map[NodeId, String],
      reserved: Set[String],
      top: Set[Term[C]],
      unnamed: Option[String],
      source: Option[SourceText]
  )

  /** The text a term was read from, the file of the URI, in code points, and
    * the spans of its literal tokens (strings and CBOR literals): what
    * `writtenBack` spells literals from.
    */
  final case class SourceText(
      uri: java.net.URI,
      codePoints: Vector[Int],
      literals: Set[Span]
  ):

    /** The span of the first of the locations in this text, by its start. */
    def span(locations: Set[Location]): Option[Span] =
      locations
        .collect { case Location.Source(at, span) if at == uri => span }
        .minByOption(_.start)

    /** The text of the literal token the span is, or holds alone in
      * parentheses, as `(0.5)` holds `0.5`.
      */
    def literal(span: Span): Option[String] =
      if literals.contains(span) then Some(span.of(codePoints))
      else
        literals
          .find(token =>
            token.start > span.start && token.end < span.end &&
              (codePoints.slice(span.start, token.start) ++ codePoints
                .slice(token.end, span.end)).forall(point =>
                point == '('.toInt || point == ')'.toInt || Character
                  .isWhitespace(point)
              )
          )
          .map(_.of(codePoints))

  object SourceText:

    /** The source text of the text, its literal tokens found by its lexemes. */
    def of(uri: java.net.URI, text: String): SourceText =
      val (literals, _) =
        Lambdalattice.lexemes(text).foldLeft((Set.empty[Span], 0)) {
          case ((found, offset), lexeme) =>
            val end =
              offset + lexeme.written.codePointCount(0, lexeme.written.length)
            lexeme match
              case Lexeme.Token(
                    TokenKind.StringLiteral(_) | TokenKind.CborLiteral(_),
                    _
                  ) =>
                (found + Span(offset, end), end)
              case _ => (found, end)
        }
      SourceText(uri, text.codePoints.toScala(Vector).map(_.toInt), literals)

  /** The binders in scope: their names by de Bruijn level, and the set of them;
    * the rests of the levels of partial functions' chains that are written as
    * plain abstractions, where no literal is looked for, since a literal found
    * there would start in the middle of the chain's bits; and for a base name,
    * the least suffix `n` of `base_n` not known to be taken, every suffix from
    * 2 below it taken, so that naming a binder `base_n` costs no scan of the
    * names already in scope: the names in scope only grow, and the printer of a
    * nameless term, every binder of which is named `x`, named the binder at
    * depth d after trying d names (the six programs of
    * `contest_hidden_37_courses`' snapshot, 606 KB as the exchange format wrote
    * them as trees, took 99 s to print with their places marked, 86 s with
    * this, measured 2026-11-19, while the places still cost the square of the
    * depth).
    */
  private final case class Scope[C <: NativeSpecializer & Singleton](
      names: Vector[String],
      taken: Set[String],
      plainLevels: Set[Term[C]],
      suffixes: Map[String, Int] = Map.empty
  ):
    def bound(name: String): Scope[C] =
      copy(names = names :+ name, taken = taken + name)
    def variable(index: Int): String = names(names.size - 1 - index)

    /** The base, or the base with `_2`, `_3` and so on, the first not taken
      * (`fresh`), and the scope that knows every suffix below it taken.
      */
    def fresh(base: String): (String, Scope[C]) =
      if !taken.contains(base) then (base, this)
      else
        val number = LazyList
          .from(suffixes.getOrElse(base, 2))
          .find(number => !taken.contains(s"${base}_$number"))
          .get
        (
          s"${base}_$number",
          copy(suffixes = suffixes.updated(base, number + 1))
        )

  /** Where a term stands, which decides whether it needs parentheses. */
  private enum Position:
    /** At the top or in parentheses: anything. */
    case Whole

    /** A body, or the last argument after `λ.`: no chain. */
    case Body

    /** The first operand of a chain: no chain, it being flattened. */
    case Operand

    /** A head or an argument before the last: an atom only. */
    case Atomic

  /** The pieces, in reverse, of the bindings of the shared values around the
    * body, in one spine: `(λt. t V) λm.` for each, the last binder merged with
    * the body's own leading binders.
    */
  private def bindingsWritten[C <: NativeSpecializer & Singleton](
      bound: Vector[Bound[C]],
      helper: String,
      body: Term[C],
      bodyRoot: TermPath,
      context: Context[C]
  ): TailRec[List[Piece]] =
    val start = Scope[C](Vector.empty, context.reserved, Set.empty)
    bound match
      case Vector() =>
        rendered(
          body,
          bodyRoot,
          start,
          Position.Whole,
          false,
          Vector.empty,
          List.empty,
          context
        )
      case _ =>
        val helperScope =
          Scope[C](Vector(helper), context.reserved + helper, Set.empty)
        val written = Trampoline.folded(
          bound.zipWithIndex,
          List[Piece](Piece.Open(Node.Spine))
        ) { case (before, (Bound(name, value, binders, places, _, _), index)) =>
          val opened = Piece.Token(" ") :: (parameters(
            Vector(helper)
          ) reverse_::: (Piece.Open(Node.Spine) ::
            Piece.Token("(") :: Piece.Open(Node.Parenthesized) :: Piece.Open(
              Node.Expression
            ) :: before))
          val application = DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value)
          // The value stands at the path 1 of the application.
          val valueRoot = TermPath.root(
            PlaceTree.Branch(None, PlaceTree.Empty, places),
            TermMap.Pair(Set.empty, TermMap.Unknown, binders)
          )
          tailcall(
            rendered(
              application,
              valueRoot,
              helperScope,
              Position.Body,
              true,
              Vector.empty,
              opened,
              context
            )
          )
            .map(withValue =>
              val closed = Piece.Close :: Piece.Close :: Piece.Token(
                ")"
              ) :: Piece.Close :: withValue
              if index < bound.size - 1 then
                Piece.Token(" ") :: (parameters(Vector(name)) reverse_::: (Piece
                  .Token(" ") :: closed))
              else Piece.Token(" ") :: closed
            )
        }
        written
          .flatMap(before =>
            tailcall(
              afterBinders(
                body,
                bodyRoot,
                start,
                Vector(bound.last.name),
                before,
                context
              )
            )
          )
          .map(Piece.Close :: _)

  /** The term after binders still to be written in its spine: an abstraction
    * takes them before its own; anything else gets them as a parameter list of
    * their own.
    */
  private def afterBinders[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      scope: Scope[C],
      pending: Vector[String],
      before: List[Piece],
      context: Context[C]
  ): TailRec[List[Piece]] =
    term match
      case DeBruijnTerm.Lambda(_) =>
        rendered(
          term,
          path,
          scope,
          Position.Body,
          true,
          pending,
          before,
          context
        )
      case _ =>
        val withParameters = parameters(pending) reverse_::: before
        val bodyScope = pending.foldLeft(scope)(_.bound(_))
        tailcall(
          rendered(
            term,
            path,
            bodyScope,
            Position.Body,
            true,
            Vector.empty,
            Piece.Token(" ") :: withParameters,
            context
          )
        )

  /** The width past which `Printed.laidOut` writes a part on lines. */
  val lineWidth: Int = 100

  /** The pieces as a tree of their nodes, each with the length of the text it
    * spells and whether a break stands inside it, the places dropped. A break
    * stands before each token whose index is among the breaks
    * (`Printed.brokenText`), where the tree holds `Broken`, which spells
    * nothing, in the innermost node that holds both the token before and that
    * token.
    */
  private enum Tree:
    case Leaf(token: String)
    case Broken
    case Branch(node: Node, parts: Vector[Tree], length: Int, broken: Boolean)

    def width: Int = this match
      case Leaf(token)             => token.length
      case Broken                  => 0
      case Branch(_, _, length, _) => length

    /** Whether a break stands inside the tree. */
    def holdsBreak: Boolean = this match
      case Leaf(_)                 => false
      case Broken                  => true
      case Branch(_, _, _, broken) => broken

    /** Whether the tree is written on one line: it is no wider than the width,
      * and no break stands inside it.
      */
    def fits(limit: Int): Boolean = !holdsBreak && width <= limit

  private def trees(pieces: Vector[Piece], breaks: Set[Int]): Vector[Tree] =
    val broken = breakPositions(pieces, breaks)
    def added(
        stack: List[(Node, Vector[Tree])],
        finished: Vector[Tree],
        tree: Tree
    ): (Vector[Tree], List[(Node, Vector[Tree])]) =
      stack match
        case (node, parts) :: rest => (finished, (node, parts :+ tree) :: rest)
        case Nil                   => (finished :+ tree, Nil)
    def read(
        state: (Vector[Tree], List[(Node, Vector[Tree])]),
        piece: Piece
    ): (Vector[Tree], List[(Node, Vector[Tree])]) =
      (state, piece) match
        case ((finished, stack), Piece.Token(token)) =>
          added(stack, finished, Tree.Leaf(token))
        case ((finished, stack), Piece.Open(node)) =>
          (finished, (node, Vector.empty) :: stack)
        case ((finished, (node, parts) :: rest), Piece.Close) =>
          added(
            rest,
            finished,
            Tree.Branch(
              node,
              parts,
              parts.map(_.width).sum,
              parts.exists(_.holdsBreak)
            )
          )
        case ((_, Nil), Piece.Close) =>
          throw IllegalStateException("the pieces close a node none opened")
        case (state, Piece.At(_, _))  => state
        case (state, Piece.Source(_)) => state
    val (finished, open) = pieces.zipWithIndex.foldLeft(
      (Vector.empty[Tree], List.empty[(Node, Vector[Tree])])
    ) {
      case ((finished, stack), (piece, position)) if broken(position) =>
        read(added(stack, finished, Tree.Broken), piece)
      case (state, (piece, _)) => read(state, piece)
    }
    if open.nonEmpty then
      throw IllegalStateException(s"the pieces leave ${open.size} nodes open")
    finished

  /** The positions among the pieces before which a break stands, one for each
    * token index among the breaks: after the token before it and the closings
    * right after that token, before the openings that lead to it.
    */
  private def breakPositions(
      pieces: Vector[Piece],
      breaks: Set[Int]
  ): Set[Int] =
    // The index of the next token, the position after the token before and
    // its closings, whether a node opened since, and the positions found.
    val (_, _, _, found) =
      pieces.zipWithIndex.foldLeft((0, 0, false, Set.empty[Int])) {
        case ((index, after, _, found), (Piece.Token(text), position))
            if tokenCount(text) > 0 =>
          (
            index + tokenCount(text),
            position + 1,
            false,
            if breaks(index) then found + after else found
          )
        case ((index, _, false, found), (Piece.Close, position)) =>
          (index, position + 1, false, found)
        case ((index, after, _, found), (Piece.Open(_), _)) =>
          (index, after, true, found)
        case (state, _) => state
      }
    found

  /** The number of tokens a piece's text holds: none in white space, two in the
    * parameter list `λ.`, one in any other piece the printer writes (a name, a
    * literal, `λ`, `.`, a parenthesis, an operator with its spaces). Not lexed,
    * since each call of the lexer compiles its parser
    * (`Lambdalattice.lexemes`).
    */
  private[frontend] def tokenCount(text: String): Int =
    if text.isBlank then 0 else if text == "λ." then 2 else 1

  /** The tokens `Printed.laidOut` may write that the pieces do not: the `λ`
    * line opening a right spine that starts with an expression
    * (`LambdalatticeLayout.ParameterLists.Prefixed`), and the parentheses
    * around a text that spans lines and is no right spine.
    */
  private val layoutTokens: Set[String] = Set("λ", ".", "(", ")")

  /** `Printed.brokenText` of the pieces. */
  private def broken(
      pieces: Vector[Piece],
      width: Int,
      breaks: Set[Int]
  ): String =
    Trampoline
      .folded(trees(pieces, breaks).toVector, List.empty[String])(
        (before, tree) => brokenWritten(tree, width, before)
      )
      .result
      .reverse
      .mkString

  /** The tokens of a tree, in reverse, on one line. */
  private def flatWritten(
      tree: Tree,
      before: List[String]
  ): TailRec[List[String]] = tree match
    case Tree.Leaf(token)            => done(token :: before)
    case Tree.Broken                 => done(before)
    case Tree.Branch(_, parts, _, _) =>
      Trampoline.folded(parts.toVector, before)((inner, part) =>
        flatWritten(part, inner)
      )

  /** The tokens of a tree, in reverse, with the line breaks of
    * `Printed.brokenText`.
    */
  private def brokenWritten(
      tree: Tree,
      width: Int,
      before: List[String]
  ): TailRec[List[String]] =
    def each(parts: Vector[Tree], start: List[String])(
        part: (Tree, List[String]) => TailRec[List[String]]
    ): TailRec[List[String]] =
      Trampoline.folded(parts, start)((inner, next) => part(next, inner))
    tree match
      case short if short.fits(width)           => flatWritten(short, before)
      case Tree.Leaf(token)                     => done(token :: before)
      case Tree.Broken                          => done(before)
      case Tree.Branch(Node.Spine, parts, _, _) =>
        // The spine breaks until the rest of it, from an expression or a
        // parameter list on, fits the width and holds no break; the rest
        // stays on one line.
        val restWidths = parts.scanRight(0)((part, rest) => part.width + rest)
        val restBroken =
          parts.scanRight(false)((part, rest) => part.holdsBreak || rest)
        val flatFrom = parts.indices
          .find(index =>
            index > 0 && restWidths(index) <= width && !restBroken(
              index
            ) && (parts(index) match
              case Tree.Branch(Node.Parameters | Node.Expression, _, _, _) =>
                true
              case _ => false)
          )
          .getOrElse(parts.size)
        each(parts.take(flatFrom), before) {
          case (Tree.Branch(Node.Parameters, list, _, _), inner) =>
            done(list.foldLeft("\n" :: inner) {
              case (written, Tree.Leaf("."))      => "\n." :: written
              case (written, Tree.Leaf("λ."))     => "λ\n." :: written
              case (written, Tree.Leaf("λ"))      => "λ " :: written
              case (written, Tree.Leaf(token))    => token :: written
              case (written, Tree.Broken)         => written
              case (written, binder: Tree.Branch) =>
                flatWritten(binder, Nil).result.reverse.mkString :: written
            })
          case (expression @ Tree.Branch(Node.Expression, _, _, _), inner) =>
            expressionWritten(expression, width, inner)
          case (part, inner) => brokenWritten(part, width, inner)
        }.flatMap(inner => each(parts.drop(flatFrom), inner)(flatWritten))
      case expression @ Tree.Branch(Node.Expression, _, _, _) =>
        expressionWritten(expression, width, before)
      // Parentheses whose content fits stay on its line: breaking before
      // `)` alone would put nothing else on a line of its own.
      case fitting @ Tree.Branch(Node.Parenthesized, _, _, false)
          if fitting.width - 2 <= width =>
        flatWritten(fitting, before)
      case Tree.Branch(Node.Parenthesized, parts, _, _) =>
        each(parts, before) {
          case (Tree.Leaf(")"), inner) => done("\n)" :: inner)
          case (part, inner)           => brokenWritten(part, width, inner)
        }
      case Tree.Branch(Node.Chain, parts, _, _) =>
        each(parts, before) {
          case (step @ Tree.Branch(Node.Step, _, _, _), inner) =>
            brokenWritten(step, width, "\n" :: inner)
          case (part, inner) => brokenWritten(part, width, inner)
        }
      case Tree.Branch(_, parts, _, _) =>
        each(parts, before)((part, inner) => brokenWritten(part, width, inner))

  /** An expression wider than the width, each parenthesized argument on a line
    * of its own.
    */
  private def expressionWritten(
      expression: Tree,
      width: Int,
      before: List[String]
  ): TailRec[List[String]] = expression match
    case Tree.Branch(_, parts, _, _) if !expression.fits(width) =>
      Trampoline.folded(parts.zipWithIndex.toVector, before) {
        case (inner, (part, index)) =>
          part match
            case Tree.Branch(Node.Parenthesized, _, _, _) if index > 0 =>
              brokenWritten(part, width, "\n" :: inner)
            case _ => brokenWritten(part, width, inner)
      }
    case _ => flatWritten(expression, before)

  /** The pieces of a parameter list, each binder an atom of its own. */
  private def parameters(names: Vector[String]): List[Piece] =
    spelledParameters(names.map(Spelled(_, None, false)))

  /** `parameters` of binders each marked where the source spells it. */
  private def spelledParameters(names: Vector[Spelled]): List[Piece] =
    if names.isEmpty then
      List(Piece.Open(Node.Parameters), Piece.Token("λ."), Piece.Close)
    else
      val binders = names.toList
        .flatMap(name => Piece.Token(" ") :: spelledPieces(name))
        .tail
      (Piece.Open(Node.Parameters) :: Piece.Token("λ") :: binders) ++ List(
        Piece.Token("."),
        Piece.Close
      )

  /** A name or a literal the printer writes, the code point offset where the
    * source text spells it, when it is written back (`writtenBack`), and
    * whether it is written in parentheses, as a literal that means another
    * literal bare is (`LiteralWriting.bareArgument`).
    */
  private final case class Spelled(
      text: String,
      start: Option[Int],
      parenthesized: Boolean
  )

  /** The pieces of a spelled name or literal, in order: its atom, in
    * parentheses where it is written so.
    */
  private def spelledPieces(spelled: Spelled): List[Piece] =
    val written =
      List(Piece.Open(Node.Atom), Piece.Token(spelled.text), Piece.Close)
    val enclosed =
      if spelled.parenthesized then
        (Piece.Open(Node.Parenthesized) :: Piece.Token("(") :: written) ++ List(
          Piece.Token(")"),
          Piece.Close
        )
      else written
    spelled.start.map(Piece.Source(_)).toList ++ enclosed

  /** The pieces before, a source mark put first where the source text spells
    * the node at the path (`writtenBack`).
    */
  private def sourceMarked[C <: NativeSpecializer & Singleton](
      path: TermPath,
      before: List[Piece],
      context: Context[C]
  ): List[Piece] =
    context.source
      .flatMap(_.span(path.binders.nodeLocations))
      .fold(before)(span => Piece.Source(span.start) :: before)

  /** The pieces, in reverse, of the term at the position. `continuing` says
    * that the term continues a spine already open; `pending` holds binders of
    * the scope already bound but not yet written, which an abstraction writes
    * before its own.
    */
  private def rendered[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      scope: Scope[C],
      position: Position,
      continuing: Boolean,
      pending: Vector[String],
      before: List[Piece],
      context: Context[C]
  ): TailRec[List[Piece]] =
    // A term in parentheses is rendered again at its path inside them, where
    // it is marked.
    val inParentheses = term match
      case DeBruijnTerm.Lambda(_) | DeBruijnTerm.Apply(_, _) =>
        position == Position.Atomic
      case DeBruijnTerm.Choice(_, _) | DeBruijnTerm.Parallel(_, _) =>
        position != Position.Whole
      case _ => false
    val marked = if inParentheses then before
    else path.places.here.fold(before)(Piece.At(_, continuing) :: before)
    renderedUnmarked(
      term,
      path,
      scope,
      position,
      continuing,
      pending,
      marked,
      context
    )

  /** `rendered` after the mark of the term's place. */
  private def renderedUnmarked[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      scope: Scope[C],
      position: Position,
      continuing: Boolean,
      pending: Vector[String],
      before: List[Piece],
      context: Context[C]
  ): TailRec[List[Piece]] =
    term match
      case DeBruijnTerm.Variable(index) =>
        done(atom(scope.variable(index), sourceMarked(path, before, context)))
      case DeBruijnTerm.Constant(instruction) =>
        done(
          atom(
            context.constantNames.getOrElse(
              instruction,
              throw IllegalStateException(s"no name for $instruction")
            ),
            before
          )
        )
      case DeBruijnTerm.Free(name) => done(atom(name, before))
      case DeBruijnTerm.Lambda(_) if position == Position.Atomic =>
        parenthesized(term, path, scope, before, context)
      case DeBruijnTerm.Lambda(_) =>
        val (names, body, bodyPath, bodyScope) =
          binders(term, path, scope, pending, context)
        val opened =
          if continuing then before else Piece.Open(Node.Spine) :: before
        val withParameters =
          Piece.Token(" ") :: (spelledParameters(names) reverse_::: opened)
        tailcall(
          rendered(
            body,
            bodyPath,
            bodyScope,
            Position.Body,
            true,
            Vector.empty,
            withParameters,
            context
          )
        )
          .map(written =>
            if continuing then written else Piece.Close :: written
          )
      case DeBruijnTerm.Apply(_, _) if position == Position.Atomic =>
        parenthesized(term, path, scope, before, context)
      case DeBruijnTerm.Apply(_, _) =>
        val (head, written) = spine(term, path)
        val arguments = context.source.fold(literalArguments(written))(
          sourceLiteralArguments(written, _)
        )
        val opened = Piece.Open(
          Node.Expression
        ) :: (if continuing then before else Piece.Open(Node.Spine) :: before)
        val withInit = tailcall(
          rendered(
            head._1,
            head._2,
            scope,
            Position.Atomic,
            false,
            Vector.empty,
            opened,
            context
          )
        )
          .flatMap(withHead =>
            Trampoline.folded(arguments.init.toVector, withHead) {
              case (before, Argument.Written(argument, argumentPath)) =>
                rendered(
                  argument,
                  argumentPath,
                  scope,
                  Position.Atomic,
                  false,
                  Vector.empty,
                  Piece.Token(" ") :: before,
                  context
                )
              case (before, Argument.LiteralText(text)) =>
                done(spelledAtom(text, Piece.Token(" ") :: before))
            }
          )
        withInit
          .flatMap(withArguments =>
            arguments.last match
              case Argument.LiteralText(text) =>
                done(
                  Piece.Close :: spelledAtom(
                    text,
                    Piece.Token(" ") :: withArguments
                  )
                )
              case Argument.Written(last @ DeBruijnTerm.Lambda(_), lastPath) =>
                tailcall(
                  rendered(
                    last,
                    lastPath,
                    scope,
                    Position.Body,
                    true,
                    Vector.empty,
                    Piece.Token(" ") :: Piece.Close :: withArguments,
                    context
                  )
                )
              case Argument
                    .Written(last @ DeBruijnTerm.Apply(_, _), lastPath) =>
                val withZero = Piece
                  .Token(" ") :: (parameters(Vector.empty) reverse_::: (Piece
                  .Token(" ") :: Piece.Close :: withArguments))
                tailcall(
                  rendered(
                    last,
                    lastPath,
                    scope,
                    Position.Body,
                    true,
                    Vector.empty,
                    withZero,
                    context
                  )
                )
              case Argument.Written(last, lastPath) =>
                tailcall(
                  rendered(
                    last,
                    lastPath,
                    scope,
                    Position.Atomic,
                    false,
                    Vector.empty,
                    Piece.Token(" ") :: withArguments,
                    context
                  )
                )
                  .map(Piece.Close :: _)
          )
          .map(done => if continuing then done else Piece.Close :: done)
      case DeBruijnTerm.Choice(_, _) | DeBruijnTerm.Parallel(_, _) =>
        if position == Position.Whole then
          chained(term, path, scope, before, context)
        else parenthesized(term, path, scope, before, context)
      case other => throw IllegalStateException(s"no rendering of $other")

  /** The pieces of an atom. */
  private def atom(name: String, before: List[Piece]): List[Piece] =
    Piece.Close :: Piece.Token(name) :: Piece.Open(Node.Atom) :: before

  /** The pieces of a spelled name or literal (`spelledPieces`). */
  private def spelledAtom(spelled: Spelled, before: List[Piece]): List[Piece] =
    spelledPieces(spelled) reverse_::: before

  /** The term in parentheses. */
  private def parenthesized[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      scope: Scope[C],
      before: List[Piece],
      context: Context[C]
  ): TailRec[List[Piece]] =
    tailcall(
      rendered(
        term,
        path,
        scope,
        Position.Whole,
        false,
        Vector.empty,
        Piece.Token("(") :: Piece.Open(Node.Parenthesized) :: before,
        context
      )
    )
      .map(written => Piece.Close :: Piece.Token(")") :: written)

  /** The binders of adjacent abstractions from the term, the pending ones
    * first, each named, and the body under them with its path and scope.
    */
  private def binders[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      scope: Scope[C],
      pending: Vector[String],
      context: Context[C]
  ): (Vector[Spelled], Term[C], TermPath, Scope[C]) =
    @scala.annotation.tailrec
    def collected(
        current: Term[C],
        currentPath: TermPath,
        currentScope: Scope[C],
        names: Vector[Spelled]
    ): (Vector[Spelled], Term[C], TermPath, Scope[C]) =
      current match
        case DeBruijnTerm.Lambda(body) =>
          val (found, plain) = context.source match
            case Some(source) =>
              (sourceLiteralBinder(current, currentPath, source), Vector.empty)
            case None =>
              if currentScope.plainLevels.contains(current) then
                (None, Vector.empty)
              else literalBinders(current, currentPath, context)
          val scope = currentScope.copy[C](plainLevels =
            currentScope.plainLevels ++ plain
          )
          found match
            case Some(LiteralBinders(texts, bits, rest, restPath)) =>
              // The bits' binders, which the rest does not read, bound with
              // no name.
              collected(
                rest,
                restPath,
                (1 to bits).foldLeft(scope)((inner, _) => inner.bound("")),
                names ++ texts
              )
            case None =>
              val origins = currentPath.binders.nodeOrigins
              // Written back, a binder keeps the one name its text writes,
              // shadowing as the text does.
              val (name, named) =
                context.source.flatMap(writtenName(origins, _)) match
                  case Some(written) => (written, scope)
                  case None          =>
                    val (chosen, after) = binderName(
                      context.unnamed
                        .filter(_ => origins.isEmpty)
                        .fold(originNames(origins, currentPath.steps))(
                          Vector(_)
                        ),
                      scope
                    )
                    (Spelled(chosen, None, false), after)
              collected(
                body,
                currentPath.below(0),
                named.bound(name.text),
                names :+ name
              )
        case _ => (names, current, currentPath, currentScope)
    collected(
      term,
      path,
      pending.foldLeft(scope)(_.bound(_)),
      pending.map(Spelled(_, None, false))
    )

  /** The literals a chain of abstractions binds, as `Literals.partialFunction`
    * writes them: their texts as binders, the number of their bits, and the
    * term after the bits with its path.
    */
  private final case class LiteralBinders[C <: NativeSpecializer & Singleton](
      texts: Vector[Spelled],
      bits: Int,
      rest: Term[C],
      restPath: TermPath
  )

  /** The longest run of complete literals at the start of a chain of
    * abstractions that is a variable arguments partial function, `λx. x REST
    * top` for a 1 and `λx. x top REST` for a 0, whose rest does not read their
    * bits' binders, none when there is no such literal; and the rests of the
    * chain's levels after them, which are written as plain abstractions.
    */
  private def literalBinders[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      context: Context[C]
  ): (Option[LiteralBinders[C]], Vector[Term[C]]) =
    @scala.annotation.tailrec
    def levels(
        current: Term[C],
        currentPath: TermPath,
        found: Vector[(Boolean, Term[C], TermPath)]
    ): Vector[(Boolean, Term[C], TermPath)] =
      current match
        case DeBruijnTerm.Lambda(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), first),
                second
              )
            ) if context.top.contains(second) =>
          levels(
            first,
            currentPath.descended(Vector(0, 0, 1)),
            found :+ (true, first, currentPath.descended(Vector(0, 0, 1)))
          )
        case DeBruijnTerm.Lambda(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), first),
                second
              )
            ) if context.top.contains(first) =>
          levels(
            second,
            currentPath.descended(Vector(0, 1)),
            found :+ (false, second, currentPath.descended(Vector(0, 1)))
          )
        case _ => found
    val found = levels(term, path, Vector.empty)
    val written = LiteralWriting.items(bytes(found.map(_._1)))
    def bitsOf(items: Vector[LiteralWriting.Written]): Int =
      8 * items.map(_.literal.bytes.length).sum
    val taken = (written.size to 1 by -1)
      .map(written.take)
      .find(prefix => !refersTo(found(bitsOf(prefix) - 1)._2, bitsOf(prefix)))
      .getOrElse(Vector.empty)
    val bits = bitsOf(taken)
    val literals = Option
      .when(bits > 0)(found(bits - 1))
      .map((_, rest, restPath) =>
        LiteralBinders[C](
          taken.map(item => Spelled(LiteralWriting.binder(item), None, false)),
          bits,
          rest,
          restPath
        )
      )
    (literals, found.drop(bits).map(_._2))

  /** An argument of an application spine as written: a term, or a literal
    * standing for a run of bit arguments.
    */
  private enum Argument[C <: NativeSpecializer & Singleton]:
    case Written(term: Term[C], path: TermPath)
    case LiteralText(text: Spelled)

  /** The arguments, each run of bit arguments that starts with complete
    * literals written as those literals; a bit no literal takes stays a term.
    */
  private def literalArguments[C <: NativeSpecializer & Singleton](
      arguments: Vector[(Term[C], TermPath)]
  ): Vector[Argument[C]] =
    @scala.annotation.tailrec
    def grouped(
        rest: Vector[(Term[C], TermPath)],
        found: Vector[Argument[C]]
    ): Vector[Argument[C]] =
      rest.headOption match
        case None               => found
        case Some((term, path)) =>
          val run = rest
            .takeWhile((argument, _) => bit(argument).isDefined)
            .flatMap((argument, _) => bit(argument))
          val written = LiteralWriting.items(bytes(run))
          if written.isEmpty then
            grouped(rest.tail, found :+ Argument.Written(term, path))
          else
            grouped(
              rest.drop(8 * written.map(_.literal.bytes.length).sum),
              found ++ written.map(item =>
                Argument.LiteralText(
                  Spelled(LiteralWriting.argument(item), None, false)
                )
              )
            )
    grouped(arguments, Vector.empty)

  /** The arguments as the source text writes them (`writtenBack`): a run of bit
    * arguments located at one literal of the text written as the literal's
    * text, every other argument a term.
    */
  private def sourceLiteralArguments[C <: NativeSpecializer & Singleton](
      arguments: Vector[(Term[C], TermPath)],
      source: SourceText
  ): Vector[Argument[C]] =
    def literalSpan(argument: (Term[C], TermPath)): Option[Span] =
      bit(argument._1)
        .flatMap(_ => source.span(argument._2.binders.nodeLocations))
        .filter(source.literal(_).isDefined)
    def spelled(span: Span): Spelled =
      val text = source
        .literal(span)
        .getOrElse(throw IllegalStateException(s"no literal at $span"))
      Spelled(text, Some(span.start), !LiteralWriting.bareArgument(text))
    @scala.annotation.tailrec
    def grouped(
        rest: Vector[(Term[C], TermPath)],
        found: Vector[Argument[C]]
    ): Vector[Argument[C]] =
      rest.headOption match
        case None                          => found
        case Some(argument @ (term, path)) =>
          literalSpan(argument) match
            case Some(span) =>
              val run = rest.takeWhile(literalSpan(_).contains(span))
              grouped(
                rest.drop(run.size),
                found :+ Argument.LiteralText(spelled(span))
              )
            case None =>
              grouped(rest.tail, found :+ Argument.Written(term, path))
    grouped(arguments, Vector.empty)

  /** The literal the source text writes as a binder at the abstraction
    * (`writtenBack`): an abstraction whose binder is the first bit of a literal
    * the text spells there, and the levels of its variable arguments partial
    * function, `λx. x REST top` for a 1 and `λx. x top REST` for a 0, down to
    * the rest; none for another abstraction.
    */
  private def sourceLiteralBinder[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      source: SourceText
  ): Option[LiteralBinders[C]] =
    path.binders.nodeOrigins
      .collectFirst { case BinderOrigin.LiteralBit(bytes, 0, location) =>
        (bytes, location)
      }
      .flatMap((bytes, location) =>
        source
          .span(Set(location))
          .flatMap(span => source.literal(span).map(span -> _))
          .flatMap((span, text) =>
            val bits = bytes.flatMap(byte =>
              (7 to 0 by -1).map(position => ((byte >> position) & 1) == 1)
            )
            val rest = bits.foldLeft(Option((term, path)))((level, one) =>
              level.flatMap {
                case (
                      DeBruijnTerm.Lambda(
                        DeBruijnTerm.Apply(
                          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), first),
                          second
                        )
                      ),
                      at
                    ) =>
                  Some(if one then (first, at.descended(Vector(0, 0, 1)))
                  else (second, at.descended(Vector(0, 1))))
                case _ => None
              }
            )
            rest.map((restTerm, restPath) =>
              LiteralBinders(
                Vector(
                  Spelled(
                    text,
                    Some(span.start),
                    !LiteralWriting.bareBinder(text)
                  )
                ),
                bits.size,
                restTerm,
                restPath
              )
            )
          )
      )

  /** The one name the written origins give, with where the source text spells
    * it, none when they give no name or several.
    */
  private def writtenName(
      origins: Set[BinderOrigin],
      source: SourceText
  ): Option[Spelled] =
    origins.collect { case BinderOrigin.Written(name, location) =>
      name -> location
    } match
      case written if written.map(_._1).size == 1 =>
        written.headOption.map((name, _) =>
          Spelled(name, source.span(written.map(_._2)).map(_.start), false)
        )
      case _ => None

  /** The bit a term spells: `λt. λf. t` 1, `λt. λf. f` 0. */
  private def bit[C <: NativeSpecializer & Singleton](
      term: Term[C]
  ): Option[Boolean] = term match
    case DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1))) =>
      Some(true)
    case DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))) =>
      Some(false)
    case _ => None

  /** The whole bytes of the bits, each byte high bit first. */
  private def bytes(bits: Vector[Boolean]): Vector[Byte] =
    bits
      .grouped(8)
      .filter(_.size == 8)
      .map(
        _.foldLeft(0)((byte, bit) => 2 * byte + (if bit then 1 else 0)).toByte
      )
      .toVector

  /** Whether the term reads one of the `count` binders right above it. */
  private def refersTo[C <: NativeSpecializer & Singleton](
      term: Term[C],
      count: Int
  ): Boolean =
    @scala.annotation.tailrec
    def searched(pending: List[(Term[C], Int)]): Boolean = pending match
      case Nil                      => false
      case (current, depth) :: rest =>
        current match
          case DeBruijnTerm.Variable(index) =>
            (index >= depth && index < depth + count) || searched(rest)
          case DeBruijnTerm.Lambda(body) => searched((body, depth + 1) :: rest)
          case DeBruijnTerm.Apply(function, argument) =>
            searched((function, depth) :: (argument, depth) :: rest)
          case DeBruijnTerm.Choice(left, right) =>
            searched((left, depth) :: (right, depth) :: rest)
          case DeBruijnTerm.Parallel(left, right) =>
            searched((left, depth) :: (right, depth) :: rest)
          case _ => searched(rest)
    searched(List((term, 0)))

  /** The names a binder's origins give it, least first; an error where it has
    * none.
    */
  private def originNames(
      origins: Set[BinderOrigin],
      path: Vector[Int]
  ): Vector[String] =
    val names = origins
      .map {
        case BinderOrigin.Written(name, _)          => name
        case BinderOrigin.Enclosing(name)           => name
        case BinderOrigin.LiteralBit(bytes, bit, _) =>
          LiteralWriting.bitName(bytes, bit)
        case BinderOrigin.Made(by) => madeName(by)
      }
      .toVector
      .sorted
    if names.isEmpty then
      throw IllegalArgumentException(
        s"the binder at $path has no origin in the map"
      )
    names

  /** The name of a binder a step made, by the kind of the step. */
  private def madeName(by: MadeBy): String = by match
    case MadeBy.Beta          => "beta"
    case MadeBy.Eta           => "eta"
    case MadeBy.Equation      => "equation"
    case MadeBy.Lemma         => "lemma"
    case MadeBy.Native        => "native"
    case MadeBy.Eigenvariable => "eigenvariable"
    case MadeBy.ReverseBeta   => "abstracted"

  /** The name of a binder from the names its origins give, in order, each
    * escaped into a name: the first that is `_` or distinct from every name in
    * scope and every constant's, else the first made distinct. A binder of an
    * instruction the text writes in several places has the names of all of them
    * (interning makes the places one instruction), and each place keeps the one
    * written there when no other name in its scope has it. With the scope that
    * knows the suffixes taken (`Scope.fresh`).
    */
  private def binderName[C <: NativeSpecializer & Singleton](
      names: Vector[String],
      scope: Scope[C]
  ): (String, Scope[C]) =
    val spelled = names.map(name =>
      if name == "_" || NameSpelling.isName(name) then name
      else NameSpelling.escaped(name)
    )
    val least = spelled.headOption.getOrElse(
      throw IllegalArgumentException("a binder has no name to choose from")
    )
    spelled.find(name => name == "_" || !scope.taken.contains(name)) match
      case Some(name) => (name, scope)
      case None       => scope.fresh(least)

  /** The head of an application spine and its arguments, each with its path. */
  private def spine[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath
  ): ((Term[C], TermPath), Vector[(Term[C], TermPath)]) =
    @scala.annotation.tailrec
    def collected(
        current: Term[C],
        currentPath: TermPath,
        arguments: List[(Term[C], TermPath)]
    ): ((Term[C], TermPath), Vector[(Term[C], TermPath)]) =
      current match
        case DeBruijnTerm.Apply(function, argument) =>
          collected(
            function,
            currentPath.below(0),
            (argument, currentPath.below(1)) :: arguments
          )
        case _ => ((current, currentPath), arguments.toVector)
    collected(term, path, Nil)

  /** A chain of + and ∥, the text's left operands flattened: a choice's right
    * side and a parallel's left side, so that a choice's left side is written
    * after its `+` (`Lambdalattice`, the paragraph on chains), each operand
    * after the first in parentheses when it is itself a chain.
    */
  private def chained[C <: NativeSpecializer & Singleton](
      term: Term[C],
      path: TermPath,
      scope: Scope[C],
      before: List[Piece],
      context: Context[C]
  ): TailRec[List[Piece]] =
    @scala.annotation.tailrec
    def collected(
        current: Term[C],
        currentPath: TermPath,
        steps: List[(String, Term[C], TermPath)]
    ): ((Term[C], TermPath), List[(String, Term[C], TermPath)]) =
      current match
        case DeBruijnTerm.Choice(left, right) =>
          collected(
            right,
            currentPath.below(1),
            ("+", left, currentPath.below(0)) :: steps
          )
        case DeBruijnTerm.Parallel(left, right) =>
          collected(
            left,
            currentPath.below(0),
            ("∥", right, currentPath.below(1)) :: steps
          )
        case _ => ((current, currentPath), steps)
    val ((first, firstPath), steps) = collected(term, path, Nil)
    tailcall(
      rendered(
        first,
        firstPath,
        scope,
        Position.Operand,
        false,
        Vector.empty,
        Piece.Open(Node.Chain) :: before,
        context
      )
    )
      .flatMap(withFirst =>
        Trampoline.folded(steps.toVector, withFirst) {
          case (before, (operator, operand, operandPath)) =>
            rendered(
              operand,
              operandPath,
              scope,
              Position.Operand,
              false,
              Vector.empty,
              Piece.Token(s" $operator ") :: Piece.Open(Node.Step) :: before,
              context
            )
              .map(Piece.Close :: _)
        }
      )
      .map(Piece.Close :: _)
