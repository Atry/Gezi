package gezi.frontend

import gezi.ir.Instruction
import gezi.ir.Spine
import gezi.locations.Span
import parsley.Parsley
import parsley.Parsley.atomic
import parsley.Parsley.eof
import parsley.Parsley.lookAhead
import parsley.Parsley.many
import parsley.Parsley.some
import parsley.combinator.ifS
import parsley.combinator.option
import parsley.character.char
import parsley.character.oneOf
import parsley.character.satisfyMap
import parsley.character.string
import parsley.errors.combinator.ErrorMethods
import parsley.errors.combinator.amend
import parsley.errors.combinator.fail
import parsley.position.offset
import parsley.state.Ref
import parsley.state.StateCombinators
import parsley.syntax.zipped.Zipped2
import parsley.syntax.zipped.Zipped3
import parsley.unicode
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The kind of a token of lambdalattice text. A literal is one token: a
  * text string `"…"` written alone is `StringLiteral`, its text, and every
  * other literal `CborLiteral`.
  */
enum TokenKind:
  case Lambda, Dot, OpenParenthesis, CloseParenthesis, Choice, Parallel, End
  case Name(name: String)
  case StringLiteral(text: String)

  /** A literal other than a top-level text string, the whole literal one
    * token, by the bytes of its CBOR data item.
    */
  case CborLiteral(literal: Literal)

/** A piece of lambdalattice text as it is written: a token, a comment (a
  * `#` comment without the line feed that ends it, which starts the white
  * space after it, or a block comment `/…/`, `/* … */`), or a run of white
  * space. The pieces of a text
  * (`Lambdalattice.lexemes`) written one after another are the text, so a
  * tool that respells a text's layout keeps its names, literals and
  * comments as they are.
  */
enum Lexeme:
  case Token(kind: TokenKind, written: String)
  case Comment(written: String)
  case Space(written: String)

  def written: String

/** What the parser expected where it found another token. */
enum Expectation:
  case End, Atom, CloseParenthesis, Dot, Name, Literal

/** What is wrong with a lambdalattice text, the Prolog front end's
  * `lambdalattice_malformed(Reason)`.
  */
enum LambdalatticeProblem:

  /** A syntax error at the offset, counted in code points from 0. */
  case Syntax(error: SyntaxError, position: Int)

  /** A name no abstraction binds: `_`, which is never bound and which the
    * grammar rejects; a free name of a text read as every text is read
    * unless the call says otherwise (`FreeNames.Rejected`); and, where a
    * call allowed free names, one that the names given to
    * `Defunctionalization.thunkInstruction` lack.
    */
  case UnboundName(name: String)

/** Whether a reading of a lambdalattice text takes a name that no
  * abstraction of the text binds, a free variable. Free variables are
  * rejected (`CONTRIBUTING.md`, "Types live only in the term"): the front
  * end treats one as an error by default, it can be configured to allow
  * them in a rare case, a new use is avoided where possible, and a design
  * that cannot avoid one is discussed before it is written.
  */
enum FreeNames:

  /** The default, which a reading that names no case has: the first name no
    * abstraction of the text binds throws `LambdalatticeMalformed` with
    * `UnboundName`. A text read by this object is read with no context, so
    * it is a closed term. A file of a directory tree is not read this way:
    * the tree is one term, and the file's content stands under the
    * abstractions of its directories, so the front end never reads the file
    * without that context; its text is read by
    * `Lambdalattice.termInScope` in the scope of those names, when
    * `gezi.directorysugar.DirectoryTree` first reaches it.
    */
  case Rejected

  /** The rare case, named at the call: a name no abstraction of the text
    * binds reads as `DeBruijnTerm.Free`. No new call passes it before its
    * design has been discussed.
    */
  case Allowed

/** A syntax error of a lambdalattice text. */
enum SyntaxError:

  /** A code point that starts no token. */
  case UnexpectedCharacter(codePoint: Int)

  /** A token where the grammar expected another. */
  case Expected(expected: Expectation, found: TokenKind)

  /** A string literal with no closing quote. */
  case UnterminatedString

  /** A backslash in a string literal followed by a code point that starts
    * none of the diagnostic notation's escapes.
    */
  case UnknownEscape(codePoint: Int)

  /** A literal that the diagnostic notation does not read
    * (draft-ietf-cbor-edn-literals-29, section 5.1; `DiagnosticNotation`),
    * where its reading stops: a malformed number, string, array or map, a
    * comment `//`, a number touching a letter, a digit or `_`.
    */
  case MalformedLiteral

  /** A part of the diagnostic notation that the reader does not support, at
    * its start (`DiagnosticNotation`): an encoding indicator other than the
    * `_` of an indefinite-length array or map, an application-extension
    * prefix other than `h` and `b64` (a name touching `'` among them), a raw
    * string, embedded CBOR, an indefinite string, an ellipsis, a tag above
    * 2^63 − 1, an item nested deeper than borer writes.
    */
  case UnsupportedDiagnosticNotation

/** A malformed lambdalattice text. */
final case class LambdalatticeMalformed(problem: LambdalatticeProblem)
    extends RuntimeException:
  override def getMessage: String = s"lambdalattice_malformed($problem)"

/** The text syntax of a lambdalattice file, whose content is one term.
  * The port of
  * `gezi/prolog/gezi/lambdalattice.pl`.
  *
  * {{{
  * Term        ::= Application
  *               | Application ('+' Application)+
  *               | Application (('∥' | '||') Application)+
  * Application ::= Abstraction   |   Atom Argument* Abstraction?
  * Abstraction ::= ('λ' | '\') Binder* '.' Application
  * Binder      ::= Name | Literal | '(' Literal ')' 
  * Atom        ::= Name | '(' Term ')'
  * Argument    ::= Atom | Literal | '(' Literal ')'
  * Literal     ::= an item of CBOR's diagnostic notation (LITERALS)
  * Name        ::= a letter, _ or $, then letters, _, $ and 0-9 (NameSpelling)
  * }}}
  *
  * + (U+002B) is the choice and ∥ (U+2225 PARALLEL TO) the parallel.
  * Outside a string, `\` (U+005C) is an ASCII spelling of λ and `||` (two
  * U+007C) of ∥, for text typed on a keyboard, while `text` and every
  * generated text keep λ and ∥; a lone `|` is no token.
  *
  * COMMENTS. A comment is one of CBOR's diagnostic notation
  * (draft-ietf-cbor-edn-literals-29, section 5.1; `DiagnosticNotation`),
  * outside literals as inside them: `#` to the end of the line, ending in a
  * line feed, so a text whose last line is a comment ends with one; `/…/`
  * and `/* … */`, which may span lines; `//` is the syntax error
  * `MalformedLiteral`. `text` and every generated text use `#`.
  *
  * PRECEDENCE. Abstraction and application take precedence over + and ∥, as
  * in M. Dezani-Ciancaglini, U. de'Liguoro and A. Piperno (1996), section
  * 2.1: "To simplify notation we assume that abstraction and application
  * take precedence over + and ∥." An abstraction's body is an application: it extends over the
  * arguments of an application and over the abstraction an application may
  * end with, and stops before + and ∥, so that `λx. a + λy. b` is
  * `(λx. a) + (λy. b)`, and a body that is a choice or a parallel is written
  * in parentheses, `λx. (a + b)`. + and ∥ have one precedence and mix in
  * one chain, left associative like addition and subtraction: `a + b ∥ c` is
  * `(a + b) ∥ c` and `a + b + c` groups as `(a + b) + c`, which the IR
  * nests as the paragraph on chains below says, a right operand that is a
  * chain written in parentheses. Application is left associative too. A λ stands bare wherever an application does, so as
  * an operand of + or ∥, but not as the function of an application nor as an
  * argument other than the last. The last argument of an application may be
  * a bare λ, so that a program in continuation passing style reads as
  * statements, `read λx. write x λ_. x` being `read (λx. write x (λ_. x))`:
  * a trailing λ continues one method, while + joins several; `text` puts the last argument in
  * parentheses. One λ may take several binders, `λn k. M` being
  * `λn. λk. M` and `λx "k" y. M` being `λx. λ"k". λy. M`, each binder, a
  * name or a literal, one abstraction around the rest; `text` writes one λ for each binder. A
  * λ of no binder, `λ. M`, is M: it only extends M over what a bare λ's body
  * extends over, as Haskell's `$`, so that `f λ. g x` is `f (g x)`; `text`
  * never writes it. A
  * name continues over
  * digits, so `f0` is a name. U+222A, U+2229, U+2205
  * and U+2016 are no token: the choice has one spelling, the abstraction
  * and the parallel the two above.
  *
  * LITERALS. A literal is a CBOR data item written in CBOR's diagnostic
  * notation, Concise Diagnostic Notation (draft-ietf-cbor-edn-literals-29,
  * section 5.1), read by `DiagnosticNotation`; its value is the bytes of the
  * item (`Literal`), and inside it only the notation is read, so `true`,
  * `false`, `null`, `undefined`, `Infinity` and `NaN` are keywords there and
  * names or no tokens elsewhere; the one notation serves both the variable
  * arguments and the partial functions' keys. A literal starts with `"`, `'`, `h'`, `b64'`, `[`,
  * `{`, a digit, or `-` touching a digit, so `[a, b]` is a CBOR array, whose
  * items are literals, and no list of terms; a name `h` or `b64` not touching
  * `'` stays a name, and a name touching `'` is the unsupported prefix of a
  * prefixed string. A literal is never a head: a literal alone, as an abstraction's body, as an operand
  * of + or ∥, or as the head of a term in parentheses is the syntax error
  * `Expected(Atom, …)`. It stands in three places:
  *   - a bare argument of an application, `f 30 "k"`, where a number never
  *     takes a following `(`, so `f 30(x)` is `f 30 (x)`, as λ-calculus reads
  *     it;
  *   - alone in parentheses as an argument, `f (30([1, 2]))`, spread as a
  *     bare one, where a number touching `(` is a CBOR tag (the notation's
  *     `tagged = uint spec "(" S item S ")"`, no blank between);
  *   - a binder, `λL. M` and `λ30([1, 2]). M`, a tag allowed as in
  *     parentheses: the variable arguments partial function of the literal
  *     (`Literals.partialFunction`), M after L's bits and top =
  *     Y (λz. λx. z ∥ x) at the first bit that differs. A bare binder holds
  *     no `.` outside its quotes and brackets, so a number in it stops before
  *     the dot, `λ3. M` and `λ12. M` binding integers, and a number with a
  *     fraction is written in parentheses, `λ(3.0). M`, inside which the
  *     notation is read in full, a deliberate
  *     departure from the notation, whose `3.` is 3.0; `λ1e3. M` holds no
  *     `.` and binds 1000.0.
  * As an argument a literal spreads into its variable arguments, the bits of
  * its bytes (`Literals.arguments`). A choice of partial functions maps keys
  * to values: `(λ"k1". a + λ"k2". b) "k1"` is `a + top`. As an argument a
  * number is read as the notation reads it, `f 3.` being `f 3.0`; a literal
  * touching a letter, a digit or `_` after it is malformed. Reading
  * `f 30(x)` by position keeps λ-calculus's reading of an application; the
  * lint rules that would warn on such texts are TODOs at their sites.
  *
  * A chain of n >= 2 operands of + and ∥ is a chain of n - 1 binary choices
  * and parallels, each operator taking the chain before it and the operand
  * after it: a ∥ has the chain as its left side and the operand as its
  * right, a + the operand as its left side and the chain as its right. So a
  * chain
  * of ∥ nests to the left, `a ∥ b ∥ c` being `(a ∥ b) ∥ c`, and a chain of +
  * nests to the right with its members in the reverse of the text's order,
  * `c + b + a` being the IR's `a + (b + c)`, as the chains the IR's readers
  * walk (`gezi.ir.ChoiceSpine`) nest. A chain of one operand is that
  * operand, and a chain in parentheses stays an operand of its own, so
  * `a + (b + c)` is the choice whose left side is `b + c` and whose right
  * side is `a`.
  *
  * STATEMENTS. A session's cells are no new form of the grammar: the cells
  * joined are one program text that ends with an abstraction's binders and
  * its `.`, and `Statement` reads it by completing it into a closed term of
  * this grammar, a fresh hole name written as the last abstraction's body and
  * the parentheses left open closed, the hole then applied to the values
  * bound there by their de Bruijn variables; neither the precedence nor the
  * grammar changes for it.
  *
  * NAMES: a text is a closed term. A name that an abstraction of the text
  * binds is the de Bruijn variable of the innermost such abstraction; any
  * other name is an error, `UnboundName`, unless the call allows free names
  * (`FreeNames`), the rare case, in which the name reads as `Free(name)` of
  * the locally nameless term (`DeBruijnTerm`) and
  * `Defunctionalization.thunkInstruction` looks it up in the names it is
  * given. The grammar reads a name without a table of names either way, so
  * that it is compiled once. A name bound by `_` cannot be referenced: `_`
  * in a value position throws `UnboundName("_")` where it stands.
  */
object Lambdalattice:

  /** A text read in one parse: its locally nameless term, and the names it
    * uses free, each once, in the order of their first occurrences, none
    * unless the reading allowed them (`FreeNames.Allowed`). The free names
    * are gathered by the parse itself, so that reading them walks the term
    * no second time.
    */
  final case class ParsedText(term: DeBruijnTerm, freeNames: Vector[String])

  /** The text read as a closed term (`FreeNames.Rejected`). Throws
    * `LambdalatticeMalformed` with `Syntax` on a syntax error and with
    * `UnboundName` on a reference to `_` and for the first name of the text
    * that none of its abstractions binds.
    */
  def parse(text: String): ParsedText =
    parse(text, FreeNames.Rejected)

  /** The text read (`ParsedText`), its free names an error or read as the
    * case says (`FreeNames`). Throws `LambdalatticeMalformed` with `Syntax`
    * on a syntax error, with `UnboundName("_")` on a reference to `_`, and,
    * where free names are rejected, with `UnboundName` for the first of
    * them.
    */
  def parse(text: String, freeNames: FreeNames): ParsedText =
    val (read, names) = checkedRead(text, freeNames)
    ParsedText(read.term, names)

  /** A text read with the spans of its term's nodes, in code points
    * (`SyntaxSpans`), and its free names as `ParsedText` has them.
    */
  final case class LocatedText(term: DeBruijnTerm, spans: SyntaxSpans, freeNames: Vector[String])

  /** The text read as `parse` reads it, with the spans of its term's nodes:
    * the term is the term `parse` gives. Throws the errors of `parse`.
    */
  def located(text: String, freeNames: FreeNames): LocatedText =
    val (read, names) = checkedRead(text, freeNames)
    LocatedText(read.term, inCodePoints(read.spans, text), names)

  /** The read and the free names of the text, its free names an error or
    * read as the case says.
    */
  private def checkedRead(text: String, freeNames: FreeNames): (Read, Vector[String]) =
    grammar.read(text) match
      case Left(failure) => throw rejected(text, failure)
      case Right((read, occurrences)) =>
        val names = occurrences.reverse.distinct.toVector
        freeNames match
          case FreeNames.Allowed => (read, names)
          case FreeNames.Rejected =>
            names.headOption.foreach(name => throw LambdalatticeMalformed(LambdalatticeProblem.UnboundName(name)))
            (read, names)

  /** The spans counted in code points instead of the UTF-16 code units the
    * grammar counts in; the same spans for a text with no supplementary
    * code point.
    */
  private def inCodePoints(spans: SyntaxSpans, text: String): SyntaxSpans =
    if text.codePointCount(0, text.length) == text.length then spans
    else
      val counted = IArray.tabulate(text.length + 1)(unit => text.codePointCount(0, unit))
      def span(read: Span): Span = Span(counted(read.start), counted(read.end))
      def converted(read: SyntaxSpans): TailRec[SyntaxSpans] = read match
        case SyntaxSpans.Written(own, parentheses, children, binder) =>
          Trampoline
            .folded(children.toVector, Vector.empty[SyntaxSpans])((written, child) => converted(child).map(written :+ _))
            .map(SyntaxSpans.Written(span(own), parentheses.map(span), _, binder.map(binderSpanned)))
        case SyntaxSpans.Generated(own, parentheses, written, binders) =>
          Trampoline
            .folded(written.toVector, Vector.empty[(Vector[Int], SyntaxSpans)])((found, embedded) =>
              converted(embedded._2).map(found :+ (embedded._1, _))
            )
            .map(SyntaxSpans.Generated(span(own), parentheses.map(span), _, binders.map((path, binder) => (path, binderSpanned(binder)))))
      def binderSpanned(binder: SpelledBinder): SpelledBinder = binder match
        case SpelledBinder.Named(name, at)               => SpelledBinder.Named(name, span(at))
        case SpelledBinder.LiteralBit(literal, bit, at) => SpelledBinder.LiteralBit(literal, bit, span(at))
        case enclosing: SpelledBinder.Enclosing         => enclosing
      converted(spans).result

  /** The closed term the text spells. Throws the errors of `parse`, among
    * them `UnboundName` for a name that no abstraction of the text binds.
    */
  def term(text: String): DeBruijnTerm =
    parse(text).term

  /** The locally nameless term the text spells, its free names an error or
    * read as the case says (`FreeNames`). Throws the errors of `parse`.
    */
  def term(text: String, freeNames: FreeNames): DeBruijnTerm =
    parse(text, freeNames).term

  /** The closed term `λd1. … λdn. M` of the text M read in the scope of the
    * enclosing names d1 … dn, d1 the outermost: a name that no abstraction of
    * the text binds is the variable of the innermost enclosing name that
    * spells it. A file of a directory tree is read this way, under its
    * directories' and its own self, the names it uses of them being bound
    * variables, never free names. Throws the errors of `parse`,
    * `UnboundName` for the first name of the text that neither an abstraction
    * of the text nor an enclosing name binds, and `IllegalArgumentException`
    * for an enclosing name that the rule Name does not spell.
    */
  def termInScope(enclosing: Vector[String], text: String): DeBruijnTerm =
    readInScope(enclosing, text).term

  /** The term `termInScope` reads, with the spans of its nodes in code
    * points: the abstractions of the enclosing names are generated, spanning
    * the whole text, the text's term written under them. Throws the errors
    * of `termInScope`.
    */
  def locatedInScope(enclosing: Vector[String], text: String): (DeBruijnTerm, SyntaxSpans) =
    val read = readInScope(enclosing, text)
    (read.term, inCodePoints(read.spans, text))

  private def readInScope(enclosing: Vector[String], text: String): Read =
    enclosing
      .find(!isName(_))
      .foreach(name => throw IllegalArgumentException(s"an enclosing name that the rule Name does not spell: $name"))
    grammar.read(text) match
      case Left(failure) => throw rejected(text, failure)
      case Right((body, occurrences)) =>
        occurrences.reverse
          .find(!enclosing.contains(_))
          .foreach(name => throw LambdalatticeMalformed(LambdalatticeProblem.UnboundName(name)))
        // A later name of the same spelling overwrites an earlier one, so each
        // name maps to its innermost binder.
        val levels = enclosing.zipWithIndex.toMap
        val term = enclosing.foldLeft(enclosingBound(body.term, levels, enclosing.size, 0).result)((inner, _) =>
          DeBruijnTerm.Lambda(inner)
        )
        if enclosing.isEmpty then Read(term, body.spans)
        else
          Read(
            term,
            SyntaxSpans.Generated(
              Span(0, text.length),
              Vector.empty,
              Vector((Vector.fill(enclosing.size)(0), body.spans)),
              enclosing.zipWithIndex.map((name, level) => Vector.fill(level)(0) -> SpelledBinder.Enclosing(name))
            )
          )

  /** The term with each `Free(name)` replaced by the variable of the
    * enclosing binder at `levels(name)`, 0 the outermost of `count`, the
    * replaced name standing under `depth` abstractions of the term.
    */
  private def enclosingBound(
      term: DeBruijnTerm,
      levels: Map[String, Int],
      count: Int,
      depth: Int
  ): TailRec[DeBruijnTerm] =
    term match
      case DeBruijnTerm.Free(name) =>
        val level =
          levels.getOrElse(name, throw IllegalStateException(s"a free name checked against the enclosing names: $name"))
        done(DeBruijnTerm.Variable(depth + count - 1 - level))
      case DeBruijnTerm.Lambda(body) =>
        tailcall(enclosingBound(body, levels, count, depth + 1)).map(DeBruijnTerm.Lambda(_))
      case DeBruijnTerm.Apply(function, argument) =>
        for
          boundFunction <- tailcall(enclosingBound(function, levels, count, depth))
          boundArgument <- tailcall(enclosingBound(argument, levels, count, depth))
        yield DeBruijnTerm.Apply(boundFunction, boundArgument)
      case DeBruijnTerm.Choice(left, right) =>
        for
          boundLeft <- tailcall(enclosingBound(left, levels, count, depth))
          boundRight <- tailcall(enclosingBound(right, levels, count, depth))
        yield DeBruijnTerm.Choice(boundLeft, boundRight)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          boundLeft <- tailcall(enclosingBound(left, levels, count, depth))
          boundRight <- tailcall(enclosingBound(right, levels, count, depth))
        yield DeBruijnTerm.Parallel(boundLeft, boundRight)
      case leaf @ (DeBruijnTerm.Variable(_) | DeBruijnTerm.Constant(_)) => done(leaf)

  /** The closed term the code points spell, as for a string. */
  def term(codePoints: Vector[Int]): DeBruijnTerm =
    term(codePoints.map(Character.toString(_)).mkString)

  /** The names the text uses that no enclosing abstraction binds, each once,
    * sorted: what a reading that rejects free names (`FreeNames.Rejected`)
    * would refuse the text for. Throws the errors of `parse` but
    * `UnboundName` for a free name.
    */
  def freeNames(text: String): Vector[String] =
    parse(text, FreeNames.Allowed).freeNames.sorted

  /** Whether the atom is spelled by the rule Name of the grammar
    * (`NameSpelling`).
    */
  def isName(atom: String): Boolean = NameSpelling.isName(atom)

  /** The text of the de Bruijn term, which `term` reads back to the same
    * term with each constant of the names read as the free name it maps to
    * and each free name as itself, with the fewest parentheses the grammar
    * allows: an abstraction bare wherever an application stands (at the top,
    * as a body, as an operand of + or ∥, inside parentheses), a body that is a
    * choice or a parallel in parentheses; a chain of choices nested in their
    * right sides and of parallels nested in their left sides as one chain of
    * `+` and `∥`, a choice's right side written before its `+` and its left
    * side after it, and an operand after a `+` or a `∥` that is a choice or a
    * parallel in parentheses; an application as a chain
    * nested to the left, a function that is an abstraction and an argument
    * that is not a name in parentheses. The variable an abstraction binds at
    * level L (the number of abstractions outside it) is named `x_L`.
    * Throws `IllegalArgumentException` for a variable no
    * abstraction binds, for a constant whose instruction the names do not map to a
    * name of the grammar or map to a name of the form `x_L`, and for a free
    * name that is no name of the grammar, is `_` or is of the form `x_L`. Stack
    * safe: the walk is a trampoline, so a chain of any depth renders, and
    * linear in the text's length: a fragment is prepended in constant time
    * and the text is joined once.
    */
  def text(term: DeBruijnTerm, names: Map[Instruction, String]): String =
    rendered(term, 0, Position.Whole, List.empty, names, false).result.reverse.mkString

  /** `text` with the literals the reader spreads written back as literals: a
    * variable arguments partial function, a chain of abstractions
    * `λx. x K top` (a 1) and `λx. x top K` (a 0) whose bits make up complete
    * literals and whose body reads none of their binders, as `λL. M`; and a
    * run of arguments that are the closed Scott booleans `λt. λf. t` and
    * `λt. λf. f` making up complete literals, as those literals
    * (`Literals.partialFunction`, `Literals.arguments`). The reader reads the
    * text to the same term, since it spreads each literal into the bits it
    * was gathered from. A marker spelled as a tag,
    * `λx. (λ"__constructor". λv. v) "__constructor" x` (the key's spelling
    * before synthetic labels took the prefix `$`, 13 bytes),
    * is a text of 14,127 characters with its bits written out, the miss top
    * spelled in full at each of the 104, against 47 written with its literal
    * (measured 2026-11-19).
    */
  def textWithLiterals(term: DeBruijnTerm, names: Map[Instruction, String]): String =
    rendered(term, 0, Position.Whole, List.empty, names, true).result.reverse.mkString

  /** The text of the closed instruction's readback
    * (`Defunctionalization.instructionTerm`), its literals written back
    * (`textWithLiterals`), with no name: a text the reader reads as the
    * readback, which a trace writes for its terms
    * (`gezi.rewritetrace.TraceText`) and a message or a snapshot shows.
    * Its size is the readback's, a tree's; the exchange format
    * (`ExchangeText`) writes an instruction at the size of its graph.
    * Throws `IllegalArgumentException` for an instruction holding an opaque
    * instruction, which reads back as a constant.
    */
  def closedText(instruction: Instruction): String =
    textWithLiterals(Defunctionalization.instructionTerm(instruction), Map.empty)

  /** The complete literals a chain of variable arguments partial function
    * abstractions at the term begins with, the term under their bits, and
    * the number of the bits, when there is at least one literal and the term
    * under the bits reads none of their binders.
    */
  private def literalBinders(term: DeBruijnTerm): Option[(Vector[LiteralWriting.Written], DeBruijnTerm, Int)] =
    @scala.annotation.tailrec
    def collected(current: DeBruijnTerm, bits: Vector[Boolean], under: Vector[DeBruijnTerm]): (Vector[Boolean], Vector[DeBruijnTerm]) =
      current match
        case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), first), second))
            if second == Literals.top && first != Literals.top =>
          collected(first, bits :+ true, under :+ first)
        case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), first), second))
            if first == Literals.top && second != Literals.top =>
          collected(second, bits :+ false, under :+ second)
        case _ => (bits, under)
    val (bits, under) = collected(term, Vector.empty, Vector.empty)
    val written = LiteralWriting.items(bytesOf(bits))
    val count = written.map(_.literal.bytes.length).sum * 8
    Option.when(count > 0 && !DeBruijnTerm.readsBelow(under(count - 1), count))((written, under(count - 1), count))

  /** The bytes of the bits, each byte high bit first; the bits after the last
    * whole byte dropped.
    */
  private def bytesOf(bits: Vector[Boolean]): Vector[Byte] =
    bits.grouped(8).filter(_.size == 8).map(byte => byte.foldLeft(0)((value, bit) => value * 2 + (if bit then 1 else 0)).toByte).toVector

  /** An argument of an application as the literal mode writes it: a
    * complete literal, or a term.
    */
  private enum WrittenArgument:
    case Literal(written: LiteralWriting.Written)
    case Term(term: DeBruijnTerm)

  /** The arguments, each run of closed Scott booleans that makes up complete
    * literals written as those literals, the bits after the last complete
    * one as terms.
    */
  private def literalArguments(arguments: Vector[DeBruijnTerm]): Vector[WrittenArgument] =
    def isBit(argument: DeBruijnTerm): Boolean = argument == Literals.one || argument == Literals.zero
    @scala.annotation.tailrec
    def grouped(rest: Vector[DeBruijnTerm], found: Vector[WrittenArgument]): Vector[WrittenArgument] =
      rest.headOption match
        case None => found
        case Some(argument) if !isBit(argument) => grouped(rest.tail, found :+ WrittenArgument.Term(argument))
        case Some(_) =>
          val run = rest.takeWhile(isBit)
          val written = LiteralWriting.items(bytesOf(run.map(_ == Literals.one)))
          val count = written.map(_.literal.bytes.length).sum * 8
          grouped(rest.drop(run.size), found ++ written.map(WrittenArgument.Literal(_)) ++ run.drop(count).map(WrittenArgument.Term(_)))
    grouped(arguments, Vector.empty)

  /** Where a subterm stands in the grammar. */
  private enum Position:
    /** At the top or inside parentheses: any term. */
    case Whole

    /** The operand before a `+` or a `∥` (a choice's right side, a
      * parallel's left side): a chain of them, an application or an
      * abstraction.
      */
    case ChainLeft

    /** A body, the operand after a `+` or a `∥` (a choice's left side, a
      * parallel's right side): an application or an abstraction.
      */
    case Application

    /** The function of an application: an application or an atom. */
    case Function

    /** An argument: a name. */
    case Atom

  /** Whether the term stands at the position with no parentheses. */
  private def fits(term: DeBruijnTerm, position: Position): Boolean =
    (term, position) match
      case (_, Position.Whole)                                                => true
      case (DeBruijnTerm.Choice(_, _) | DeBruijnTerm.Parallel(_, _), Position.ChainLeft) => true
      case (DeBruijnTerm.Choice(_, _) | DeBruijnTerm.Parallel(_, _), _)       => false
      case (DeBruijnTerm.Lambda(_), Position.Function | Position.Atom)        => false
      case (DeBruijnTerm.Lambda(_), _)                                        => true
      case (DeBruijnTerm.Apply(_, _), Position.Atom)                          => false
      case (DeBruijnTerm.Apply(_, _), _)                                      => true
      case (DeBruijnTerm.Variable(_) | DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_), _) => true
      case (other, _) =>
        throw IllegalStateException(
          s"a de Bruijn term is a variable, an abstraction, an application, a constant, a free name, a choice or a parallel, not ${other.layer}"
        )

  private val boundVariableName: scala.util.matching.Regex = "x_[0-9]+".r

  /** The fragments of the text before the term, most recent first, followed
    * by the term's own.
    */
  private def rendered(
      term: DeBruijnTerm,
      depth: Int,
      position: Position,
      before: List[String],
      names: Map[Instruction, String],
      literals: Boolean
  ): TailRec[List[String]] =
    if !fits(term, position) then
      tailcall(rendered(term, depth, Position.Whole, "(" :: before, names, literals)).map(")" :: _)
    else
      term match
        case DeBruijnTerm.Lambda(body) =>
          (if literals then literalBinders(term) else None) match
            case Some((written, under, count)) =>
              val withBinders = written.foldLeft(before)((fragments, literal) => s"λ${LiteralWriting.binder(literal)}. " :: fragments)
              tailcall(rendered(DeBruijnTerm.shiftedDown(under, count), depth, Position.Application, withBinders, names, literals))
            case None =>
              tailcall(rendered(body, depth + 1, Position.Application, s"λx_$depth. " :: before, names, literals))
        case DeBruijnTerm.Choice(left, right) =>
          tailcall(rendered(right, depth, Position.ChainLeft, before, names, literals)).flatMap(withRight =>
            tailcall(rendered(left, depth, Position.Application, " + " :: withRight, names, literals))
          )
        case DeBruijnTerm.Parallel(left, right) =>
          tailcall(rendered(left, depth, Position.ChainLeft, before, names, literals)).flatMap(withLeft =>
            tailcall(rendered(right, depth, Position.Application, " ∥ " :: withLeft, names, literals))
          )
        case DeBruijnTerm.Apply(_, _) if literals =>
          val (head, arguments) = Spine.of(term)
          tailcall(rendered(head, depth, Position.Function, before, names, literals)).flatMap(withHead =>
            Trampoline.folded(literalArguments(arguments).toVector, withHead)((fragments, argument) =>
              argument match
                case WrittenArgument.Literal(literal) => done(LiteralWriting.argument(literal) :: " " :: fragments)
                case WrittenArgument.Term(argumentTerm) =>
                  tailcall(rendered(argumentTerm, depth, Position.Atom, " " :: fragments, names, literals))
            )
          )
        case DeBruijnTerm.Apply(function, argument) =>
          tailcall(rendered(function, depth, Position.Function, before, names, literals)).flatMap(withFunction =>
            tailcall(rendered(argument, depth, Position.Atom, " " :: withFunction, names, literals))
          )
        case DeBruijnTerm.Variable(index) =>
          val level = depth - index - 1
          if index < 0 || level < 0 then
            throw IllegalArgumentException(s"no abstraction binds the variable $index at depth $depth")
          done(s"x_$level" :: before)
        case DeBruijnTerm.Constant(instruction) =>
          val name = names.getOrElse(instruction, throw IllegalArgumentException(s"no name for the $instruction"))
          if !isName(name) || boundVariableName.matches(name) then
            throw IllegalArgumentException(s"$name is no lambdalattice name of a constant")
          done(name :: before)
        case DeBruijnTerm.Free(name) =>
          if !isName(name) || name == "_" || boundVariableName.matches(name) then
            throw IllegalArgumentException(s"$name is no lambdalattice free name")
          done(name :: before)

  // ---- the lexer and the grammar, written with Parsley ----
  //
  // The user, 2026-11-09: "Please migrate the parsers all to Parsley".
  // Parsley's machine keeps its stack on the heap, so a term of any depth
  // reads without the JVM stack. The text is read twice: first its tokens
  // alone (`tokens`), so that a code point that starts no token, a string
  // with no closing quote and an unknown escape are reported before any
  // error of the grammar; then the grammar, scannerless, each token followed
  // by the layout after it (`parse`: the grammar, compiled once, which needs
  // no table of names). A syntax error fails the parse with one message
  // (`ParsleyFailure`), raised at the token where the grammar finds no way on
  // (the alternative left when every other has failed without reading; the
  // grammar is LL(1)), or, with `amend`, at the start of the construct it
  // breaks; a reference to `_` fails the parse the same way, where the name
  // stands. `rejection` reads the failure back into the
  // exception the reader throws; the token found at a syntax error is lexed
  // again from its offset. No error is thrown from a parser's action:
  // Parsley's optimizer takes actions to be pure, drops the action of a
  // result it discards, and may run an action before a parser sequenced
  // after it (`ParsleyFailure`). Every `atomic` alternative is amended, so
  // that its error stands where it started and does not outrun the error of
  // the alternative after it (Parsley keeps the error that stands furthest).

  /** White space as SWI-Prolog's `code_type(Code, space)` reads it, to the
    * extent Java's classification of white space and space characters
    * agrees with it.
    */
  private def space(codePoint: Int): Boolean =
    Character.isWhitespace(codePoint) || Character.isSpaceChar(codePoint)

  /** The messages of the failures the lexer and the grammar raise, each read
    * back into the exception it stands for by `rejection`.
    */
  private[frontend] object Raised:
    val unexpectedCharacter: String = "UnexpectedCharacter"
    val unterminatedString: String = "UnterminatedString"
    val unknownEscape: String = "UnknownEscape"
    val malformedLiteral: String = "MalformedLiteral"
    val unsupportedNotation: String = "UnsupportedDiagnosticNotation"
    val expected: String = "Expected "
    val unboundName: String = "UnboundName "

  /** The parser, an alternative that reads nothing when it fails, its error
    * where it started.
    */
  private def backtracking[A](parser: Parsley[A]): Parsley[A] = amend(atomic(parser))

  /** The tokens of lambdalattice text, without the layout around them. */
  private object Lexer:

    /** White space and the diagnostic notation's comments
      * (`DiagnosticNotation.commentBeforeLineFeed`).
      */
    val layout: Parsley[Unit] =
      many(unicode.satisfy(space).void | DiagnosticNotation.commentBeforeLineFeed).void

    /** A name. A name touching `'` or `` ` `` would be the prefix of a
      * prefixed string of the diagnostic notation, `dt'…'`, which is
      * unsupported (`SyntaxError.UnsupportedDiagnosticNotation`) at the name;
      * `h'…'` and `b64'…'` are literals, read before a name wherever one may
      * stand.
      */
    val name: Parsley[String] =
      (
        (unicode.satisfy(NameSpelling.isStart), many(unicode.satisfy(NameSpelling.isContinuation))).zipped((first, rest) =>
          (first :: rest).map(Character.toString(_)).mkString
        ),
        option(lookAhead(oneOf('\'', '`')))
      ).zipped((_, _)).collectMsg(_ => Seq(Raised.unsupportedNotation)) { case (written, None) => written }

    private val punctuation: Map[Char, TokenKind] = Map(
      'λ' -> TokenKind.Lambda,
      '\\' -> TokenKind.Lambda,
      '.' -> TokenKind.Dot,
      '(' -> TokenKind.OpenParenthesis,
      ')' -> TokenKind.CloseParenthesis,
      '+' -> TokenKind.Choice,
      '∥' -> TokenKind.Parallel
    )

    /** A literal where a number never takes a following `(`, a bare
      * argument (`DiagnosticNotation.argumentLiteral`).
      */
    val argumentLiteral: Parsley[Literal] = DiagnosticNotation.argumentLiteral.map(_._2)

    /** A literal where a number touching `(` is a tag, alone in parentheses
      * as an argument or a binder (`DiagnosticNotation.parenthesizedLiteral`).
      */
    val parenthesizedLiteral: Parsley[Literal] = DiagnosticNotation.parenthesizedLiteral.map(_._2)

    /** A bare binder, whose literal holds no `.` outside its quotes and
      * brackets (`DiagnosticNotation.binderLiteral`).
      */
    val binderLiteral: Parsley[Literal] = DiagnosticNotation.binderLiteral.map(_._2)

    /** The token of a literal: a text string alone is `StringLiteral`. */
    private def literalToken(read: (io.bullet.borer.Dom.Element, Literal)): TokenKind = read match
      case (io.bullet.borer.Dom.StringElem(text), _) => TokenKind.StringLiteral(text)
      case (_, literal)                              => TokenKind.CborLiteral(literal)

    /** A token: `||` is the ASCII spelling of `∥`, and a lone `|`, like any
      * code point that starts no token, is malformed. A literal is one token,
      * read by the parser of the literal's place.
      */
    private def token(literal: Parsley[(io.bullet.borer.Dom.Element, Literal)]): Parsley[TokenKind] =
      backtracking(string("||")).as(TokenKind.Parallel) |
        satisfyMap(punctuation) |
        literal.map(literalToken) |
        name.map(TokenKind.Name(_)) |
        amend(unicode.item.collectMsg(_ => Seq(Raised.unexpectedCharacter))(PartialFunction.empty))

    private val argumentToken: Parsley[TokenKind] = token(DiagnosticNotation.argumentLiteral)

    private val headToken: Parsley[TokenKind] = token(DiagnosticNotation.parenthesizedLiteral)

    private val binderToken: Parsley[TokenKind] = token(DiagnosticNotation.binderLiteral)

    /** The token at the start of a text, or the end of the text, a number
      * taking no `(`: the token the grammar found where it expected another.
      */
    val tokenOrEnd: Parsley[TokenKind] = argumentToken | eof.as(TokenKind.End)

    /** Where the lexer stands, which decides how a literal is read there,
      * as the grammar reads it:
      * after a name, a `)` or a literal a bare argument may
      * follow, where a number touching `(` is no tag (`Argument`); among the
      * binders of a λ a number touching `(` is a tag and holds no `.`
      * (`Binder`); inside parentheses among the binders, and everywhere else,
      * where a literal would be a head or alone in parentheses, a number
      * touching `(` is a tag (`BinderParenthesis`, `Head`).
      */
    private enum Place:
      case Head, Argument, Binder, BinderParenthesis

    /** The place after a token read at the place. */
    private def following(current: Place, kind: TokenKind): Place = (current, kind) match
      case (_, TokenKind.Lambda)                                 => Place.Binder
      case (Place.Binder, TokenKind.OpenParenthesis)             => Place.BinderParenthesis
      case (Place.Binder, TokenKind.Dot)                         => Place.Head
      case (Place.Binder, _)                                     => Place.Binder
      case (Place.BinderParenthesis, TokenKind.CloseParenthesis) => Place.Binder
      case (Place.BinderParenthesis, _)                          => Place.BinderParenthesis
      case (_, TokenKind.Name(_) | TokenKind.CloseParenthesis | TokenKind.StringLiteral(_) | TokenKind.CborLiteral(_)) =>
        Place.Argument
      case _ => Place.Head

    /** A parser that starts a text and a parser of its next token, read as
      * its place says, the place moved past it. Each call makes its own
      * Parsley reference of the place, for one top-level parser: a reference
      * shared by two top-level parsers is compiled into the registers of the
      * first and overruns those of a smaller second (an
      * ArrayIndexOutOfBoundsException met on 2026-11-16).
      */
    def placedTokens(): (Parsley[Unit], Parsley[TokenKind]) =
      val place: Ref[Place] = Ref.make
      (
        place.set(Place.Head),
        ifS(
          place.gets(_ == Place.Argument),
          argumentToken,
          ifS(place.gets(_ == Place.Binder), binderToken, headToken)
        ).fillRef(read => place.update(read.gets(kind => (current: Place) => following(current, kind))) ~> read.get)
      )

    /** Every token of the text, the layout skipped. */
    val tokens: Parsley[Vector[TokenKind]] =
      val (started, placedToken) = placedTokens()
      started ~> layout ~> many(placedToken <~ layout).map(_.toVector) <~ eof

  /** The pieces of the text as written (`Lexeme`), in order; their written
    * texts joined are the text. Throws the lexer's syntax errors, those
    * `parse` throws for a token it cannot read.
    */
  def lexemes(text: String): Vector[Lexeme] =
    lexemePieces.parse[ParsleyFailure](text).toEither match
      case Right(read)   => read.map(_(text))
      case Left(failure) => throw rejection(text, failure)

  /** The parser of `lexemes`, made and compiled once: each piece a function
    * of the text it was read from, which cuts the piece's written text out
    * of it, so that the parser holds no text. Made inside `lexemes`, the
    * parser closed over its text and was built and compiled again at every
    * call, a fixed cost of about 15 ms (the FFI session's reading of
    * 2026-11-20: 17 characters 15 ms, a hundred copies of them joined 27 ms).
    * Its own Parsley
    * reference of the place, one top-level parser (`Lexer.placedTokens`).
    */
  private val lexemePieces: Parsley[Vector[String => Lexeme]] =
    val (started, placedToken) = Lexer.placedTokens()
    val piece: Parsley[String => Lexeme] =
      some(unicode.satisfy(space)).map(codePoints =>
        val written = codePoints.map(Character.toString(_)).mkString
        (_: String) => Lexeme.Space(written)
      ) |
        (offset, DiagnosticNotation.commentBeforeLineFeed, offset).zipped((start, _, end) =>
          (text: String) => Lexeme.Comment(text.substring(start, end))
        ) |
        (offset, placedToken, offset).zipped((start, kind, end) => (text: String) => Lexeme.Token(kind, text.substring(start, end)))
    started ~> many(piece).map(_.toVector) <~ eof

  /** The exception of a text the grammar rejected with the failure: the
    * lexer's error when the lexer rejects the text too, read first as before
    * the grammar, so that a lexical error is reported as one; the grammar's
    * otherwise. The lexer is read only when the grammar fails: a text the
    * grammar reads is one the lexer reads, its places (`Lexer.Place`)
    * following the grammar's and its tokens read by the grammar's parsers
    * (`LexerOfReadTextLawTest`), and reading it first on every text took 27%
    * of the parse's JFR samples in TrapJudgmentsLawTest on 2026-11-20.
    */
  private def rejected(text: String, failure: ParsleyFailure): RuntimeException =
    val _ = tokens(text)
    rejection(text, failure)

  /** The tokens of the text, read for their errors and their names. */
  private[frontend] def tokens(text: String): Vector[TokenKind] =
    Lexer.tokens.parse[ParsleyFailure](text).toEither match
      case Right(read)   => read
      case Left(failure) => throw rejection(text, failure)

  /** The exception a failure of the lexer or the grammar stands for: a
    * reference to `_`, or a syntax error at the failure's offset in code
    * points.
    */
  private def rejection(text: String, failure: ParsleyFailure): RuntimeException =
    failure.message match
      case message if message.startsWith(Raised.unboundName) =>
        LambdalatticeMalformed(LambdalatticeProblem.UnboundName(message.stripPrefix(Raised.unboundName)))
      case _ => syntaxError(text, failure)

  /** The syntax error a failure of the lexer or the grammar raised, at its
    * offset in code points.
    */
  private def syntaxError(text: String, failure: ParsleyFailure): LambdalatticeMalformed =
    val offset = failure.offset(text)
    def found: TokenKind = Lexer.tokenOrEnd.parse[ParsleyFailure](text.substring(offset)).toEither match
      case Right(token) => token
      case Left(other) =>
        throw IllegalStateException(s"no token at the offset $offset of a text the lexer read: $other")
    val error = failure.message match
      case Raised.unexpectedCharacter => SyntaxError.UnexpectedCharacter(text.codePointAt(offset))
      case Raised.unterminatedString  => SyntaxError.UnterminatedString
      case Raised.unknownEscape       => SyntaxError.UnknownEscape(text.codePointAt(offset))
      case Raised.malformedLiteral    => SyntaxError.MalformedLiteral
      case Raised.unsupportedNotation => SyntaxError.UnsupportedDiagnosticNotation
      case message if message.startsWith(Raised.expected) =>
        SyntaxError.Expected(Expectation.valueOf(message.stripPrefix(Raised.expected)), found)
      case message => throw IllegalStateException(s"a failure no syntax error stands for: $message")
    LambdalatticeMalformed(LambdalatticeProblem.Syntax(error, text.codePointCount(0, offset)))

  /** The scope of a subterm: the level of the innermost abstraction that
    * binds each name, and the number of abstractions around it.
    */
  private final case class Scope(levels: Map[String, Int], depth: Int, innermost: String):
    def bound(name: String): Scope =
      Scope(levels.updated(name, depth), depth + 1, name)

  /** A node the grammar read: its term and the spans of the term's nodes,
    * in UTF-16 code units until `located` counts them in code points. A
    * node's extent is its span with the parentheses around it.
    */
  private final case class Read(term: DeBruijnTerm, spans: SyntaxSpans):
    def extent: Span = spans.parentheses.lastOption.getOrElse(spans.span)

    def parenthesized(outer: Span): Read = Read(term, spans.parenthesized(outer))

  private object Read:

    /** A generated node of no written subterm. */
    def generated(term: DeBruijnTerm, span: Span): Read =
      Read(term, SyntaxSpans.Generated(span, Vector.empty, Vector.empty, Vector.empty))

    /** The read whose own span starts at the offset instead, as an
      * abstraction's starts at its λ.
      */
    def startingAt(start: Int, read: Read): Read =
      val widened = Span(start, read.spans.span.end)
      Read(
        read.term,
        read.spans match
          case written: SyntaxSpans.Written     => written.copy(span = widened)
          case generated: SyntaxSpans.Generated => generated.copy(span = widened)
      )

    /** The abstraction of the name written at the offset over the body. */
    def abstraction(start: Int, name: String, body: Read): Read =
      Read(
        DeBruijnTerm.Lambda(body.term),
        SyntaxSpans.Written(
          Span(start, body.extent.end),
          Vector.empty,
          Vector(body.spans),
          Some(SpelledBinder.Named(name, Span(start, start + name.length)))
        )
      )

    def application(function: Read, argument: Read): Read =
      Read(
        DeBruijnTerm.Apply(function.term, argument.term),
        SyntaxSpans.Written(
          Span(function.extent.start, argument.extent.end),
          Vector.empty,
          Vector(function.spans, argument.spans),
          None
        )
      )

    def parallel(left: Read, right: Read): Read =
      Read(
        DeBruijnTerm.Parallel(left.term, right.term),
        SyntaxSpans.Written(Span(left.extent.start, right.extent.end), Vector.empty, Vector(left.spans, right.spans), None)
      )

    /** The choice of the chain before a + and the operand after it, the
      * operand its left side and the chain its right, so that the text
      * `c + b + a` is the IR's right-nested `a + (b + c)`. It spans
      * from the chain's start to the operand's end; its spans list the
      * operand's before the chain's, in the order of the term's sides.
      */
    def choice(chain: Read, operand: Read): Read =
      Read(
        DeBruijnTerm.Choice(operand.term, chain.term),
        SyntaxSpans.Written(Span(chain.extent.start, operand.extent.end), Vector.empty, Vector(operand.spans, chain.spans), None)
      )

    /** The variable arguments a literal argument spreads into, each spanning
      * the literal, the binders of each bit named `t` and `f`.
      */
    def arguments(literal: (Literal, Span)): Vector[Read] =
      val (read, span) = literal
      val binders = Vector(Vector() -> SpelledBinder.Named("t", span), Vector(0) -> SpelledBinder.Named("f", span))
      Literals.arguments(read).map(bit => Read(bit, SyntaxSpans.Generated(span, Vector.empty, Vector.empty, binders)))

    /** The variable arguments partial function of the literal over the body, spanning
      * from the literal to the body's end, the body written at its path.
      */
    def partialFunction(literal: (Literal, Span), body: Read): Read =
      val (read, span) = literal
      val extent = Span(span.start, body.extent.end)
      // Each bit's level is a generated node of its own, the next level (the
      // body after the last bit) written below it at the bit's step: in the
      // function of its application to the rest for a 1 (`λx. x REST top`),
      // in the argument for a 0 (`λx. x top REST`). Its miss top stands
      // beside the rest, in the argument of the outer application for a 1,
      // of the inner one for a 0, its binders named as `Term.top` names
      // them, so that every binder the literal spreads into has an origin (a
      // step that moves a top out of the literal prints it as a term, its
      // binders named by their origins). Every path is relative to its
      // level, so that the spans of a literal of b bits hold O(b) entries
      // and a walk down them (`SyntaxSpans.child`) reads O(1) at each level;
      // paths from the literal's root made them Θ(b²), which ran a reading
      // of an exchange line of 7,947 literal binders out of 5 GB
      // (measured 2026-11-21).
      val spans = Literals.bits(read).zipWithIndex.foldRight(body.spans) { case ((bit, index), below) =>
        val (rest, miss) = if bit then (Vector(0, 0, 1), Vector(0, 1)) else (Vector(0, 1), Vector(0, 0, 1))
        SyntaxSpans.Generated(
          extent,
          Vector.empty,
          Vector(rest -> below),
          (Vector() -> SpelledBinder.LiteralBit(read, index, span)) +:
            missBinders.map((path, name) => (miss ++ path) -> SpelledBinder.Named(name, span))
        )
      }
      Read(Literals.partialFunction(read, body.term), spans)

    /** The binders of top, `(λf. (λx. f (x x)) (λx. f (x x))) (λz. λx. z ∥ x)`
      * (`Term.top`), each at its path from top's root with its name there.
      */
    private val missBinders: Vector[(Vector[Int], String)] =
      Vector(Vector(0) -> "f", Vector(0, 0, 0) -> "x", Vector(0, 0, 1) -> "x", Vector(1) -> "z", Vector(1, 0) -> "x")

  /** The grammar, built and compiled once. Parsley compiles a parser the
    * first time it parses, so a grammar built for each text is compiled for
    * each text: on 2026-11-09, 530 of the 1,108 JFR execution samples of
    * `TrapJudgmentsLawTest` were in Parsley's compiler
    * (`parsley.internal.deepembedding`), under `Grammar.term` and
    * `freeNames`, when every call built its grammar.
    */
  private lazy val grammar: Grammar = Grammar()

  /** The grammar of the Scaladoc of this object, which reads a name no
    * abstraction of the text binds as `Free`, and so needs no table of
    * names; `parse` rejects the text for such a name unless its call allows
    * free names (`FreeNames`). The scope of the abstractions and the list cells is a Parsley
    * reference (`parsley.state.Ref`) set for a subterm's extent with
    * `local`; the free names the parse meets are gathered in one more, most
    * recent first. The grammar's parsers refer to each other as lazy values;
    * a recursive reference stands only where a combinator takes its parser
    * by name (after `~>`, the body of `local`), since a Scala 3 lazy value
    * that its own initialization reads waits for itself.
    */
  private final class Grammar():

    private val scope: Ref[Scope] = Ref.make

    /** The free names met so far, an occurrence each, most recent first. */
    private val freeNameOccurrences: Ref[List[String]] = Ref.make

    /** The offset, in UTF-16 code units, at which the last token read ends,
      * the layout after it left out: the end of a node's span.
      */
    private val tokenEnd: Ref[Int] = Ref.make

    /** The term of the whole text with the spans of its nodes in UTF-16
      * code units and the free names met, or the failure of its parse.
      */
    def read(text: String): Either[ParsleyFailure, (Read, List[String])] =
      whole.parse[ParsleyFailure](text).toEither

    /** The end of a token: its offset recorded, then the layout after it. */
    private def ended[A](token: Parsley[A]): Parsley[A] = token <~ tokenEnd.set(offset) <~ Lexer.layout

    /** A token of one character and the layout after it. */
    private def symbol(character: Char): Parsley[Unit] = ended(char(character).void)

    private val name: Parsley[String] = ended(Lexer.name)

    /** The syntax error where the grammar expected something else. */
    private def expected(expectation: Expectation): Parsley[Nothing] = fail(s"${Raised.expected}$expectation")

    private lazy val whole: Parsley[(Read, List[String])] =
      scope.set(Scope(Map.empty, 0, "")) ~> freeNameOccurrences.set(Nil) ~> tokenEnd.set(offset) ~> Lexer.layout ~>
        (termParser <~ (eof | expected(Expectation.End)), freeNameOccurrences.get).zipped((_, _))

    /** An application alone, or a chain of + and ∥ over applications, the
      * grammar's Term, left associative: each operator takes the chain before
      * it and the operand after it, a ∥ the chain as its left side, a + as
      * its right side (`Read.choice`), and spans from the chain's start to
      * the operand's end.
      */
    private lazy val termParser: Parsley[Read] =
      (application, many(chainOperand)).zipped((first, rest) =>
        rest.foldLeft(first) {
          case (chain, Left(operand))  => Read.choice(chain, operand)
          case (chain, Right(operand)) => Read.parallel(chain, operand)
        }
      )

    /** An operator of a chain and the application after it: the operand of
      * a + on the left, of a ∥ on the right.
      */
    private lazy val chainOperand: Parsley[Either[Read, Read]] =
      (choiceOperator ~> application).map(Left(_)) | (parallelOperator ~> application).map(Right(_))

    private val choiceOperator: Parsley[Unit] = symbol('+')

    private val parallelOperator: Parsley[Unit] =
      ended(char('∥').void | backtracking(string("||")).void)

    /** `λx. M`, its body read with x bound; or `λL. M`, L a literal, the
      * variable arguments partial function of the literal (`Literals`). One
      * λ may take several binders, names and literals mixed, each one
      * abstraction around the rest: `λx "k" y. M` is `λx. λ"k". λy. M`. A λ
      * of no binder, `λ. M`, is its body M, read as a bare λ's body is: an
      * application, ending before + and ∥ (`zeroBinder`). The outermost
      * abstraction spans from the λ, each inner one from its binder, to the
      * body's end.
      */
    private lazy val abstraction: Parsley[Read] =
      offset.zip((char('λ') | char('\\')) ~> Lexer.layout ~> (zeroBinder | literalAbstraction | namedAbstraction)).map(
        Read.startingAt(_, _)
      )

    /** The dot right after a λ and the body: no abstraction, only the extent
      * of a bare λ's body, as Haskell's `$`: zero binders, a change of
      * precedence only.
      */
    private lazy val zeroBinder: Parsley[Read] =
      symbol('.') ~> application

    /** After a binder: the dot and the body, an application, or the next
      * binder.
      */
    private lazy val afterBinder: Parsley[Read] =
      (symbol('.') ~> application) | literalAbstraction | nextNamedAbstraction | expected(Expectation.Dot)

    private lazy val namedAbstraction: Parsley[Read] =
      offset
        .zip(scope.local((scope.get, name | expected(Expectation.Name)).zipped(_.bound(_)))(boundAndAfterBinder))
        .map { case (start, (bound, body)) => Read.abstraction(start, bound, body) }

    /** A name after another binder of the same λ. */
    private lazy val nextNamedAbstraction: Parsley[Read] =
      offset
        .zip(scope.local((scope.get, name).zipped(_.bound(_)))(boundAndAfterBinder))
        .map { case (start, (bound, body)) => Read.abstraction(start, bound, body) }

    /** The name just bound, the innermost of the scope, and what follows
      * its binder.
      */
    private lazy val boundAndAfterBinder: Parsley[(String, Read)] =
      (scope.get.map(_.innermost), afterBinder).zipped((_, _))

    /** A literal and its span in UTF-16 code units, read by the parser. */
    private def located(literal: Parsley[Literal]): Parsley[(Literal, Span)] =
      (offset, ended(literal), tokenEnd.get).zipped((start, read, end) => (read, Span(start, end)))

    /** A literal standing as a bare argument, where a number never takes a
      * following `(`: `f 30(x)` is `f 30 (x)`.
      *
      * TODO (https://github.com/Atry/private-overlay/issues/1514; the linter
      * waits for the source locations of debug information): a linter warns
      * where a name or a literal that is not the head of its application
      * touches the `(` after it, `foo bar(baz)` and `foo 30(baz)`, which read
      * as `foo bar (baz)` and `foo 30 (baz)` and are rewritten as that, as
      * `foo (bar baz)`, `(foo 30)(baz)` or the tag `foo (30(baz))`; checked by
      * tokens, a parenthesis inside a literal not counted. No linter is built
      * yet.
      */
    private val argumentLiteral: Parsley[(Literal, Span)] = located(Lexer.argumentLiteral)

    /** A literal standing alone in parentheses, as an argument `f ( L )` or
      * a binder `λ( L ). M`, where a number touching `(` is a CBOR tag:
      * `f (30([1, 2]))`, `λ(3.0). M`.
      */
    private val parenthesizedLiteral: Parsley[(Literal, Span)] = located(Lexer.parenthesizedLiteral)

    /** A literal standing bare as a binder, `λL. M`, where a number touching
      * `(` is a CBOR tag, `λ30([1, 2]). M`, and which holds no `.` outside
      * its quotes and brackets, so that `λ3. M` binds the integer 3 and
      * `λ(3.0). M` the float (`DiagnosticNotation.binderLiteral`).
      */
    private val binderLiteral: Parsley[(Literal, Span)] = located(Lexer.binderLiteral)

    /** A binder that is a literal alone in parentheses, `λ(3.0). M`, spanning
      * its parentheses, in which the diagnostic notation is read in full.
      */
    private val parenthesizedBinderLiteral: Parsley[(Literal, Span)] =
      (
        offset,
        symbol('(') ~> (parenthesizedLiteral | expected(Expectation.Literal)) <~
          (symbol(')') | expected(Expectation.CloseParenthesis)),
        tokenEnd.get
      ).zipped((start, read, end) => (read._1, Span(start, end)))

    /** `λL. M`, the variable arguments partial function of the literal
      * (`Literals.partialFunction`), L bare or alone in parentheses, its body
      * read in the abstraction's own scope: the bits it takes have no names.
      */
    private lazy val literalAbstraction: Parsley[Read] =
      // `zip` takes its parser by name, which `afterBinder` needs, since it
      // reads this value.
      (binderLiteral | parenthesizedBinderLiteral).zip(afterBinder).map(Read.partialFunction(_, _))

    /** An abstraction, or a head atom applied to its arguments, nested to the
      * left: each argument a name, a term in parentheses, or a literal, bare
      * or alone in parentheses, spread into its variable arguments
      * (`Literals.arguments`); the last argument may be an abstraction with
      * no parentheses, whose body, an application, stops before + and ∥, so
      * that `f a λx. M + N` is `(f a (λx. M)) + N`. A literal is no atom, so a
      * literal where a head stands (a whole term, an abstraction's body, an
      * operand of + or ∥, the head of a term in parentheses) is the syntax
      * error `Expected(Atom, …)`.
      */
    private lazy val application: Parsley[Read] =
      abstraction |
        (atom, many(argument), option(abstraction))
          .zipped((function, arguments, trailing) => (arguments.flatten ++ trailing).foldLeft(function)(Read.application))

    /** A head: a name or a term in parentheses. A literal starts no head and
      * is `Expected(Atom, …)` where it stands, `h'…'` and `b64'…'` included,
      * which a name would otherwise begin; the name is then not tried, whose
      * failure at the same place would be a second error.
      */
    private lazy val atom: Parsley[Read] =
      ifS(
        option(DiagnosticNotation.literalStart).map(_.isDefined),
        expected(Expectation.Atom),
        nameTerm | parenthesizedTerm | expected(Expectation.Atom)
      )

    /** A term in parentheses, the parentheses' span recorded on the term. */
    private lazy val parenthesizedTerm: Parsley[Read] =
      (offset, symbol('(') ~> termParser <~ (symbol(')') | expected(Expectation.CloseParenthesis)), tokenEnd.get)
        .zipped((start, inner, end) => inner.parenthesized(Span(start, end)))

    /** An argument and the reads it spreads into: a literal, its variable
      * arguments; a name; or, after `(`, a literal alone in the parentheses,
      * its variable arguments, each with the parentheses' span, or a term.
      * After `(` a literal start starts no term, so one code point decides.
      */
    private lazy val argument: Parsley[Vector[Read]] =
      argumentLiteral.map(Read.arguments) | nameTerm.map(Vector(_)) |
        (
          offset,
          symbol('(') ~> (parenthesizedLiteral.map(Left(_)) | termParser.map(Right(_))) <~
            (symbol(')') | expected(Expectation.CloseParenthesis)),
          tokenEnd.get
        ).zipped((start, inner, end) =>
          inner match
            case Left(literal) => Read.arguments(literal).map(_.parenthesized(Span(start, end)))
            case Right(term)   => Vector(term.parenthesized(Span(start, end)))
        )

    /** The term of a name in a value position: the variable of the innermost
      * abstraction that binds it, else `Free(name)`, gathered in
      * `freeNameOccurrences`. `_` fails the parse as unbound where it
      * stands.
      */
    private lazy val nameTerm: Parsley[Read] =
      (offset, nameReference, tokenEnd.get).zipped((start, term, end) => Read(term, SyntaxSpans.leaf(Span(start, end))))

    private lazy val nameReference: Parsley[DeBruijnTerm] =
      (name <~> scope.get)
        .collectMsg { case (spelling, _) => Seq(s"${Raised.unboundName}$spelling") } {
          case (spelling, current) if spelling != "_" =>
            current.levels.get(spelling) match
              case Some(level) => DeBruijnTerm.Variable(current.depth - level - 1)
              case None        => DeBruijnTerm.Free(spelling)
        }
        .fillRef(read =>
          freeNameOccurrences.update(read.gets {
            case DeBruijnTerm.Free(spelling) => (occurrences: List[String]) => spelling :: occurrences
            case _                           => (occurrences: List[String]) => occurrences
          }) ~> read.get
        )
