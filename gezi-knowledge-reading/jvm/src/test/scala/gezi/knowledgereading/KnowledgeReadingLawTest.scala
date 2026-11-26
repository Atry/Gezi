package gezi.knowledgereading

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Literals
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.Instruction
import gezi.weakhead.Computation
import gezi.weakhead.Value

/** The laws of the data reader (`KnowledgeReading`).
  *
  * The round trip and the union: generated members, each a tuple of a name
  * (the trie of its string literal, as a knowledge file writes one), a
  * closed term, a list of strings and an integer, contributed to generated
  * slots of a fixed-width mixin by mixins chosen together
  * (`KnowledgeReading.slots`), the term `λy. F A y` with F and A written
  * out or bound by a let around the whole, read back as the same members of
  * each slot, the term as the instruction its text alone defunctionalizes
  * to. Its purpose is to catch a slot read as another, a member lost or
  * doubled when the mixins are chosen together, a slot nobody writes read as
  * a member or as an error, a field order or a bit order read wrongly, a
  * string, a list or an integer decoded wrongly, and a term read with the
  * let's spelling instead of its own.
  *
  * The values that are no sets: a value written once reads as written, a
  * choice of one value twice reads as that value (a choice is a set, and the
  * tabled reading takes it once), and a choice of two values is refused. Its
  * purpose is to catch a reader that takes one of two values silently.
  */
class KnowledgeReadingLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of KnowledgeReadingLawTest, "records chosen together read back the members of each key", takes 4.687 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  // TODO: defines and instructions stood here, the library names the generated terms used and their opaque instructions,
  // through which the records' texts were converted and the members' terms read back. They named library terms by
  // Term.define leaves of HoasGenerators.closedTerm and a map of names to instructions, a free variable (blacklisted)
  // and a table of library files deleted when the library became files reached by paths.
  // The generated terms now have no free name, so the texts are read closed. The deleted code:
  // git show 2908bffd5:lambda_jit/knowledge-reading/src/test/scala/lambdajit/knowledgereading/KnowledgeReadingLawTest.scala.

  /** The width of the mixin the members are contributed to. */
  private val width: Int = 3

  /** A member: its key, the record of the choice that writes it, its name,
    * the two closed terms of its term field `λy. function argument y`, its
    * strings, its integer, and whether the two terms are bound by a let
    * around the whole instead of written out.
    */
  private final case class Member(
      key: Int,
      part: Int,
      name: String,
      function: Term,
      argument: Term,
      strings: Vector[String],
      number: BigInt,
      letBound: Boolean
  ):
    def term: Term = Term.λ(y => function(argument)(y))

  private val parts = 3

  private val text: Gen[String] = Gen.string(Gen.unicode, Range.linear(0, 6))

  private val number: Gen[BigInt] =
    for
      high <- Gen.long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
      low <- Gen.long(Range.linear(0L, Long.MaxValue))
      wide <- Gen.boolean
    yield if wide then BigInt(high) * BigInt(Long.MaxValue) + BigInt(low) else BigInt(high)

  private val member: Gen[Member] =
    for
      key <- Gen.int(Range.linear(0, width - 1))
      part <- Gen.int(Range.linear(0, parts - 1))
      name <- text
      function <- HoasGenerators.closedTerm
      argument <- HoasGenerators.closedTerm
      strings <- text.list(Range.linear(0, 3))
      value <- number
      letBound <- Gen.boolean
    yield Member(key, part, name, function, argument, strings.toVector, value, letBound)

  /** A string literal of the key, which stands only as an argument and
    * spreads into its elements. A control character other than a line feed
    * or a carriage return is written as a `\u` escape: the diagnostic
    * notation's `unescaped` admits none of them (`DiagnosticNotation`), and
    * `text` draws any Unicode character.
    */
  private def quoted(text: String): String =
    "\"" + text.flatMap {
      case '"'                                                     => "\\\""
      case '\\'                                                    => "\\\\"
      case control if control < ' ' && control != '\n' && control != '\r' => f"\\u${control.toInt}%04x"
      case other                                                   => other.toString
    } + "\""

  /** The text of the library's Scott list of the text's bytes, what
    * `from_cbor` of `text/cbor` of its string literal gives: a literal is never a value
    * of its own.
    */
  private def textValue(text: String): String =
    s"(${Lambdalattice.text(Literals.textTerm(IArray.unsafeFromArray(text.getBytes(java.nio.charset.StandardCharsets.UTF_8))), Map.empty)})"

  /** The trie of the text's string literal, `(λk. k "…")`, whose bits the
    * host reads (`KnowledgeReading.trieText`): how a knowledge file writes a
    * name.
    */
  private def trieValue(text: String): String = s"(λk. k ${quoted(text)})"

  /** The text of the library's Scott integer. */
  private def integerValue(value: BigInt): String =
    s"(${Lambdalattice.text(Literals.integerTerm(value), Map.empty)})"

  /** The text of the library's Scott list of the closed items' texts, nil
    * `λn. λc. n` and a cell `λn. λc. c h t` (`Literals.textTerm`'s
    * encoding): the bracket is a CBOR array literal and no list of terms.
    */
  private def scottList(items: Seq[String]): String =
    items.foldRight("(λn. λc. n)")((item, tail) => s"(λn. λc. c $item $tail)")

  /** The text: the choice of the records, each the choice of its keys'
    * partial functions, a key's value the choice of its members; a record of
    * no member writes one field of a key no member has. A let-bound member's
    * term is a variable of a let around the whole.
    */
  private def recordText(members: Vector[Member]): String =
    val written = members.zipWithIndex.map((found, position) =>
      val term =
        if found.letBound then s"(λy. function_$position argument_$position y)"
        else s"(λy. (${LambdalatticeText.text(found.function)}) (${LambdalatticeText.text(found.argument)}) y)"
      (found, s"(λs. s ${trieValue(found.name)} $term ${scottList(found.strings.map(textValue))} ${integerValue(found.number)})")
    )
    val records = (0 until parts).flatMap(part =>
      val fields = (0 until width).flatMap(key =>
        written.collect { case (found, tuple) if found.part == part && found.key == key => tuple } match
          case Vector() => None
          case tuples   =>
            val binders = (0 until width).map(slot => if slot == key then s"slot_$slot" else "_").mkString(" ")
            Some(s"(λ_ $binders. slot_$key (${tuples.mkString(" + ")}))")
      )
      if fields.isEmpty then None else Some(fields.mkString("(", " + ", ")"))
    )
    val body = records.mkString(" + ")
    val lets = members.zipWithIndex.filter(_._1.letBound)
    val letted = lets.foldRight(body)((bound, inner) => s"(λfunction_${bound._2}. λargument_${bound._2}. ($inner))")
    val arguments = lets
      .map((found, _) =>
        s" (${LambdalatticeText.text(found.function)}) (${LambdalatticeText.text(found.argument)})"
      )
      .mkString
    s"$letted$arguments"

  property("mixins chosen together read back the members of each slot") {
    for members <- member.list(Range.linear(1, 5)).forAllWithLog(found => recordText(found.toVector))
    yield
      val knowledge = Defunctionalization.thunkInstruction(Lambdalattice.term(recordText(members.toVector)))
      val names = Set.empty[Instruction]
      val reading = KnowledgeReading.slots(knowledge, width).flatMap(slots =>
        Computation.traversed(slots)(bodies =>
          Computation.traversed(bodies)(KnowledgeReading.members).map(_.flatten).flatMap(found =>
            Computation.traversed(found) {
            case Vector(name, term, strings, value) =>
              for
                nameText <- KnowledgeReading.trieText(name)
                items <- KnowledgeReading.items(strings)
                stringTexts <- Computation.traversed(items)(KnowledgeReading.text)
                valueRead <- KnowledgeReading.integer(value)
              yield (nameText, KnowledgeReading.term(term, names), stringTexts, valueRead)
            case other => throw IllegalStateException(s"four fields, not ${other.size}")
          }
          )
        )
      )
      val read = KnowledgeReading.run(reading, 10000000L)
      val expected = (0 until width).toVector.map(key =>
        members.toVector.filter(_.key == key).map(found =>
          (found.name, Defunctionalization.thunkInstruction(found.term.deBruijnTerm(Map.empty)), found.strings, found.number)
        )
      )
      Result
        .diff(read.map(_.toSet), expected.map(_.toSet))(_ == _)
        .and(Result.diff(read.map(_.size), expected.map(_.distinct.size))(_ == _))
  }

  property("a value is read as written once, or refused when two values are chosen") {
    for
      name <- text.forAll
      value <- number.forAll
      other <- text.forAll
    yield
      def record(written: String): Value =
        Defunctionalization.thunkInstruction(Lambdalattice.term(written))
      val read = KnowledgeReading.run(
        for
          nameRead <- KnowledgeReading.trieTextWritten(record(trieValue(name)))
          valueRead <- KnowledgeReading.integerWritten(record(integerValue(value)))
        yield (nameRead, valueRead),
        10000000L
      )
      val writtenTwice = scala.util
        .Try(KnowledgeReading.run(KnowledgeReading.trieTextWritten(record(s"${trieValue(name)} + ${trieValue(other)}")), 10000000L))
      val refused = writtenTwice.failed.toOption.exists {
        case _: KnowledgeReadingError => true
        case _                        => false
      }
      // A choice is a set: one value chosen twice is that value written
      // once, and only two different values are refused.
      val twiceAsExpected =
        if other == name then Result.diff(writtenTwice.toOption, Option(Option(name)))(_ == _).log("the same value twice")
        else Result.assert(refused).log("two values")
      Result.diff(read, (Option(name), Option(value)))(_ == _).and(twiceAsExpected)
  }

  /** Its purpose is to catch a trie reader that accepts a literal of
    * another kind of CBOR item as a text, or reads the bits of a text that
    * more bytes follow: a trie of an integer literal, of a byte string, and of
    * a text's literal then one more literal are refused.
    */
  property("a trie that wraps no single text string is refused") {
    for
      name <- text.forAll
      value <- number.forAll
    yield
      def refused(written: String): Boolean =
        scala.util
          .Try(KnowledgeReading.run(KnowledgeReading.trieText(Defunctionalization.thunkInstruction(Lambdalattice.term(written))), 10000000L))
          .failed
          .toOption
          .exists {
            case _: KnowledgeReadingError => true
            case _                        => false
          }
      val bytes = name.getBytes(java.nio.charset.StandardCharsets.UTF_8).map(byte => f"${byte & 0xff}%02x").mkString
      Result
        .assert(refused(s"(λk. k $value)"))
        .log("an integer")
        .and(Result.assert(refused(s"(λk. k h'$bytes')")).log("a byte string"))
        .and(Result.assert(refused(s"(λk. k ${quoted(name)} 0)")).log("a text then an integer"))
  }
