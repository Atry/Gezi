package gezi.frontend

import gezi.ir.Instruction
import scala.annotation.tailrec

/** The exchange format of terms: one line of lambda-lattice text that writes
  * a closed IR term at the size of its graph, in the language of the front
  * end, lambda-lattice, with no layer of records.
  *
  * A line is `λstart. start (λk. k N) (TERM)`, the shape of a trace's start
  * (`gezi.rewritetrace.TraceStart`) on one line: TERM is the text the
  * printer (`ReadableText`) writes for the instruction with no names
  * (`ReadableText.printedNameless`, on one line, `Printed.text`), which binds
  * each closed instruction the text refers to more than once by the
  * library's import form `(λt. t V) λm. BODY` at TERM's start and writes the
  * literals back in their diagnostic notation, and N is the number of those
  * bindings, a literal. A program's own text may begin with a binding of the
  * same shape, so the line says how many are the printer's. The reader
  * contracts N bindings (`Defunctionalization.bindingsContracted`): it
  * converts each value V, its names of earlier bindings standing for their
  * instructions, and then the body, so that reading is linear in the text,
  * as writing is; a line whose
  * instruction, written again, is not the line is no line of the format,
  * so that one instruction has one line.
  *
  * The judge writes the terms of its points file and of its pipe in it,
  * and the
  * snapshots of `contest-corpora` record the generated programs in it. A
  * line holds no tab and no newline: the printer writes neither on one line,
  * and a literal it writes back escapes them in its diagnostic notation. A
  * term written here is closed: it is read with no name bound outside it,
  * so the library a program uses is part of it, each of its instructions
  * written once however often the program refers to it.
  *
  * A set of one or more normal forms is one line too (`normalForms`): their
  * choice, a chain of `+` in their order. A βη normal form is a pure term, no
  * choice, so the right spine of the choice gives back the members.
  *
  * The form is here, in the front end, so that the runner in an entry's JVM
  * (`gezi.contest.runner`) reads and writes the pipe without the problem
  * corpora on its classpath, which an entry's JVM does not have.
  */
object ExchangeText:

  /** The line of the closed instruction, which reads back as the
    * instruction when it is in the front end's spelling
    * (`Defunctionalization.thunkInstruction` of its readback), as every
    * instruction the front end makes is; one in another spelling reads as
    * the front end's. The line is not read back here: reading costs as much
    * as printing, and a writer of many lines would pay it for each. Throws
    * `IllegalArgumentException` for an instruction that holds an opaque
    * instruction or a URI node, which the text would write as a name no
    * abstraction binds.
    */
  def line(instruction: Instruction): String =
    opaqueLeaf(List(instruction), Set.empty).foreach(leaf =>
      throw IllegalArgumentException(s"an exchange line writes no opaque instruction, found $leaf")
    )
    printed(instruction)

  /** An opaque instruction under the pending ones, each distinct
    * instruction visited once.
    */
  @tailrec
  private def opaqueLeaf(pending: List[Instruction], visited: Set[Instruction]): Option[Instruction] = pending match
    case Nil                                         => None
    case current :: rest if visited.contains(current) => opaqueLeaf(rest, visited)
    case current :: _ if current.opaque              => Some(current)
    case current :: rest                             => opaqueLeaf(current.layered.children.toList ++ rest, visited + current)

  /** The instruction of the line, or why the text is no line of the format:
    * a syntax error, a free name, a text of another shape, or a spelling
    * other than the one `line` writes for the instruction it reads as.
    */
  def term(text: String): Either[String, Instruction] =
    read(text).flatMap(instruction =>
      val written = printed(instruction)
      if written == text then Right(instruction) else Left(s"another spelling of the term written ${written.take(80)}")
    )

  /** The line of the set of normal forms, given in order: their choice.
    * Throws `IllegalArgumentException` for a member that is a choice, which
    * no βη normal form is.
    */
  def normalFormsLine(normalForms: Vector[Instruction]): String =
    normalForms.foreach {
      case member @ Instruction.Choice(_, _) =>
        throw IllegalArgumentException(s"a normal form is no choice: $member")
      case _ => ()
    }
    if normalForms.isEmpty then noNormalFormLine else line(Instruction.Choice.nested(normalForms))

  /** The line of no normal form: the format's own spelling of the empty set,
    * which is no term of the language and which `term` does not read: no
    * answer is written in the protocol's own spelling, not as a term.
    * Its bytes are the ones the points files and the pipe carried while the
    * language had a record of no entries.
    */
  val noNormalFormLine: String = "{}"

  /** The normal forms of a line `normalFormsLine` writes, in order, or why
    * the text is none.
    */
  def normalForms(text: String): Either[String, Vector[Instruction]] =
    if text == noNormalFormLine then Right(Vector.empty)
    else term(text).map { case Instruction.ChoiceMembers(members) => members }

  /** The text of the instruction in the format's shape, not read back. */
  private def printed(instruction: Instruction): String =
    val written = ReadableText.printedNamelessUnmarked(instruction)
    s"λstart. start (λk. k ${written.bindings}) (${written.text})"

  /** The instruction the text reads as, its printer's bindings contracted,
    * or the reason it reads as none.
    */
  private def read(text: String): Either[String, Instruction] =
    try
      Lambdalattice.term(text) match
        case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Lambda(count)), body)) =>
          bindingCount(count).flatMap(bindings => Defunctionalization.bindingsContracted(body, bindings, enclosingBinders = 1))
        case _ => Left("no text λstart. start (λk. k N) (TERM)")
    catch
      case LambdalatticeMalformed(problem) => Left(problem.toString)
      case LambdaError(reason)             => Left(reason.productPrefix)

  /** N of `λk. k N`: the body `k` applied to the bits of one CBOR integer
    * (`Literals.arguments`), each byte high bit first, a natural `Int`; or
    * why it is none.
    */
  private def bindingCount(applied: DeBruijnTerm): Either[String, Int] =
    @tailrec
    def bits(current: DeBruijnTerm, found: List[Boolean]): Option[Vector[Boolean]] = current match
      case DeBruijnTerm.Apply(function, argument) if argument eq Literals.one  => bits(function, true :: found)
      case DeBruijnTerm.Apply(function, argument) if argument eq Literals.zero => bits(function, false :: found)
      case DeBruijnTerm.Variable(0)                                           => Some(found.toVector)
      case _                                                                  => None
    bits(applied, Nil) match
      case Some(read) if read.nonEmpty && read.size % 8 == 0 =>
        val bytes = read.grouped(8).map(byte => byte.foldLeft(0)((value, bit) => value * 2 + (if bit then 1 else 0)).toByte).toVector
        Literal.integerRead(Literal(IArray.from(bytes))).flatMap(count =>
          if count.isValidInt && count >= 0 then Right(count.toInt) else Left(s"the number of bindings $count is no natural Int")
        )
      case _ => Left("the number of bindings is no literal")
