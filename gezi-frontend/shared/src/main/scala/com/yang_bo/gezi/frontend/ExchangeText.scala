package com.yang_bo.gezi.frontend

import com.yang_bo.gezi.ir.ChoiceSpine
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.StorageAccess
import scala.annotation.tailrec

/** The exchange format of terms: one line of lambda-lattice text that writes a
  * closed IR term at the size of its graph, in the language of the front end,
  * lambda-lattice, with no layer of records.
  *
  * A line is `λstart. start (λk. k N) (TERM)`, the shape of a trace's start
  * (`com.yang_bo.gezi.rewritetrace.TraceStart`) on one line: TERM is the text the printer
  * (`ReadableText`) writes for the instruction with no names
  * (`ReadableText.printedNameless`, on one line, `Printed.text`), which binds
  * each closed instruction the text refers to more than once by the library's
  * import form `(λt. t V) λm. BODY` at TERM's start and writes the literals
  * back in their diagnostic notation, and N is the number of those bindings, a
  * literal. A program's own text may begin with a binding of the same shape, so
  * the line says how many are the printer's. The reader contracts N bindings
  * (`Defunctionalization.bindingsContracted`): it converts each value V, its
  * names of earlier bindings standing for their instructions, and then the
  * body, so that reading is linear in the text, as writing is; a line whose
  * instruction, written again, is not the line is no line of the format, so
  * that one instruction has one line.
  *
  * The judge writes the terms of its points file and of its pipe in it, and the
  * snapshots of `contest-corpora` record the generated programs in it. A line
  * holds no tab and no newline: the printer writes neither on one line, and a
  * literal it writes back escapes them in its diagnostic notation. A term
  * written here is closed: it is read with no name bound outside it, so the
  * library a program uses is part of it, each of its instructions written once
  * however often the program refers to it.
  *
  * A set of one or more normal forms is one line too (`normalForms`): their
  * choice, a chain of `+` in their order. A βη normal form is a pure term, no
  * choice, so the right spine of the choice gives back the members.
  *
  * A set of Scott ADT values is one line too (`scottADTLine`): the members the
  * Scott ADT reading gives (`ReadableText.Reading.ScottADT`), a storage written
  * as its untyped Scott ADT layer and a parallel node `v ∥ E` as v, their
  * choice in the order of each member's own text (`ReadableText.scottADTText`).
  * Any other term, the remainder of an output, is written by `line`, which
  * keeps every `∥ T` and writes a storage as its view.
  *
  * The form is here, in the front end, so that the runner in an entry's JVM
  * (`com.yang_bo.gezi.contest.runner`) reads and writes the pipe without the problem
  * corpora on its classpath, which an entry's JVM does not have.
  */
object ExchangeText:

  /** The line of the closed instruction, which reads back as the instruction
    * when it is in the front end's spelling
    * (`Defunctionalization.thunkInstruction` of its readback), as every
    * instruction the front end makes is; one in another spelling reads as the
    * front end's. The line is not read back here: reading costs as much as
    * printing, and a writer of many lines would pay it for each. Throws
    * `IllegalArgumentException` for an instruction that holds an opaque
    * instruction or a URI node, which the text would write as a name no
    * abstraction binds. A storage in the instruction is written as its view,
    * `v ∥ T`, every `∥ T` kept: the line of the remainder of an output, or of
    * any term. The Scott ADT values of an output are written by `scottADTLine`.
    */
  def line[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C, StorageAccess): String =
    lineRead(instruction, ReadableText.Reading.Display)

  /** The line of a set of Scott ADT values, given as their members (each member
    * of `ScottADTChoices.members`, a group of storages already given as its
    * members): their choice, a chain of `+`, in the order of each member's own
    * text (`ReadableText.scottADTText`), so that a set has one line. Each
    * storage in a member is written as its untyped Scott ADT layer
    * `λc1 … ck. ci f1 … fn` from its native data, and a parallel node `v ∥ E`
    * as v; the layer is the one the front end spells for the same term, so a
    * storage and the pure term it equals are one binding. The empty set is
    * `noNormalFormLine`, as for normal forms. Throws `IllegalArgumentException`
    * for a member that is a choice, which no Scott ADT value is, and for an
    * opaque instruction or a URI node, as `line` does.
    */
  def scottADTLine[C <: NativeSpecializer & Singleton](
      members: Vector[Configured[C]]
  )(using
      specializer: C,
      access: StorageAccess
  ): String =
    members.foreach { member =>
      member.layer match
        case com.yang_bo.gezi.ir.Choice(_, _) =>
          throw IllegalArgumentException(
            s"a Scott ADT value is no choice: $member"
          )
        case _ => ()
    }
    if members.isEmpty then noNormalFormLine
    else
      val ordered = members
        .map(member => (ReadableText.scottADTText(member), member))
        .sortBy(_._1)
        .map(_._2)
      lineRead(
        ChoiceSpine.nested[Configured[C]](ordered, specializer.choice(_, _)),
        ReadableText.Reading.ScottADT
      )

  /** The line of an output that holds both Scott ADT values and a remainder
    * (`OutputDisplay.Mixed`): the choice of the members, as `scottADTLine`
    * writes them, then the remainder, a term kept as it is (every `∥ T`, a
    * storage as its view) as `line` writes it. One table serves the whole line,
    * so that an instruction the members and the remainder refer to more than
    * once between them is bound once, and a storage both hold is bound twice,
    * once as its Scott ADT layer and once as its view. With no member the line
    * is `line` of the remainder. Throws `IllegalArgumentException` as
    * `scottADTLine` and `line` do.
    */
  def mixedLine[C <: NativeSpecializer & Singleton](
      members: Vector[Configured[C]],
      remainder: Configured[C]
  )(using
      C,
      StorageAccess
  ): String =
    members.foreach { member =>
      member.layer match
        case com.yang_bo.gezi.ir.Choice(_, _) =>
          throw IllegalArgumentException(
            s"a Scott ADT value is no choice: $member"
          )
        case _ => ()
    }
    if members.isEmpty then line(remainder)
    else
      val ordered = members
        .map(member => (ReadableText.scottADTText(member), member))
        .sortBy(_._1)
        .map(_._2)
      (ordered.map((_, ReadableText.Reading.ScottADT)) :+ ((
        remainder,
        ReadableText.Reading.Display
      ))).foreach((part, reading) =>
        opaqueLeaf(List(part), Set.empty, reading).foreach(leaf =>
          throw IllegalArgumentException(
            s"an exchange line writes no opaque instruction, found $leaf"
          )
        )
      )
      framed(ReadableText.printedMixedUnmarked(ordered, remainder))

  /** The line of the instruction with its storages read as the reading says. */
  private def lineRead[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      reading: ReadableText.Reading
  )(using
      C,
      StorageAccess
  ): String =
    opaqueLeaf(List(instruction), Set.empty, reading).foreach(leaf =>
      throw IllegalArgumentException(
        s"an exchange line writes no opaque instruction, found $leaf"
      )
    )
    printed(instruction, reading)

  /** An opaque instruction under the pending ones, each distinct instruction
    * visited once, the terms a storage holds as the reading says.
    */
  @tailrec
  private def opaqueLeaf[C <: NativeSpecializer & Singleton](
      pending: List[Configured[C]],
      visited: Set[Configured[C]],
      reading: ReadableText.Reading
  )(using C, StorageAccess): Option[Configured[C]] = pending match
    case Nil                                          => None
    case current :: rest if visited.contains(current) =>
      opaqueLeaf(rest, visited, reading)
    case current :: _ if current.opaque => Some(current)
    case current :: rest                =>
      opaqueLeaf(
        ReadableText.childrenOf(current, reading).toList ++ rest,
        visited + current,
        reading
      )

  /** Whether the text has the shape of a line, `λstart. start (λk. k N) (TERM)`
    * with no tab and no newline, read no further: for a holder of lines that
    * does not read their terms (the judge's supervisor, whose runner reads
    * them), which learns that a line is malformed only where the line is read.
    */
  def shaped(text: String): Boolean =
    text.startsWith(shapePrefix) && text.endsWith(")") && !text.exists(
      character => character == '\t' || character == '\n'
    )

  private val shapePrefix: String = "λstart. start (λk. k "

  /** The instruction of the line, or why the text is no line of the format: a
    * syntax error, a free name, a text of another shape, or a spelling other
    * than the one `line` writes for the instruction it reads as.
    */
  def term[C <: NativeSpecializer & Singleton](
      text: String
  )(using C, StorageAccess): Either[String, Configured[C]] =
    read[C](text).flatMap(instruction =>
      val written = printed(instruction, ReadableText.Reading.Display)
      if written == text then Right(instruction)
      else Left(s"another spelling of the term written ${written.take(80)}")
    )

  /** The line of the set of normal forms, given in order: their choice. Throws
    * `IllegalArgumentException` for a member that is a choice, which no βη
    * normal form is.
    */
  def normalFormsLine[C <: NativeSpecializer & Singleton](
      normalForms: Vector[Configured[C]]
  )(using
      specializer: C,
      access: StorageAccess
  ): String =
    normalForms.foreach { member =>
      member.layer match
        case com.yang_bo.gezi.ir.Choice(_, _) =>
          throw IllegalArgumentException(s"a normal form is no choice: $member")
        case _ => ()
    }
    if normalForms.isEmpty then noNormalFormLine
    else
      line(
        ChoiceSpine.nested[Configured[C]](normalForms, specializer.choice(_, _))
      )

  /** The line of no normal form: the format's own spelling of the empty set,
    * which is no term of the language and which `term` does not read: no answer
    * is written in the protocol's own spelling, not as a term. Its bytes are
    * the ones the points files and the pipe carried while the language had a
    * record of no entries.
    */
  val noNormalFormLine: String = "{}"

  /** The normal forms of a line `normalFormsLine` writes, in order, or why the
    * text is none.
    */
  def normalForms[C <: NativeSpecializer & Singleton](
      text: String
  )(using C, StorageAccess): Either[String, Vector[Configured[C]]] =
    if text == noNormalFormLine then Right(Vector.empty)
    else
      term[C](text).map(choice =>
        ChoiceSpine.members[Configured[C]](
          choice,
          member =>
            member.layer match
              case com.yang_bo.gezi.ir.Choice(left, right) => Some((left, right))
              case _                           => None
        )
      )

  /** The text of the instruction in the format's shape, not read back. */
  private def printed[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      reading: ReadableText.Reading
  )(using
      C,
      StorageAccess
  ): String = framed(ReadableText.printedNamelessUnmarked(instruction, reading))

  /** The printed text in the format's shape: `λstart. start (λk. k N) (TERM)`.
    */
  private def framed[C <: NativeSpecializer & Singleton](
      written: ReadableText.Printed[C]
  ): String =
    s"λstart. start (λk. k ${written.bindings}) (${written.text})"

  /** The instruction the text reads as, its printer's bindings contracted, or
    * the reason it reads as none.
    */
  private def read[C <: NativeSpecializer & Singleton](
      text: String
  )(using C): Either[String, Configured[C]] =
    try
      Lambdalattice.term(text) match
        case DeBruijnTerm.Lambda(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Apply(
                  DeBruijnTerm.Variable(0),
                  DeBruijnTerm.Lambda(count)
                ),
                body
              )
            ) =>
          bindingCount(count).flatMap(bindings =>
            Defunctionalization
              .bindingsContracted[C](body, bindings, enclosingBinders = 1)
          )
        case _ => Left("no text λstart. start (λk. k N) (TERM)")
    catch
      case LambdalatticeMalformed(problem) => Left(problem.toString)
      case LambdaError(reason)             => Left(reason.productPrefix)

  /** N of `λk. k N`: the body `k` applied to the bits of one CBOR integer
    * (`Literals.arguments`), each byte high bit first, a natural `Int`; or why
    * it is none.
    */
  private def bindingCount(applied: DeBruijnTerm): Either[String, Int] =
    @tailrec
    def bits(
        current: DeBruijnTerm,
        found: List[Boolean]
    ): Option[Vector[Boolean]] = current match
      case DeBruijnTerm.Apply(function, argument) if argument eq Literals.one =>
        bits(function, true :: found)
      case DeBruijnTerm.Apply(function, argument)
          if argument eq Literals.zero =>
        bits(function, false :: found)
      case DeBruijnTerm.Variable(0) => Some(found.toVector)
      case _                        => None
    bits(applied, Nil) match
      case Some(read) if read.nonEmpty && read.size % 8 == 0 =>
        val bytes = read
          .grouped(8)
          .map(byte =>
            byte
              .foldLeft(0)((value, bit) => value * 2 + (if bit then 1 else 0))
              .toByte
          )
          .toVector
        Literal
          .integerRead(Literal(IArray.from(bytes)))
          .flatMap(count =>
            if count.isValidInt && count >= 0 then Right(count.toInt)
            else Left(s"the number of bindings $count is no natural Int")
          )
      case _ => Left("the number of bindings is no literal")
