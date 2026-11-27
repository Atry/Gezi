package gezi.frontend

import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.StorageAccess
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The occurrence tagging (`Occurrences.tagged`) of a program given as an
  * instruction, such as a point of the judge's exchange format, whose library
  * terms are inlined and whose repeated parts are shared, with no name left to
  * tag.
  *
  * The program is read back into a de Bruijn term only down to its shared
  * parts: an instruction the program refers to more than once, and an
  * instruction of `kept`, stays a `Constant` (the printer's reference count,
  * `ReadableText.counted`, the literals' parts left out as the printer leaves
  * them, since a literal is never cut). So the readback is linear in the
  * instruction graph, where a full readback writes a shared part out at each of
  * its references. The readback is then tagged: each lambda chain gets the
  * closure marker, each `Constant` the name marker, each with its own tag, so
  * that a library whose lemmas type each occurrence on its own (HM's) meets
  * every reference to a shared part as an occurrence of its own.
  *
  * A shared part that is not in `kept` is tagged the same way inside, once, and
  * every reference to it refers to the tagged part, which stays shared. A part
  * of `kept` is left as it is inside: a library term that the library knows by
  * its handle (a scheme's lemma, a native's binding) would no longer be that
  * handle once tagged inside.
  */
object ProgramOccurrences:

  /** The program with its occurrences tagged, `kept` left untagged inside. */
  def tagged[C <: NativeSpecializer & Singleton](
      program: Configured[C],
      kept: Set[Configured[C]],
      markers: OccurrenceMarkers
  )(using C, StorageAccess): Configured[C] =
    val (counts, order) = ReadableText.counted(program)
    val shared = order
      .filter(instruction =>
        (counts.getOrElse(instruction, 0) > 1 || kept
          .contains(instruction)) && !ReadableText.literalPart(instruction)
      )
      .toSet - program
    // `order` lists each instruction after those it refers to, so the
    // shared parts a part refers to are tagged before it.
    val taggedParts = order
      .filter(shared.contains)
      .foldLeft(Map.empty[Configured[C], Configured[C]]) { (done, part) =>
        if kept.contains(part) then done
        else done.updated(part, partTagged(part, shared, done, markers))
      }
    partTagged(program, shared, taggedParts, markers)

  /** The part read back down to the shared parts, each of those that is tagged
    * already replaced by its tagged part, then tagged.
    */
  private def partTagged[C <: NativeSpecializer & Singleton](
      part: Configured[C],
      shared: Set[Configured[C]],
      taggedParts: Map[Configured[C], Configured[C]],
      markers: OccurrenceMarkers
  )(using C, StorageAccess): Configured[C] =
    val readback = Defunctionalization.instructionTerm(part, shared)
    Defunctionalization.thunkInstruction[C](
      Occurrences
        .tagged[C](constantsReplaced(readback, taggedParts).result, markers)
    )

  /** The term with each `Constant` of a tagged part replaced by the tagged
    * part.
    */
  private def constantsReplaced[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      taggedParts: Map[Configured[C], Configured[C]]
  ): TailRec[DeBruijnTermOf[Configured[C]]] =
    term match
      case DeBruijnTerm.Constant(instruction) =>
        done(taggedParts.get(instruction).fold(term)(DeBruijnTerm.Constant(_)))
      case DeBruijnTerm.Variable(_) | DeBruijnTerm.Free(_) => done(term)
      case DeBruijnTerm.Lambda(body)                       =>
        tailcall(constantsReplaced(body, taggedParts)).map(
          DeBruijnTerm.Lambda(_)
        )
      case DeBruijnTerm.Apply(function, argument) =>
        for
          functionReplaced <- tailcall(constantsReplaced(function, taggedParts))
          argumentReplaced <- tailcall(constantsReplaced(argument, taggedParts))
        yield DeBruijnTerm.Apply(functionReplaced, argumentReplaced)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          leftReplaced <- tailcall(constantsReplaced(left, taggedParts))
          rightReplaced <- tailcall(constantsReplaced(right, taggedParts))
        yield DeBruijnTerm.Parallel(leftReplaced, rightReplaced)
      case DeBruijnTerm.Choice(left, right) =>
        for
          leftReplaced <- tailcall(constantsReplaced(left, taggedParts))
          rightReplaced <- tailcall(constantsReplaced(right, taggedParts))
        yield DeBruijnTerm.Choice(leftReplaced, rightReplaced)
