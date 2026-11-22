package gezi.frontend

import gezi.ir.Instruction
import gezi.ir.Layer
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel}

/** The outcome of `LibraryRecognition.recognised`: the term with each
  * recognised subterm a constant, the number of subterms recognised, and the
  * operations it spent.
  */
final case class Recognition(term: DeBruijnTerm, recognised: Int, operations: Long)

/** A front-end stage that recognises the library's defines in a closed
  * program written with the library and inlined (recognition by structure,
  * not by name), to run before the occurrence tagging (`Occurrences.tagged`).
  *
  * Each closed subterm's IR instruction is computed bottom up. A closed subterm whose instruction is the instruction of a define
  * is replaced by `DeBruijnTerm.Constant` of that instruction: the tagging then
  * reads an occurrence of the define, as it reads a name written in the
  * program, and every later stage sees the define. The match is instruction
  * equality against the set of define instructions given, generic over every
  * define; no name is read. The replacement leaves the program's IR
  * unchanged: a constant converts to the bare instruction it holds
  * (`Defunctionalization`), and the subterm converts to the same instruction, by
  * hash consing.
  *
  * A LIMIT: a define whose body is a lambda chain, written as the body of a
  * lambda, continues that lambda's chain once inlined, and the two are one
  * thunk in the IR; it is no closed subterm, so it is not recognised there.
  *
  * TIES: two defines whose bodies are the same IR are one instruction, so the
  * stage cannot tell them apart, and need not: the constant is the same term
  * either way. No tie is broken by name.
  *
  * COST: linear in the program. A closed subterm's instruction is built from its
  * parts' instructions: a closed application, parallel or choice is one layer
  * interned over them; a closed lambda chain is converted with every closed
  * subterm of its body already a constant, so the conversion walks only the
  * body's open part, which no other chain walks. No subterm is interned
  * whole twice. `operations` counts the conversion's operations of each
  * chain (`Defunctionalization.thunkInstructionCounted`, which interns as
  * it converts) and one for each layer interned over closed parts
  * (`Interning.layerInternedCounted`); the library's LibraryRecognitionLawTest records them on generated inlined
  * numerals as a snapshot (snapshot/library_recognition/operations.txt).
  *
  * PRIOR WORK IN THE REPOSITORY: the entry `contest-entries-solo` has a LibraryRecognition of its
  * own (`gezi.contest.entries.solo.LibraryRecognition`), which reads the
  * defines' instructions off the untagged IR and tags them there, a name tag at
  * each position that holds one. This stage works before the front end's
  * tagging instead, on the point, so the tagging itself writes the
  * recognised defines' name tags and every other lambda's closure tag.
  */
object LibraryRecognition:

  /** The program with every closed subterm that is a define replaced by the
    * define's constant, outermost first.
    */
  def recognised(term: DeBruijnTerm, defines: Set[Instruction]): Recognition =
    val (visit, state) = visited(term, defines, State(0, 0L)).result
    Recognition(visit.term, state.recognised, state.operations)

  /** The walk's state: the subterms recognised and the operations spent. */
  private final case class State(recognised: Int, operations: Long)

  /** A subterm visited: the term written out, each recognised subterm a
    * constant; the same subterm with every closed subterm the constant of
    * its instruction, from which a chain is converted; its looseness, the least
    * number of enclosing binders under which it is closed; and its instruction
    * when it is closed.
    */
  private final case class Visited(term: DeBruijnTerm, compact: DeBruijnTerm, looseness: Int, instruction: Option[Instruction])

  private val unbounded: Int = Int.MaxValue

  private def visited(term: DeBruijnTerm, defines: Set[Instruction], state: State): TailRec[(Visited, State)] =
    term match
      case DeBruijnTerm.Variable(index) =>
        done((Visited(term, term, if index < 0 then unbounded else index + 1, None), state))
      case DeBruijnTerm.Constant(instruction) =>
        done((Visited(term, term, 0, Some(instruction)), state))
      case DeBruijnTerm.Free(name) =>
        throw IllegalArgumentException(s"library recognition reads a term with no free name, found $name")
      case DeBruijnTerm.Lambda(_) =>
        val (count, body) = chain(term, 0)
        tailcall(visited(body, defines, state)).map((bodyVisit, afterBody) =>
          val looseness =
            if bodyVisit.looseness == unbounded then unbounded else math.max(0, bodyVisit.looseness - count)
          val written = lambdas(bodyVisit.term, count)
          val compact = lambdas(bodyVisit.compact, count)
          if looseness == 0 then
            val conversion = Defunctionalization.thunkInstructionCounted(compact)
            closed(
              written,
              conversion.value,
              defines,
              afterBody.copy(operations = afterBody.operations + conversion.operations)
            )
          else (Visited(written, compact, looseness, None), afterBody)
        )
      case DeBruijnTerm.Apply(function, argument) =>
        parts(Vector(function, argument), defines, state).map((visits, afterParts) =>
          val Vector(functionVisit, argumentVisit) = visits: @unchecked
          combined(
            visits,
            DeBruijnTerm.Apply(functionVisit.term, argumentVisit.term),
            DeBruijnTerm.Apply(functionVisit.compact, argumentVisit.compact),
            instructions =>
              val Vector(functionInstruction, argumentInstruction) = instructions: @unchecked
              Apply(functionInstruction, argumentInstruction),
            defines,
            afterParts
          )
        )
      case DeBruijnTerm.Parallel(left, right) =>
        parts(Vector(left, right), defines, state).map((visits, afterParts) =>
          val Vector(leftVisit, rightVisit) = visits: @unchecked
          combined(
            visits,
            DeBruijnTerm.Parallel(leftVisit.term, rightVisit.term),
            DeBruijnTerm.Parallel(leftVisit.compact, rightVisit.compact),
            instructions =>
              val Vector(leftInstruction, rightInstruction) = instructions: @unchecked
              Parallel(leftInstruction, rightInstruction),
            defines,
            afterParts
          )
        )
      case DeBruijnTerm.Choice(left, right) =>
        parts(Vector(left, right), defines, state).map((visits, afterParts) =>
          val Vector(leftVisit, rightVisit) = visits: @unchecked
          combined(
            visits,
            DeBruijnTerm.Choice(leftVisit.term, rightVisit.term),
            DeBruijnTerm.Choice(leftVisit.compact, rightVisit.compact),
            instructions =>
              val Vector(leftInstruction, rightInstruction) = instructions: @unchecked
              Choice(leftInstruction, rightInstruction),
            defines,
            afterParts
          )
        )

  /** The visits of the parts, in order, the state threaded. */
  private def parts(terms: Vector[DeBruijnTerm], defines: Set[Instruction], state: State): TailRec[(Vector[Visited], State)] =
    Trampoline.threaded(terms, state)((part, current) => tailcall(visited(part, defines, current)))

  /** A node of the parts: closed when every part is, its instruction the layer
    * over the parts' instructions; open otherwise.
    */
  private def combined(
      visits: Vector[Visited],
      written: DeBruijnTerm,
      compact: DeBruijnTerm,
      layer: Vector[Instruction] => Layer[Instruction],
      defines: Set[Instruction],
      state: State
  ): (Visited, State) =
    val looseness = visits.map(_.looseness).maxOption.getOrElse(0)
    if looseness == 0 then
      val counted = Interning.layerInternedCounted(layer(visits.map(_.instruction.getOrElse(
        throw IllegalStateException("a closed part with no instruction")
      ))))
      closed(written, counted.value, defines, state.copy(operations = state.operations + counted.operations))
    else (Visited(written, compact, looseness, None), state)

  /** A closed subterm of the instruction: the define's constant when the instruction
    * is a define's, the term written out otherwise.
    */
  private def closed(written: DeBruijnTerm, instruction: Instruction, defines: Set[Instruction], state: State): (Visited, State) =
    val constant = DeBruijnTerm.Constant(instruction)
    if defines.contains(instruction) then (Visited(constant, constant, 0, Some(instruction)), state.copy(recognised = state.recognised + 1))
    else (Visited(written, constant, 0, Some(instruction)), state)

  /** The chain of abstractions at the term: their number and the body under
    * them, which is no abstraction.
    */
  @tailrec
  private def chain(term: DeBruijnTerm, count: Int): (Int, DeBruijnTerm) = term match
    case DeBruijnTerm.Lambda(body) => chain(body, count + 1)
    case other                     => (count, other)

  /** The body under the number of abstractions. */
  private def lambdas(body: DeBruijnTerm, count: Int): DeBruijnTerm =
    (1 to count).foldLeft(body)((inner, _) => DeBruijnTerm.Lambda(inner))
