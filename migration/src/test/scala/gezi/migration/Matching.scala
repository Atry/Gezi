package gezi.migration

import gezi.ir.Layer
import gezi.ir.Pattern
import gezi.ir.{Apply, Choice, Parallel, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** The syntactic match of a pattern with no closure against an instruction,
  * for the migration's law: a site's text must be an instance of the lemma's
  * left side as written, which is the instance the e-graph's matching finds
  * on a graph of the text alone, before any union.
  */
object Matching:

  /** The instruction of each metavariable, from 0 to the arity, when the
    * instruction is an instance of the pattern; a metavariable the pattern
    * does not mention is the instruction itself.
    */
  def bindings[C <: NativeSpecializer & Singleton](pattern: Pattern[C], instruction: Configured[C], arity: Int)(using C): Option[Vector[Configured[C]]] =
    bound(List((pattern, instruction)), Map.empty).map(found =>
      Vector.tabulate(arity)(index => found.getOrElse(index, instruction))
    )

  @scala.annotation.tailrec
  private def bound[C <: NativeSpecializer & Singleton](pending: List[(Pattern[C], Configured[C])], found: Map[Int, Configured[C]])(using C): Option[Map[Int, Configured[C]]] =
    pending match
      case Nil => Some(found)
      case (pattern, instruction) :: rest =>
        val below: Option[List[(Pattern[C], Configured[C])]] = (pattern, instruction.layer) match
          case (Pattern.Metavariable(index), _) =>
            if found.get(index).forall(Configured.same(_, instruction)) then Some(Nil) else None
          case (Pattern.InstructionReference(referenced), _) => Option.when(Configured.same(referenced, instruction))(Nil)
          case (Pattern.Apply(function, argument), Apply(functionInstruction, argumentInstruction)) =>
            Some(List((function, functionInstruction), (argument, argumentInstruction)))
          case (Pattern.Choice(left, right), Choice(leftInstruction, rightInstruction)) =>
            Some(List((left, leftInstruction), (right, rightInstruction)))
          case (Pattern.Parallel(left, right), Parallel(leftInstruction, rightInstruction)) =>
            Some(List((left, leftInstruction), (right, rightInstruction)))
          case (Pattern.Thunk(code, holes, fillings), Thunk(instructionCode, instructionHoles, instructionFillings))
              if (code eq instructionCode) && holes == instructionHoles && fillings.size == instructionFillings.size =>
            Some(fillings.zip(instructionFillings).toList)
          case _ => None
        val withBinding = pattern match
          case Pattern.Metavariable(index) => found.updated(index, instruction)
          case _                           => found
        below match
          case None        => None
          case Some(pairs) => bound(pairs ++ rest, withBinding)
