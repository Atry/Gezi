package gezi.programfamilies

import gezi.backendcomparison.ConstantNumbers
import gezi.backendcomparison.Projection
import gezi.backendcomparison.RunInput
import gezi.orientation.Orientation
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import scala.annotation.tailrec
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}

/** A run's input with the exporter's numbering of its instructions and codes: the
  * instructions and the codes in the order the walk numbered them, each one's
  * number its position.
  */
final case class ExportedInput(runInput: RunInput, instructions: Vector[Instruction], codes: Vector[Code]):

  /** The numbers of the constants of a fixed point's projection in this numbering. */
  def constantNumbers(projection: Projection): ConstantNumbers = ConstantNumbers.numbered(instructions, codes, projection)

/** The numbering of instructions, codes and lemmas the Prolog exporter gave a
  * fixture (its `store_numbered/4`).
  * Each kind is numbered densely from 0 in the order one walk first meets it:
  * the pattern instructions in order, then each orientation in order (its lemma,
  * its matched side, its added side, its shared parts, each pattern in
  * preorder), then the inputs. An instruction met the first time is numbered and
  * its layer walked at once, its children in layer order and a thunk's code
  * before its fillings; a noinline instruction is not expanded. A code met the
  * first time is numbered and walked the same way.
  *
  * The form of a fixed point names leaves and codes by number
  * (`gezi.backendcomparison.ConstantNumbers`), and the text of an input
  * (`InputText`) names every instruction and code by number, so a run compared
  * with the reference forms and inputs of the fixtures reads its constants
  * in this numbering. The instructions stay the canonical instructions; lemmas, which
  * are numbered in any case, are renumbered.
  */
object ExportedNumbering:

  /** One thing the walk meets. */
  private enum Met:
    case InstructionMet(instruction: Instruction)
    case CodeMet(code: Code)
    case PatternMet(pattern: Pattern)
    case LemmaMet(lemma: LemmaIdentifier)

  /** The numbers given so far: the instructions and codes in the order they were
    * numbered, the sets of those met, and each lemma's number.
    */
  private final case class Numbers(
      instructionOrder: Vector[Instruction],
      instructionsMet: Set[Instruction],
      codeOrder: Vector[Code],
      codesMet: Set[Code],
      lemmas: Map[LemmaIdentifier, LemmaIdentifier]
  )

  /** The run's input with the exporter's numbering: the orientations with
    * their lemmas renumbered, the pattern instructions, the inputs and the
    * budget, and the instructions and codes in their numbering. `noinline` are
    * the instructions the e-graph never expands.
    */
  def renumbered(
      noinline: Set[Instruction],
      orientations: Vector[Orientation],
      patternInstructions: Vector[Instruction],
      inputs: Vector[Instruction],
      budget: Int
  ): ExportedInput =
    val start =
      patternInstructions.map(Met.InstructionMet(_)) ++
        orientations.flatMap(orientation =>
          Vector(
            Met.LemmaMet(orientation.lemma),
            Met.PatternMet(orientation.matched),
            Met.PatternMet(orientation.added)
          ) ++ orientation.shared.map(Met.PatternMet(_))
        ) ++
        inputs.map(Met.InstructionMet(_))
    val numbers = walked(
      start.toList,
      noinline,
      Numbers(Vector.empty, Set.empty, Vector.empty, Set.empty, Map.empty)
    )
    val runInput = RunInput(
      Store(noinline),
      orientations.map(orientation => orientation.copy(lemma = numbers.lemmas(orientation.lemma))),
      patternInstructions,
      inputs,
      budget
    )
    ExportedInput(runInput, numbers.instructionOrder, numbers.codeOrder)

  /** The walk: the first thing pending met, and what it leads to put before
    * the rest, so that the things are numbered in preorder.
    */
  @tailrec
  private def walked(
      pending: List[Met],
      noinline: Set[Instruction],
      numbers: Numbers
  ): Numbers = pending match
    case Nil => numbers
    case met :: rest =>
      met match
        case Met.InstructionMet(instruction) =>
          if numbers.instructionsMet.contains(instruction) then walked(rest, noinline, numbers)
          else
            val numbered = numbers.copy(
              instructionOrder = numbers.instructionOrder :+ instruction,
              instructionsMet = numbers.instructionsMet + instruction
            )
            val below =
              if noinline.contains(instruction) then Nil
              else layerParts(instruction, instruction.layered)
            walked(below ++ rest, noinline, numbered)
        case Met.CodeMet(code) =>
          if numbers.codesMet.contains(code) then walked(rest, noinline, numbers)
          else
            val numbered = numbers.copy(
              codeOrder = numbers.codeOrder :+ code,
              codesMet = numbers.codesMet + code
            )
            walked(codeParts(code.layer) ++ rest, noinline, numbered)
        case Met.PatternMet(pattern) =>
          val below = pattern match
            case Pattern.InstructionReference(instruction) => List(Met.InstructionMet(instruction))
            case Pattern.Thunk(code, _, fillings) =>
              Met.CodeMet(code) :: fillings.map(Met.PatternMet(_)).toList
            case compound => compound.children.map(Met.PatternMet(_)).toList
          walked(below ++ rest, noinline, numbers)
        case Met.LemmaMet(lemma) =>
          val numbered =
            if numbers.lemmas.contains(lemma) then numbers
            else numbers.copy(lemmas = numbers.lemmas.updated(lemma, LemmaIdentifier(numbers.lemmas.size)))
          walked(rest, noinline, numbered)

  /** The parts of an instruction's layer the walk meets, in layer order. */
  private def layerParts(instruction: Instruction, layer: Layer[Instruction]): List[Met] = layer match
    case Thunk(code, _, fillings) =>
      Met.CodeMet(code) :: fillings.map(Met.InstructionMet(_)).toList
    case NoinlineLeaf(_) =>
      throw IllegalStateException(s"the instruction $instruction has a leaf layer")
    case compound => compound.children.map(Met.InstructionMet(_)).toList

  /** The parts of a code the walk meets, in order. */
  private def codeParts(code: CodeLayer[Code]): List[Met] = code match
    case Slot(_)                    => Nil
    case Apply(function, argument)  => List(Met.CodeMet(function), Met.CodeMet(argument))
    case Parallel(left, right)      => List(Met.CodeMet(left), Met.CodeMet(right))
    case Choice(left, right)        => List(Met.CodeMet(left), Met.CodeMet(right))
    case Thunk(inner, _, fillings) => (inner +: fillings).map(Met.CodeMet(_)).toList
