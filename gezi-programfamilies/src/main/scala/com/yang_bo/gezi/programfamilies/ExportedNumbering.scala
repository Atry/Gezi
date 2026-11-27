package com.yang_bo.gezi.programfamilies

import com.yang_bo.gezi.backendcomparison.ConstantNumbers
import com.yang_bo.gezi.backendcomparison.Projection
import com.yang_bo.gezi.backendcomparison.RunInput
import com.yang_bo.gezi.orientation.Orientation
import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.IrLayer
import com.yang_bo.gezi.ir.NativeStorage
import com.yang_bo.gezi.ir.Opaque
import com.yang_bo.gezi.ir.UriNode
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Store
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** The configuration of the terms here: no facts. */
private given exportedNumberingNoFacts: NoFacts.type = NoFacts

/** A run's input with the exporter's numbering of its instructions and codes:
  * the instructions and the codes in the order the walk numbered them, each
  * one's number its position.
  */
final case class ExportedInput(
    runInput: RunInput[NoFacts.type],
    instructions: Vector[Configured[NoFacts.type]],
    codes: Vector[Code]
):

  /** The numbers of the constants of a fixed point's projection in this
    * numbering.
    */
  def constantNumbers(
      projection: Projection[NoFacts.type]
  ): ConstantNumbers[NoFacts.type] =
    ConstantNumbers.numbered(instructions, codes, projection)

/** The numbering of instructions, codes and lemmas the Prolog exporter gave a
  * fixture (its `store_numbered/4`). Each kind is numbered densely from 0 in
  * the order one walk first meets it: the pattern instructions in order, then
  * each orientation in order (its lemma, its matched side, its added side, its
  * shared parts, each pattern in preorder), then the inputs. An instruction met
  * the first time is numbered and its layer walked at once, its children in
  * layer order and a thunk's code before its fillings; a noinline instruction
  * is not expanded. A code met the first time is numbered and walked the same
  * way.
  *
  * The form of a fixed point names leaves and codes by number
  * (`com.yang_bo.gezi.backendcomparison.ConstantNumbers`), so a run compared with the
  * reference forms of the fixtures reads its constants in this numbering. The
  * instructions stay the canonical instructions; lemmas, which are numbered in
  * any case, are renumbered.
  */
object ExportedNumbering:

  /** One thing the walk meets. */
  private enum Met[C <: NativeSpecializer & Singleton]:
    case InstructionMet(instruction: Configured[C])
    case CodeMet(code: Code)
    case PatternMet(pattern: Pattern[C])
    case LemmaMet(lemma: LemmaIdentifier)

  /** The numbers given so far: the instructions and codes in the order they
    * were numbered, the sets of those met, and each lemma's number.
    */
  private final case class Numbers[C <: NativeSpecializer & Singleton](
      instructionOrder: Vector[Configured[C]],
      instructionsMet: Set[Configured[C]],
      codeOrder: Vector[Code],
      codesMet: Set[Code],
      lemmas: Map[LemmaIdentifier, LemmaIdentifier]
  )

  /** The run's input with the exporter's numbering: the orientations with their
    * lemmas renumbered, the pattern instructions, the inputs and the budget,
    * and the instructions and codes in their numbering. `noinline` are the
    * instructions the e-graph never expands.
    */
  def renumbered(
      noinline: Set[Configured[NoFacts.type]],
      orientations: Vector[Orientation[NoFacts.type]],
      patternInstructions: Vector[Configured[NoFacts.type]],
      inputs: Vector[Configured[NoFacts.type]],
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
    val numbers = walked[NoFacts.type](
      start.toList,
      noinline,
      Numbers(Vector.empty, Set.empty, Vector.empty, Set.empty, Map.empty)
    )
    val runInput = RunInput(
      Store(noinline, com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts)),
      orientations.map(orientation =>
        orientation.copy(lemma = numbers.lemmas(orientation.lemma))
      ),
      patternInstructions,
      inputs,
      budget
    )
    ExportedInput(runInput, numbers.instructionOrder, numbers.codeOrder)

  /** The walk: the first thing pending met, and what it leads to put before the
    * rest, so that the things are numbered in preorder.
    */
  @tailrec
  private def walked[C <: NativeSpecializer & Singleton](
      pending: List[Met[C]],
      noinline: Set[Configured[C]],
      numbers: Numbers[C]
  )(using C): Numbers[C] = pending match
    case Nil         => numbers
    case met :: rest =>
      met match
        case Met.InstructionMet(instruction) =>
          if numbers.instructionsMet.contains(instruction) then
            walked(rest, noinline, numbers)
          else
            val numbered = numbers.copy(
              instructionOrder = numbers.instructionOrder :+ instruction,
              instructionsMet = numbers.instructionsMet + instruction
            )
            val below =
              if noinline.contains(instruction) then Nil
              else layerParts(instruction, instruction.layer)
            walked(below ++ rest, noinline, numbered)
        case Met.CodeMet(code) =>
          if numbers.codesMet.contains(code) then
            walked(rest, noinline, numbers)
          else
            val numbered = numbers.copy(
              codeOrder = numbers.codeOrder :+ code,
              codesMet = numbers.codesMet + code
            )
            walked(codeParts(code.layer) ++ rest, noinline, numbered)
        case Met.PatternMet(pattern) =>
          val below = pattern match
            case Pattern.InstructionReference(instruction) =>
              List(Met.InstructionMet(instruction))
            case Pattern.Thunk(code, _, fillings) =>
              Met.CodeMet(code) :: fillings.map(Met.PatternMet(_)).toList
            case compound => compound.children.map(Met.PatternMet(_)).toList
          walked(below ++ rest, noinline, numbers)
        case Met.LemmaMet(lemma) =>
          val numbered =
            if numbers.lemmas.contains(lemma) then numbers
            else
              numbers.copy(lemmas =
                numbers.lemmas
                  .updated(lemma, LemmaIdentifier(numbers.lemmas.size))
              )
          walked(rest, noinline, numbered)

  /** The parts of an instruction's layer the walk meets, in layer order. */
  private def layerParts[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      layer: IrLayer[Configured[C]]
  )(using C): List[Met[C]] = layer match
    case Thunk(code, _, fillings) =>
      Met.CodeMet(code) :: fillings.map(Met.InstructionMet(_)).toList
    case _: UriNode | _: Opaque | _: NativeStorage =>
      throw IllegalStateException(
        s"the instruction $instruction has a leaf layer"
      )
    case Apply(function, argument) =>
      List(Met.InstructionMet(function), Met.InstructionMet(argument))
    case Parallel(left, right) =>
      List(Met.InstructionMet(left), Met.InstructionMet(right))
    case Choice(left, right) =>
      List(Met.InstructionMet(left), Met.InstructionMet(right))

  /** The parts of a code the walk meets, in order. */
  private def codeParts[C <: NativeSpecializer & Singleton](
      code: CodeLayer[Code]
  ): List[Met[C]] = code match
    case Slot(_)                   => Nil
    case Apply(function, argument) =>
      List(Met.CodeMet(function), Met.CodeMet(argument))
    case Parallel(left, right) => List(Met.CodeMet(left), Met.CodeMet(right))
    case Choice(left, right)   => List(Met.CodeMet(left), Met.CodeMet(right))
    case Thunk(inner, _, fillings) =>
      (inner +: fillings).map(Met.CodeMet(_)).toList
