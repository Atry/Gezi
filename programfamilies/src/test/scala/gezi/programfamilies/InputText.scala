package gezi.programfamilies

import gezi.orientation.Orientation
import gezi.orientation.Orientations
import gezi.saturation.Saturation
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.Pattern
import scala.util.hashing.MurmurHash3
import gezi.ir

/** A run's input and the graph built from it before the saturation, written
  * as one text in a fixed order, and the text's digest (`InputAgreementTest`).
  * Every instruction and code is written by its number in the exporter's walk
  * numbering (`ExportedNumbering`), the same for every process: the store's
  * layers and codes in the order of their numbers, the noinline instructions the
  * walk met sorted, and each layer, code and orientation as its case class prints
  * with numbers in place of its instructions and codes, the text the fixtures'
  * numbered instructions gave.
  */
object InputText:

  /** The input and the graph the saturation builds from it: the pattern
    * instructions' graph with the inputs added.
    */
  def ofRun(exported: ExportedInput): String =
    val input = exported.runInput
    val initial = Saturation.initialGraph(
      input.store,
      Orientations.headArityBounds(input.orientations),
      input.patternInstructions,
      explained = false
    )
    val (graph, inputNodes) = Saturation.inputsAdded(initial, input.inputs)
    written(
      exported,
      graph.nodes.map(_.layer),
      graph.instructionFilings,
      inputNodes,
      graph.nodeCount - initial.nodeCount
    )

  /** The input and the graph's records, one item a line. */
  def written(
      exported: ExportedInput,
      initialNodes: Vector[Layer[Int]],
      initialInstructions: Vector[(Instruction, Int)],
      inputNodes: Vector[Int],
      inputNodesMade: Int
  ): String =
    val input = exported.runInput
    val numbering = Numbering(exported.instructions.zipWithIndex.toMap, exported.codes.zipWithIndex.toMap)
    val noinline = input.store.noinline
    (Vector(s"budget ${input.budget}") ++
      exported.codes.map(code => s"code ${numbering.code(code)} ${numbering.codeText(code.layer)}") ++
      exported.instructions
        .filterNot(noinline.contains)
        .map(instruction => s"layer ${numbering.instruction(instruction)} ${numbering.layerText(instruction.layered, numbering.instruction)}") ++
      exported.instructions.filter(noinline.contains).map(numbering.instruction).sorted.map(number => s"noinline $number") ++
      input.orientations.map(orientation => s"orientation ${numbering.orientationText(orientation)}") ++
      input.patternInstructions.map(instruction => s"pattern_handle ${numbering.instruction(instruction)}") ++
      input.inputs.map(instruction => s"input ${numbering.instruction(instruction)}") ++
      initialNodes.map(layer => s"initial_node ${numbering.layerText[Int](layer, identity)}") ++
      initialInstructions.map((instruction, node) => s"initial_handle ${numbering.instruction(instruction)} $node") ++
      inputNodes.map(node => s"input_node $node") ++
      Vector(s"input_nodes_made $inputNodesMade")).mkString("", "\n", "\n")

  /** The number of each instruction and code, and the texts written with them. */
  private final case class Numbering(instruction: Map[Instruction, Int], code: Map[Code, Int]):

    def layerText[Child](layer: Layer[Child], child: Child => Int): String = layer match
      case ir.Apply(function, argument)    => s"Apply(${child(function)},${child(argument)})"
      case ir.Parallel(left, right)        => s"Parallel(${child(left)},${child(right)})"
      case ir.Choice(left, right)          => s"Choice(${child(left)},${child(right)})"
      case ir.Thunk(inner, holes, fillings) => s"Thunk(${code(inner)},$holes,${fillings.map(child)})"
      case ir.NoinlineLeaf(leaf)                   => s"Leaf(${instruction(leaf)})"

    def codeText(body: CodeLayer[ir.Code]): String = body match
      case ir.Slot(index)                   => s"Slot($index)"
      case ir.Apply(function, argument)     => s"Apply(${code(function)},${code(argument)})"
      case ir.Parallel(left, right)         => s"Parallel(${code(left)},${code(right)})"
      case ir.Choice(left, right)           => s"Choice(${code(left)},${code(right)})"
      case ir.Thunk(inner, holes, fillings) => s"Thunk(${code(inner)},$holes,${fillings.map(code)})"

    def patternText(pattern: Pattern): String = pattern match
      case Pattern.Metavariable(index)       => s"Metavariable($index)"
      case Pattern.Closure(index)            => s"Closure($index)"
      case Pattern.InstructionReference(referred) => s"HandleReference(${instruction(referred)})"
      case Pattern.Apply(function, argument) => s"Apply(${patternText(function)},${patternText(argument)})"
      case Pattern.Parallel(left, right)     => s"Parallel(${patternText(left)},${patternText(right)})"
      case Pattern.Choice(left, right)       => s"Choice(${patternText(left)},${patternText(right)})"
      case Pattern.Thunk(inner, holes, fillings) =>
        s"Thunk(${code(inner)},$holes,${fillings.map(patternText)})"

    def orientationText(orientation: Orientation): String =
      import orientation.*
      s"Orientation($index,${lemma.number},$direction,$arity,${patternText(matched)},${patternText(added)},$functions,$essential,${shared.map(patternText)})"

  /** 128 bits of the text: four MurmurHash3 hashes of it under four seeds,
    * in hexadecimal.
    */
  def digest(text: String): String =
    Vector(17, 31, 61, 127).map(seed => f"${MurmurHash3.stringHash(text, seed)}%08x").mkString
