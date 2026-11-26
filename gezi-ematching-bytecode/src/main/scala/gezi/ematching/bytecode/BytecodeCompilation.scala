package gezi.ematching.bytecode

import gezi.egraph.GraphBuilding
import gezi.egraph.GraphView
import gezi.ematching.Backend
import gezi.ematching.CompiledProgram
import gezi.ematching.Matching
import gezi.ematching.Program
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ir.Code

/** The backend that compiles a program into one hidden class (the package's
  * documentation gives the discipline of the generated code). The tree of
  * the seeds filed under a kind and a key (`Program.trees`) is an entry of
  * the class, numbered in the order of the program's table, and a static
  * method: its registers JVM locals, its `Each` steps loops over the
  * snapshot the graph gives, its branches run one after another; each
  * building is a static method that calls the graph's operations directly.
  * Each seed's matches come out in the order of the closure backend: the
  * entries an `Each` step reads in their order, depth first; the matches of
  * a key are handed over grouped by seed, in the seeds' order.
  */
object BytecodeCompilation extends Backend:

  def compiled(program: Program): CompiledProgram =
    val entries = program.trees.toVector
    val sharedNumbers = program.orientations
      .scanLeft(0)((first, plan) => first + plan.shared.size)
    val codeNumbers = program.codes.keys.toVector.zipWithIndex.toMap
    CompiledBytecode(
      entries.zipWithIndex
        .groupBy { case (((kind, _), _), _) => kind }
        .map((kind, numbered) =>
          kind -> numbered.map { case (((_, key), _), entry) => key -> entry }.toMap
        ),
      sharedNumbers,
      codeNumbers,
      ClassFileGeneration.generated(
        program,
        entries.map((kindAndKey, tree) => (tree, program.seeds(kindAndKey).size)),
        codeNumbers
      )
    )

private final class CompiledBytecode(
    entries: Map[SeedKind, Map[SeedKey, Int]],
    sharedNumbers: Vector[Int],
    codeNumbers: Map[Code, Int],
    generated: GeneratedProgram
) extends CompiledProgram:

  def matches(
      kind: SeedKind,
      key: SeedKey,
      graph: GraphView,
      delta: Int
  ): Matching =
    entries.get(kind).flatMap(_.get(key)) match
      case Some(entry) => generated.matches(entry, graph, delta)
      case None        => Matching.none

  def added[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    generated
      .added(orientation, graph, bindings.map(_.getOrElse(-1)))
      .asInstanceOf[(Graph, Int)]

  def shared[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      part: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    require(
      part >= 0 && sharedNumbers(orientation) + part < sharedNumbers(orientation + 1),
      s"the orientation $orientation has no shared subterm $part"
    )
    generated
      .shared(sharedNumbers(orientation) + part, graph, bindings.map(_.getOrElse(-1)))
      .asInstanceOf[(Graph, Int)]

  def body[Graph <: GraphBuilding[Graph]](
      code: Code,
      graph: Graph,
      slotValues: Vector[Int]
  ): (Graph, Int) =
    codeNumbers.get(code) match
      case Some(number) => generated.body(number, graph, slotValues).asInstanceOf[(Graph, Int)]
      case None         => GeneratedCodeSupport.missingCode(code).asInstanceOf[(Graph, Int)]
