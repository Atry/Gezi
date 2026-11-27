package com.yang_bo.gezi.ematching.bytecode

import com.yang_bo.gezi.egraph.GraphBuilding
import com.yang_bo.gezi.egraph.GraphView
import com.yang_bo.gezi.ematching.Backend
import com.yang_bo.gezi.ematching.CompiledProgram
import com.yang_bo.gezi.ematching.Matching
import com.yang_bo.gezi.ematching.Program
import com.yang_bo.gezi.ematching.SeedKey
import com.yang_bo.gezi.ematching.SeedKind
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.NativeSpecializer

/** The backend that compiles a program into one hidden class (the package's
  * documentation gives the discipline of the generated code). The tree of the
  * seeds filed under a kind and a key (`Program.trees`) is an entry of the
  * class, numbered in the order of the program's table, and a static method:
  * its registers JVM locals, its `Each` steps loops over the snapshot the graph
  * gives, its branches run one after another; each building is a static method
  * that calls the graph's operations directly. Each seed's matches come out in
  * the order of the closure backend: the entries an `Each` step reads in their
  * order, depth first; the matches of a key are handed over grouped by seed, in
  * the seeds' order.
  */
object BytecodeCompilation extends Backend:

  def compiled[C <: NativeSpecializer & Singleton](
      program: Program[C]
  ): CompiledProgram[C] =
    val entries = program.trees.toVector
    val sharedNumbers = program.orientations
      .scanLeft(0)((first, plan) => first + plan.shared.size)
    val codeNumbers = program.codes.keys.toVector.zipWithIndex.toMap
    CompiledBytecode(
      entries.zipWithIndex
        .groupBy { case (((kind, _), _), _) => kind }
        .map((kind, numbered) =>
          kind -> numbered.map { case (((_, key), _), entry) =>
            key -> entry
          }.toMap
        ),
      sharedNumbers,
      codeNumbers,
      ClassFileGeneration.generated(
        program,
        entries.map((kindAndKey, tree) =>
          (tree, program.seeds(kindAndKey).size)
        ),
        codeNumbers
      )
    )

private final class CompiledBytecode[C <: NativeSpecializer & Singleton](
    entries: Map[SeedKind, Map[SeedKey[C], Int]],
    sharedNumbers: Vector[Int],
    codeNumbers: Map[Code, Int],
    generated: GeneratedProgram
) extends CompiledProgram[C]:

  def matches(
      kind: SeedKind,
      key: SeedKey[C],
      graph: GraphView[C],
      delta: Int
  ): Matching =
    entries.get(kind).flatMap(_.get(key)) match
      case Some(entry) => generated.matches(entry, graph, delta)
      case None        => Matching.none

  def added[Graph <: GraphBuilding[C, Graph]](
      orientation: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    // Registered conversion (issue 2261, section 8): the generated class returns an untyped `(Any, Int)`; the graph it
    // builds on is the `Graph` it was handed.
    generated
      .added(orientation, graph, bindings.map(_.getOrElse(-1)))
      .asInstanceOf[(Graph, Int)]

  def shared[Graph <: GraphBuilding[C, Graph]](
      orientation: Int,
      part: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    require(
      part >= 0 && sharedNumbers(orientation) + part < sharedNumbers(
        orientation + 1
      ),
      s"the orientation $orientation has no shared subterm $part"
    )
    // Registered conversion (issue 2261, section 8): as in `added`.
    generated
      .shared(
        sharedNumbers(orientation) + part,
        graph,
        bindings.map(_.getOrElse(-1))
      )
      .asInstanceOf[(Graph, Int)]

  def body[Graph <: GraphBuilding[C, Graph]](
      code: Code,
      graph: Graph,
      slotValues: Vector[Int]
  ): (Graph, Int) =
    // Registered conversion (issue 2261, section 8): as in `added`, for the body of a code; a code the program does not
    // number throws before any graph is returned.
    codeNumbers.get(code) match
      case Some(number) =>
        generated.body(number, graph, slotValues).asInstanceOf[(Graph, Int)]
      case None =>
        GeneratedCodeSupport.missingCode(code).asInstanceOf[(Graph, Int)]
