package gezi.traceplayer

import gezi.generatedinputs.SeededSnapshots
import gezi.ir.Configured
import gezi.ir.NoFacts
import snapshot4s.generated.snapshotConfig

private given nodeShapeSnapshotTestNoFacts: NoFacts.type = NoFacts

/** What the player draws for generated terms (`TermSequences.term`), node
  * by node, recorded as a seeded snapshot: each node's path, its role under
  * the node above, and its shape (`NodeShape`), a thunk's with its binders
  * and its code (`CodeDisplay`). The drawing is as complex as the code that
  * makes it, so there is no concise law. Its purpose is to show, as a diff
  * beside the inputs, any change of what a node draws, of the roles and
  * paths that key the nodes (`TermView`), or of how a code names a binder
  * or a filling.
  */
class NodeShapeSnapshotTest extends gezi.generatedinputs.FailFastSuite with SeededSnapshots:

  private def outline(term: Configured[NoFacts.type]): String =
    def lines(instruction: Configured[NoFacts.type], path: Vector[Int], role: String): Vector[String] =
      val shape = NodeShape.of(instruction)
      val drawn = shape match
        case NodeShape.Thunk(code, holes, fillings) =>
          s"thunk λ ${CodeDisplay.binders(holes, 0, Map.empty).mkString(" ")}. ${CodeDisplay.of(code, holes, Vector.empty, None, None).text} with $fillings fillings"
        case other => other.toString
      val key = if path.isEmpty then "root" else path.mkString(".")
      s"${"  " * path.size}$key $role: $drawn" +: shape.roles.zipWithIndex.flatMap((under, index) =>
        lines(NodeShape.under(instruction, index), path :+ index, under)
      )
    lines(term, Vector.empty, "term").mkString("\n")

  test("the nodes the player draws for generated terms") {
    assertSeededSnapshot(TermSequences.term, 20261109L, 30, "node_shape/generated_terms.txt")(
      TermSequences.instructionText,
      identity[String]
    )(outline)
  }
