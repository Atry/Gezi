package gezi.strategies

import hedgehog.Gen
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.ematching.closures.ClosureCompilation
import gezi.ematching.indexing.Indexing
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Reachability
import gezi.ir.Store
import gezi.ir.{Apply, Thunk}
import gezi.saturation.HigherOrderMatching
import gezi.saturation.Saturation

/** The law that reading a code's body by `HigherOrderMatching.bodyAdded`,
  * which the β rule uses for a code the compiled program was not built with
  * (a thunk the graph respelled)
  * and the body opening uses for every closure, builds what the compiled body
  * builds (`ClosureCompilation`'s body of `Indexing.codeBuilding`): the same
  * nodes, in the same order, with the same layers, and the same applications
  * marked for the β rule to read. Its inputs are the front end's thunks of
  * generated lambdas whose body applies an inner lambda that reads the outer
  * binder, a redex of the code such as a let; the holes are read at fresh
  * leaves and the fillings at their nodes.
  *
  * Purpose: catch two readers of one code that build different graphs. The
  * case that set it (2026-11-16): `bodyAdded` did not mark a redex of the
  * code readable, so the bodies of respelled thunks kept their lets
  * unreduced, a chain of β steps was missing, and `contest-entries-wren`'s extracted
  * narrow-block cost on calls_10000_hot/direct rose from 166 to 1,922.
  */
class BodyReadingLawTest extends GeneratedProperties:

  /** `λx. (λy. y x + B x y) A x`, B and A generated: the code applies the
    * inner thunk `λy. …`, which reads x and so stays in the code.
    */
  private val lambdas: Gen[Term] =
    for
      inner <- Gen.sized(size => HoasGenerators.openTerm(2, size.value / 2))
      argument <- Gen.sized(size => HoasGenerators.openTerm(1, size.value / 2))
    yield Term.λ(outer => Term.λ(bound => Term.choice(bound(outer), inner(Vector(outer, bound))))(argument(Vector(outer))))

  private def redexes(code: Code): Int = code.layer match
    case Apply(function, argument) =>
      (function.layer match
        case Thunk(_, _, _) => 1
        case _              => 0) + redexes(function) + redexes(argument)
    case Thunk(_, _, fillings) => fillings.map(redexes).sum
    case gezi.ir.Parallel(left, right) => redexes(left) + redexes(right)
    case gezi.ir.Choice(left, right)   => redexes(left) + redexes(right)
    case gezi.ir.Slot(_)               => 0

  property("reading a code's body builds the compiled body's nodes, its redexes marked alike") {
    for lambda <- lambdas.forAllWithLog(gezi.generatedinputs.LambdalatticeText.text)
    yield
      val instruction = Defunctionalization.thunkInstruction(lambda.deBruijnTerm(Map.empty))
      instruction.layer match
        case Thunk(code, holes, fillings) =>
          val leaves = holes.indices.toVector.map(position => Instruction.opaque(s"hole $position"))
          val (withLeaves, leafNodes) = leaves.foldLeft((EGraph.empty(Store(noinline = leaves.toSet), Map.empty, explained = false), Vector.empty[Int])) {
            case ((current, nodes), leaf) =>
              val (next, node) = current.instructionAdded(leaf)
              (next, nodes :+ node)
          }
          val (graph, fillingNodes) = fillings.foldLeft((withLeaves, Vector.empty[Int])) { case ((current, nodes), filling) =>
            val (next, node) = current.instructionAdded(filling)
            (next, nodes :+ node)
          }
          val values = Saturation.slotValues(holes, leafNodes, fillingNodes)
          val (read, readNode) = HigherOrderMatching.bodyAdded(graph, code, values)
          val compiled = ClosureCompilation.compiled(Indexing.program(Vector.empty, Reachability.codesUnder(Vector(instruction), Vector(code))))
          val (built, builtNode) = compiled.body(code, graph, values)
          def marked(of: EGraph): Vector[(gezi.ir.Layer[Int], Boolean)] =
            (0 until of.nodeCount).toVector.map(node => (of.layer(node), of.readable(node)))
          Result
            .all(
              List(
                Result.assert(redexes(code) > 0).log(s"the code holds no redex: the generator drifted: $code"),
                Result.diff(readNode, builtNode)(_ == _),
                Result.diff(marked(read), marked(built))(_ == _)
              )
            )
        case other => Result.failure.log(s"the front end's term is no thunk: $other")
  }
