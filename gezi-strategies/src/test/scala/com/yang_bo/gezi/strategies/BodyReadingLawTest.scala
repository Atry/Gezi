package com.yang_bo.gezi.strategies

import hedgehog.Gen
import hedgehog.Result
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Reachability
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.ir.{Apply, Thunk}
import com.yang_bo.gezi.saturation.HigherOrderMatching
import com.yang_bo.gezi.saturation.Saturation

/** The law that reading a code's body by `HigherOrderMatching.bodyAdded`, which
  * the β rule uses for a code the compiled program was not built with (a thunk
  * the graph respelled) and the body opening uses for every closure, builds
  * what the compiled body builds (`ClosureCompilation`'s body of
  * `Indexing.codeBuilding`): the same nodes, in the same order, with the same
  * layers, and the same applications marked for the β rule to read. Its inputs
  * are the front end's thunks of generated lambdas whose body applies an inner
  * lambda that reads the outer binder, a redex of the code such as a let; the
  * holes are read at fresh leaves and the fillings at their nodes.
  *
  * Purpose: catch two readers of one code that build different graphs. The case
  * that set it (2026-11-16): `bodyAdded` did not mark a redex of the code
  * readable, so the bodies of respelled thunks kept their lets unreduced, a
  * chain of β steps was missing, and `contest-entries-wren`'s extracted
  * narrow-block cost on calls_10000_hot/direct rose from 166 to 1,922.
  */
class BodyReadingLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  /** `λx. (λy. y x + B x y) A x`, B and A generated: the code applies the inner
    * thunk `λy. …`, which reads x and so stays in the code.
    */
  private val lambdas: Gen[Term] =
    for
      inner <- Gen.sized(size => HoasGenerators.openTerm(2, size.value / 2))
      argument <- Gen.sized(size => HoasGenerators.openTerm(1, size.value / 2))
    yield Term.λ(outer =>
      Term.λ(bound => Term.choice(bound(outer), inner(Vector(outer, bound))))(
        argument(Vector(outer))
      )
    )

  private def redexes(code: Code): Int = code.layer match
    case Apply(function, argument) =>
      (function.layer match
        case Thunk(_, _, _) => 1
        case _              => 0
      ) + redexes(function) + redexes(argument)
    case Thunk(_, _, fillings)         => fillings.map(redexes).sum
    case com.yang_bo.gezi.ir.Parallel(left, right) => redexes(left) + redexes(right)
    case com.yang_bo.gezi.ir.Choice(left, right)   => redexes(left) + redexes(right)
    case com.yang_bo.gezi.ir.Slot(_)               => 0

  property(
    "reading a code's body builds the compiled body's nodes, its redexes marked alike"
  ) {
    for lambda <- lambdas.forAllWithLog(
        com.yang_bo.gezi.generatedinputs.LambdalatticeText.text
      )
    yield
      val instruction =
        Defunctionalization.thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](
          lambda.deBruijnTerm(Map.empty)
        )(using com.yang_bo.gezi.ir.NoFacts)
      instruction.layer match
        case Thunk(code, holes, fillings) =>
          val leaves = holes.indices.toVector.map(position =>
            NoFacts.opaque(s"hole $position")
          )
          val (withLeaves, leafNodes) = leaves.foldLeft(
            (
              EGraph.empty(
                Store(
                  noinline = leaves.toSet,
                  com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts)
                ),
                Map.empty,
                explained = false
              ),
              Vector.empty[Int]
            )
          ) { case ((current, nodes), leaf) =>
            val (next, node) = current.instructionAdded(leaf)
            (next, nodes :+ node)
          }
          val (graph, fillingNodes) =
            fillings.foldLeft((withLeaves, Vector.empty[Int])) {
              case ((current, nodes), filling) =>
                val (next, node) = current.instructionAdded(filling)
                (next, nodes :+ node)
            }
          val values = Saturation.slotValues(holes, leafNodes, fillingNodes)
          val (read, readNode) =
            HigherOrderMatching.bodyAdded(graph, code, values)
          val compiled = ClosureCompilation.compiled(
            Indexing.program(
              Vector.empty,
              Reachability.codesUnder(Vector(instruction), Vector(code))
            )
          )
          val (built, builtNode) = compiled.body(code, graph, values)
          def marked(
              of: EGraph[NoFacts.type]
          ): Vector[(com.yang_bo.gezi.ir.Layer[Int], Boolean)] =
            (0 until of.nodeCount).toVector.map(node =>
              (of.layer(node), of.readable(node))
            )
          Result
            .all(
              List(
                Result
                  .assert(redexes(code) > 0)
                  .log(
                    s"the code holds no redex: the generator drifted: $code"
                  ),
                Result.diff(readNode, builtNode)(_ == _),
                Result.diff(marked(read), marked(built))(_ == _)
              )
            )
        case other =>
          Result.failure.log(s"the front end's term is no thunk: $other")
  }
