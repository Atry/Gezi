package gezi.strategies

import gezi.proofs.Justification
import gezi.proofs.MadeNodes
import gezi.proofs.ProofEquation
import gezi.proofs.ProofUnion
import gezi.proofs.StrategyProof
import gezi.egraph.EGraph
import gezi.egraph.Justification as GraphJustification
import gezi.lemmaencoding.EncodedLemma
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer}

/** The proof of a graph a run left (THE PROOF of
  * `gezi/prolog/gezi/baseline/fixpoint_search.pl`,
  * `graph_proof/3`): the nodes by their layers as they were made
  * (`EGraph.madeLayer`), over the nodes their makers passed, so that a node's
  * term is the term made, an eigenvariable never in a term made outside its
  * opening; the unions with their two nodes and the nodes a lemma instance
  * bound; and for each equation the nodes of its two sides, which the article
  * writer matches the two sides against. The proof is the one
  * `gezi.proofs.StrategyProof` the writer reads, and it builds no term: the
  * writer reads each node's term from its layer. A side with no node throws
  * `FixpointSearchError` with `NotInTheGraph`. The graph must record the
  * terms made (`EGraph.explained`); a graph that does not throws
  * `IllegalArgumentException`.
  */
object GraphProof:

  /** The proof of the graph that joins the two sides of each equation, an
    * input and its output, the graph saturated with the lemmas as encoded.
    */
  def proof[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      equations: Vector[(Configured[C], Configured[C])],
      lemmas: Vector[EncodedLemma[C]]
  )(using C): StrategyProof[C] =
    require(graph.explained, "a proof reads a graph that records the terms made (EGraph.explained)")
    val layers = Vector.tabulate(graph.nodeCount)(graph.madeLayer)
    val unions = graph.unions.zipWithIndex.map { (union, index) =>
      ProofUnion(
        index + 1,
        union.first,
        union.second,
        justification(union.justification),
        union.made.map(made => MadeNodes(made.first, made.last))
      )
    }
    val equationsAt = equations.map((left, right) => ProofEquation(sideNode(graph, left), sideNode(graph, right)))
    StrategyProof(layers, unions, equationsAt, lemmas)

  private def justification(justification: GraphJustification): Justification =
    justification match
      case GraphJustification.Lemma(lemma, bindings) => Justification.Lemma(lemma, bindings)
      case GraphJustification.Congruence             => Justification.Congruence
      case GraphJustification.PatternView(leaf)      => Justification.PatternView(leaf)
      case GraphJustification.StorageView(leaf)      => Justification.StorageView(leaf)
      case GraphJustification.Folding(native, define, arguments) => Justification.Folding(native, define, arguments)
      // The thunk the step took is not read: the writer finds the closure
      // of the step itself (`ProofMatching.betaProofs`).
      case GraphJustification.Beta(_)                => Justification.Beta
      // The abstraction rule ξ of a body written back
      // (`HigherOrderSaturator`'s openings): the article states the closures'
      // equation after the opened bodies' theorem, and the round certificate
      // proves it (`LambdaJit.RoundCertificate.abstracted`).
      case GraphJustification.Abstraction(eigenvariables, body, spelling) =>
        Justification.Abstraction(eigenvariables, body, spelling)
      // β conversion (`HigherOrderSaturator`'s root reverse β,
      // `HigherOrderMatching`'s expansions and normalizations) is several β
      // steps, under abstractions too, that the normal form does not record:
      // the writer imports the union as its conversion equation
      // (`Axiom.Conversion`), which the Lean checker decides by a search for
      // the steps (`EndToEnd.conversionChecked`).
      case GraphJustification.BetaConversion(reduct) => Justification.BetaConversion(reduct)
      case GraphJustification.Eta(thunk)             => Justification.Eta(thunk)
      case GraphJustification.Compiled(function)     => Justification.Compiled(function)

  /** The node of a side, an instruction, found layer by layer in the graph,
    * nothing made (`side_term/4`).
    */
  private def sideNode[C <: NativeSpecializer & Singleton](graph: EGraph[C], side: Configured[C])(using C): Int =
    termNode(graph, side).result.getOrElse(
      throw FixpointSearchError(FixpointSearchErrorReason.NotInTheGraph(side))
    )

  /** `term_node/3`: the node of the instruction, or of its stored layer over the
    * nodes of its children.
    */
  private def termNode[C <: NativeSpecializer & Singleton](graph: EGraph[C], instruction: Configured[C])(using C): TailRec[Option[Int]] =
    graph.instructionNode(instruction) match
      case Some(node) => done(Some(node))
      case None if instruction.heldAsLeaf => done(None)
      case None =>
        // A storage with no node of its own is found by its view's layer, read with the capability of the graph's store.
        val layer = graph.store.expanded(instruction)
        childNodes(graph, layer.children.toList, Vector.empty).map(
          _.flatMap(nodes => graph.layerNode(FixpointEgraph.layerOver(layer, nodes)))
        )

  private def childNodes[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      children: List[Configured[C]],
      found: Vector[Int]
  )(using C): TailRec[Option[Vector[Int]]] = children match
    case Nil => done(Some(found))
    case child :: rest =>
      tailcall(termNode(graph, child)).flatMap {
        case None       => done(None)
        case Some(node) => tailcall(childNodes(graph, rest, found :+ node))
      }
