package gezi.strategies

import gezi.proofs.Justification
import gezi.proofs.MadeTerms
import gezi.proofs.ProofEquation
import gezi.proofs.ProofUnion
import gezi.proofs.StrategyProof
import gezi.egraph.EGraph
import gezi.egraph.Justification as GraphJustification
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.lemmaencoding.EncodedLemma
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.NoinlineLeaf

/** The proof of a graph a run left (THE PROOF of
  * `gezi/prolog/gezi/baseline/fixpoint_search.pl`,
  * `graph_proof/3`): the nodes as the terms they stand for, in creation
  * order, a node's term its layer as it was made over the terms of the nodes
  * its maker passed (`EGraph.madeLayer`), so that a node's term is the term
  * made, an eigenvariable never in a term made outside its opening; the
  * unions with their two nodes
  * and the nodes a lemma instance bound read as those terms; and for each
  * equation the terms of the nodes of its two sides, which the article
  * writer matches the two sides against. The proof is the one
  * `gezi.proofs.StrategyProof` the writer reads. A side with no node
  * throws `FixpointSearchError` with `NotInTheGraph`. The graph must record
  * the terms made (`EGraph.explained`); a graph that does not throws
  * `IllegalArgumentException`.
  */
object GraphProof:

  /** The proof of the graph that joins the two sides of each equation, an
    * input and its output, the graph saturated with the lemmas as encoded.
    */
  def proof(
      graph: EGraph,
      equations: Vector[(Instruction, Instruction)],
      lemmas: Vector[EncodedLemma]
  ): StrategyProof =
    require(graph.explained, "a proof reads a graph that records the terms made (EGraph.explained)")
    val terms = (0 until graph.nodeCount).foldLeft(Vector.empty[Instruction]) { (made, node) =>
      graph.madeLayer(node) match
        case NoinlineLeaf(instruction) => made :+ instruction
        case layer              => made :+ Instruction(layer.map(made))
    }
    val unions = graph.unions.zipWithIndex.map { (union, index) =>
      ProofUnion(index + 1, terms(union.first), terms(union.second), justification(union.justification, terms), union.made.map(made => MadeTerms(terms(made.first), terms(made.last))))
    }
    val equationsAt = equations.map((left, right) =>
      ProofEquation(terms(sideNode(graph, left)), terms(sideNode(graph, right)))
    )
    StrategyProof(terms, unions, equationsAt, lemmas)

  private def justification(justification: GraphJustification, terms: Vector[Instruction]): Justification =
    justification match
      case GraphJustification.Lemma(lemma, bindings) => Justification.Lemma(lemma, bindings.map(_.map(terms)))
      case GraphJustification.Congruence             => Justification.Congruence
      // The thunk the step took is not read: the writer finds the closure
      // of the step itself (`ProofMatching.betaProofs`).
      case GraphJustification.Beta(_)                => Justification.Beta
      // The abstraction rule ξ of a body written back
      // (`HigherOrderSaturator`'s openings): the article states the closures'
      // equation after the opened bodies' theorem, and the round certificate
      // proves it (`LambdaJit.RoundCertificate.abstracted`).
      case GraphJustification.Abstraction(eigenvariables, body, spelling) =>
        Justification.Abstraction(eigenvariables.map(terms), terms(body), terms(spelling))
      // β conversion (`HigherOrderSaturator`'s root reverse β,
      // `HigherOrderMatching`'s expansions and normalizations) is several β
      // steps, under abstractions too, that the normal form does not record:
      // the writer imports the union as its conversion equation
      // (`Axiom.Conversion`), which the Lean checker decides by a search for
      // the steps (`EndToEnd.conversionChecked`).
      case GraphJustification.BetaConversion(reduct) => Justification.BetaConversion(terms(reduct))

  /** The node of a side, an instruction, found layer by layer in the graph,
    * nothing made (`side_term/4`).
    */
  private def sideNode(graph: EGraph, side: Instruction): Int =
    termNode(graph, side).result.getOrElse(
      throw FixpointSearchError(FixpointSearchErrorReason.NotInTheGraph(side))
    )

  /** `term_node/3`: the node of the instruction, or of its stored layer over the
    * nodes of its children.
    */
  private def termNode(graph: EGraph, instruction: Instruction): TailRec[Option[Int]] =
    graph.instructionNode(instruction) match
      case Some(node) => done(Some(node))
      case None =>
        val layer = instruction.layered
        childNodes(graph, layer.children.toList, Vector.empty).map(
          _.flatMap(nodes => graph.layerNode(FixpointEgraph.layerOver(layer, nodes)))
        )

  private def childNodes(
      graph: EGraph,
      children: List[Instruction],
      found: Vector[Int]
  ): TailRec[Option[Vector[Int]]] = children match
    case Nil => done(Some(found))
    case child :: rest =>
      tailcall(termNode(graph, child)).flatMap {
        case None       => done(None)
        case Some(node) => tailcall(childNodes(graph, rest, found :+ node))
      }
