package com.yang_bo.gezi.proofs

import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.lemmaencoding.EncodedLemma

/** The proof a search strategy gives that each of its inputs equals its output,
  * the schedule's THE PROOF (`gezi/prolog/gezi/schedule.pl`): its NODES,
  * numbered from 0 in the order the search made them, each by its layer as it
  * was made (`com.yang_bo.gezi.egraph.EGraph.madeLayer`), over the numbers of the nodes its
  * maker passed, a leaf (a noinline instruction, a storage the graph keeps as a
  * leaf, an eigenvariable) holding its term of the configuration `C`; its
  * unions, in the order the search made them, the `i`-th numbered `i` from 1,
  * each between two nodes; and one equation for each input, in order, by the
  * nodes whose classes hold its two sides. Each union joins two classes of the
  * equivalence the unions before it make, so the unions form a forest over the
  * nodes, and the two nodes of each equation are in one tree. The proof builds
  * no term: the article writer reads each node's term from its layer
  * (`ProofTerms`). The proof also holds the lemmas it may name, as the search
  * encoded them into patterns: an instance of a lemma binds the metavariables
  * of that encoding, which the article states and matches the lemma by.
  */
final case class StrategyProof[C <: NativeSpecializer & Singleton](
    layers: Vector[LayerWith[Int, Configured[C]]],
    unions: Vector[ProofUnion],
    equations: Vector[ProofEquation],
    lemmas: Vector[EncodedLemma[C]]
)

/** A step of a search: the union numbered `index` of two nodes of the proof,
  * why the two are equal, and the nodes the union's own step made, if it made
  * any (`com.yang_bo.gezi.egraph.UnionRecord`'s `made`).
  */
final case class ProofUnion(
    index: Int,
    first: Int,
    second: Int,
    justification: Justification,
    made: Option[MadeNodes]
):

  /** The one of the two nodes the union's step made, the last it made. */
  def built: Option[Int] = made.map(_.last)

/** The first and the last node a step made (`com.yang_bo.gezi.egraph.MadeNodes`): the step
  * made every node between them, and the last is the root of what it built.
  */
final case class MadeNodes(first: Int, last: Int)

/** The nodes of a proof whose classes hold an input and its output: a search
  * may have made another spelling of a term than the one a round gives.
  */
final case class ProofEquation(leftAt: Int, rightAt: Int)

/** Why a union holds. Every term it names is a node of the proof. */
enum Justification:

  /** An instance of the lemma: each metavariable bound to a node, or to nothing
    * when no side mentions it.
    */
  case Lemma(lemma: LemmaIdentifier, bindings: Vector[Option[Int]])

  /** An instance of the lemma whose bindings the search did not record; the
    * writer refuses it.
    */
  case LemmaWithoutBindings(lemma: LemmaIdentifier)

  /** The two nodes are one layer over classes united earlier, or two spellings
    * of one application.
    */
  case Congruence

  /** A native storage s the graph keeps as a leaf, the node `storage`, and its
    * pattern view `s ∥ T`, T its criterion: s = v ∥ T by the storage's
    * definition, then (4) and the idempotence of ∥ that (6) and (5) give.
    */
  case PatternView(storage: Int)

  /** A native storage `s` the graph kept as a leaf, the node `storage`, united
    * with the node of its view, `s = v ∥ T`: the article writes a storage as
    * its view, so the union is the congruence of the parallel over the forest's
    * paths between the view's sides and the node's children.
    */
  case StorageView(storage: Int)

  /** An application united with the storage of the native's result on the
    * storages of the nodes `arguments`, the node `define` bound to the native
    * named: the application equals `define a1 … an` by the forest, and that
    * equals the result by the native's obligation with the unique spelling's
    * pattern theorem at each storage, imported as one equation
    * (`Axiom.Native`).
    */
  case Folding(native: String, define: Int, arguments: Vector[Int])

  /** An application united with the body of the closure its function's class
    * holds.
    */
  case Beta

  /** A β conversion, `reduct` the node of the two that the other reduces to:
    * the trace keeps it as a `Convert` command, whose replacement the replay
    * computes, and the writer imports it as its conversion equation
    * (`Axiom.Conversion`), which the checker decides.
    */
  case BetaConversion(reduct: Int)

  /** The abstraction rule ξ: a closure united with the thunk written back from
    * its body opened at the eigenvariables (opaque leaves, in lambda order) and
    * rewritten to the spelling, the body and the spelling united earlier. The
    * trace keeps it as an `Abstraction` command over the body's steps; the
    * writer refuses it until extensionality is imported (Lean
    * `Derivable.extensional`).
    */
  case Abstraction(eigenvariables: Vector[Int], body: Int, spelling: Int)

  /** The η rule: the node `thunk`, a thunk of one hole whose code applies its
    * one filling to the hole, united with that filling (`Axiom.Eta`).
    */
  case Eta(thunk: Int)

  /** A closure unit, the node `function`, united with the artifact of its
    * compilation, an equation the compilation's own graph derives.
    */
  case Compiled(function: Int)

  /** A step a valuation justified; the writer has no proof of it. */
  case Valuation(justification: Justification)
