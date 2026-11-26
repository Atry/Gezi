package gezi.proofs

import gezi.ir.Instruction
import gezi.ir.LemmaIdentifier
import gezi.lemmaencoding.EncodedLemma

/** The proof a search strategy gives that each of its inputs equals its
  * output, the schedule's THE PROOF (`gezi/prolog/gezi/schedule.pl`):
  * the terms it names, instructions of the IR, each once, in the order the search
  * made them; its unions, in the order the search made them, the `i`-th
  * numbered `i` from 1; and one equation for each input, in order. Each
  * union joins two classes of the equivalence the unions before it make, so
  * the unions form a forest over the terms, and the two terms of each
  * equation are in one tree. The proof also holds the lemmas it may name, as
  * the search encoded them into patterns: an instance of a lemma binds the
  * metavariables of that encoding, which the article states and matches
  * the lemma by.
  */
final case class StrategyProof(
    terms: Vector[Instruction],
    unions: Vector[ProofUnion],
    equations: Vector[ProofEquation],
    lemmas: Vector[EncodedLemma]
)

/** A step of a search: the union numbered `index` of two terms of the proof,
  * why the two are equal, and the terms of the nodes the union's own step
  * made, if it made any (`gezi.egraph.UnionRecord`'s `made`).
  */
final case class ProofUnion(
    index: Int,
    first: Instruction,
    second: Instruction,
    justification: Justification,
    made: Option[MadeTerms]
):

  /** The one of the two terms the union's step made, the last it made. */
  def built: Option[Instruction] = made.map(_.last)

/** The terms of the first and the last node a step made
  * (`gezi.egraph.MadeNodes`): the step made every node between them, in
  * the order of the proof's terms, and the last is the root of what it built.
  */
final case class MadeTerms(first: Instruction, last: Instruction)

/** The terms of a proof whose classes hold an input and its output: a
  * search may have made another spelling of a term than the one a round
  * gives.
  */
final case class ProofEquation(leftAt: Instruction, rightAt: Instruction)

/** Why a union holds. */
enum Justification:

  /** An instance of the lemma: each metavariable bound to a term, or to
    * nothing when no side mentions it.
    */
  case Lemma(lemma: LemmaIdentifier, bindings: Vector[Option[Instruction]])

  /** An instance of the lemma whose bindings the search did not record; the
    * writer refuses it.
    */
  case LemmaWithoutBindings(lemma: LemmaIdentifier)

  /** The two terms are one layer over classes united earlier, or two
    * spellings of one application.
    */
  case Congruence

  /** An application united with the body of the closure its function's
    * class holds.
    */
  case Beta

  /** A β conversion, `reduct` the term of the two that the other reduces
    * to: the trace keeps it as a `Convert` command, whose replacement the
    * replay computes, and the writer imports it as its conversion equation
    * (`Axiom.Conversion`), which the checker decides.
    */
  case BetaConversion(reduct: Instruction)

  /** The abstraction rule ξ: a closure united with the thunk written back
    * from its body opened at the eigenvariables (opaque leaves, in lambda
    * order) and rewritten to the spelling, the body and the spelling united
    * earlier. The trace keeps it as an `Abstraction` command over the body's
    * steps; the writer refuses it until extensionality is imported (Lean
    * `Derivable.extensional`).
    */
  case Abstraction(eigenvariables: Vector[Instruction], body: Instruction, spelling: Instruction)

  /** A step a valuation justified; the writer has no proof of it. */
  case Valuation(justification: Justification)
