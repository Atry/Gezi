package gezi.contest.corpora.reductions

import java.nio.file.Path
import gezi.directorysugar.DirectoryTree
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Literals
import gezi.frontend.Term
import gezi.ir.Instruction
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The functions of `problems/cses`, the port of the CSES Problem
  * Set, that
  * the CSES families (`CsesFamilies.scala`) apply to their drawn inputs, and
  * of the problems outside it built as CSES families are
  * (`SpeculativeUntabling.scala`).
  *
  * Each problem is the file `problems/cses/<problem>/<problem>.lambdalattice`,
  * which exports one function. The function is the one member of the file's
  * tuple read by projection off the tree whose visible subtree is Gezi's
  * directory (`StandardLibrary.entryMember`), read back to a closed
  * instruction that holds what its imports gave (the library's prelude and
  * binary naturals, and `problems/cses/common/binary_modular`) and no name
  * (a point carries the bodies, never the names, [[gezi.contest.corpora.reductions]]). Each read starts from the
  * URI expansions the owner carries (`ProblemFamilies.sharedExpansions`) and
  * is made once, when first used.
  */
final case class CsesProblems(root: Path, expansions: Expansions):

  /** The function the problem's file exports, as a closed instruction. */
  private def read(problem: String): Instruction =
    readFile(root.resolve("problems").resolve(CsesProblems.directory).resolve(problem).resolve(problem + DirectoryTree.fileExtension))

  /** The function the file exports, as a closed instruction. */
  private def readFile(file: Path): Instruction = StandardLibrary.entryMember(root, file, expansions)._1

  /** `dice_combinations n`. */
  lazy val diceCombinations: Instruction = read("dice_combinations")

  /** `minimizing_coins coins x`. */
  lazy val minimizingCoins: Instruction = read("minimizing_coins")

  /** `message_route n connections`. */
  lazy val messageRoute: Instruction = read("message_route")

  /** `counting_rooms map`. */
  lazy val countingRooms: Instruction = read("counting_rooms")

  /** `exponentiation a b`. */
  lazy val exponentiation: Instruction = read("exponentiation")

  // The second batch.

  /** `coin_combinations_ordered coins x`. */
  lazy val coinCombinationsOrdered: Instruction = read("coin_combinations_ordered")

  /** `coin_combinations_unordered coins x`. */
  lazy val coinCombinationsUnordered: Instruction = read("coin_combinations_unordered")

  /** `removing_digits n`. */
  lazy val removingDigits: Instruction = read("removing_digits")

  /** `grid_paths rows`. */
  lazy val gridPaths: Instruction = read("grid_paths")

  /** `book_shop books x`. */
  lazy val bookShop: Instruction = read("book_shop")

  /** `shortest_routes_single_source n flights`. */
  lazy val shortestRoutesSingleSource: Instruction = read("shortest_routes_single_source")

  /** `shortest_routes_queries n roads queries`. */
  lazy val shortestRoutesQueries: Instruction = read("shortest_routes_queries")

  /** `counting_divisors numbers`. */
  lazy val countingDivisors: Instruction = read("counting_divisors")

  /** `binomial_coefficients queries`. */
  lazy val binomialCoefficients: Instruction = read("binomial_coefficients")

  /** `distinct_numbers numbers`. */
  lazy val distinctNumbers: Instruction = read("distinct_numbers")

  // A problem built as the CSES problems are, outside problems/cses.

  /** `value steps root` of `problems/speculative_untabling/weighted_paths`
    * (`WeightedPaths`).
    */
  lazy val weightedPaths: Instruction =
    readFile(root.resolve("problems").resolve(WeightedPaths.directory).resolve(WeightedPaths.problem + DirectoryTree.fileExtension))

/** The directory of the problems under `problems`. */
object CsesProblems:

  val directory: String = "cses"

/** The CSES problems' data as the problem files' headers give their
  * encodings: the library's canonical binary naturals, Booleans and Scott
  * lists (`StandardLibraryNormalForms`), the prelude's pair `λp. p l r`
  * (`corpora/library/prelude/pair.lambdalattice`) and the Scott option of
  * `minimizing_coins` and `message_route`, none `λn s. n` and some k
  * `λn s. s k`. A site's data is a HOAS term whose atoms, each natural and
  * each Boolean, are closed instructions converted once (`Term.closed`), so
  * that a site costs its program's conversion a node for each atom and not
  * the nodes of the atom. MEASURED 2026-11-21 by a scratch probe in
  * contest-corpora's tests (CPUs 6, 7, 10 and 11 of contest.slice, nice 10,
  * a 2.5 GB test heap, the 1-minute load about 6): with each site's data
  * written whole as one de Bruijn term and converted, the 40,000
  * connections of a graph of 20,000 computers took 10.6 s to convert and a
  * graph of CSES's size ran the heap out; written as here, a site of
  * `MessageRoute`'s top rung (about 10^5 computers and 2 · 10^5
  * connections) took 7.4 s for its data (the naturals converted) and 7.6 s
  * for its program's conversion (`Reduction.programRoot`), and one of
  * `CountingRooms`' top rung (up to 10^6 squares) 1.0 s and 13.6 s.
  */
object CsesEncodings:

  /** The option none, `λn s. n`, a normal form. */
  val none: DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))

  /** The option some of the closed normal form, `λn s. s k`. */
  def some(value: DeBruijnTerm): DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value)))

  /** The closed normal form as a closed HOAS term, converted once. */
  def closed(term: DeBruijnTerm): Term = Term.closed(Defunctionalization.thunkInstruction(term))

  /** The binary natural of the value, converted once. */
  def natural(value: BigInt): Term = closed(StandardLibraryNormalForms.binary(value))

  /** The natural of each distinct value, each converted once. */
  def naturals(values: Vector[Int]): Map[Int, Term] = values.distinct.map(value => value -> natural(value)).toMap

  /** The Boolean true, converted once. */
  val trueValue: Term = closed(StandardLibraryNormalForms.boolean(true))

  /** The Boolean false, converted once. */
  val falseValue: Term = closed(StandardLibraryNormalForms.boolean(false))

  /** The pair `λp. p l r`. */
  def pair(left: Term, right: Term): Term = Term.λ(select => select(left)(right))

  /** The triple `pair a (pair b c)` of the shortest routes' flights and
    * roads, each end and the cost a natural of `naturals`.
    */
  def triple(naturals: Map[Int, Term], from: Int, to: Int, cost: Int): Term =
    pair(naturals(from), pair(naturals(to), naturals(cost)))

  /** `[f a11 … a1k, …, f aR1 … aRk]`, the function let bound once,
    * `(λf. …) Function`, and applied at each site to that site's
    * arguments, the results in the library's Scott list.
    */
  def sites(function: Term, arguments: Vector[Vector[Term]]): Term =
    Term.λ(bound => list(arguments.map(Encodings.applied(bound, _))))(function)

  /** The empty list `λn c. n`, converted once. It is the term `trueValue`
    * is, and as one more atom it is one instruction with it: with `nil`
    * written inline, the list `[true]` held the closed term `λx y. x` as two
    * instructions, the atom and the inline `nil`, which the front end
    * spells as one (`Defunctionalization.thunkInstruction` of the readback),
    * so its exchange line read back as another instruction or, when the
    * printer's sharing differed, was refused as another spelling
    * (`ExchangeText.term`): measured 2026-11-21 on bb6ba0942 by a scratch
    * probe in contest-judge's tests, of the 48 repeated programs of
    * `CountingRooms`' two lower rungs (both twins, the seeds 0, 1, 2 and
    * 20261031, R = 1 to 3) 16 read back as another instruction and 24 were
    * refused, while every program of the other four problems read back as
    * itself. With `nil` an atom, none of the 48 differs.
    */
  val nilValue: Term = closed(StandardLibraryNormalForms.list(Vector.empty))

  /** The library's Scott list of the terms, `nil` `λn c. n` (`nilValue`)
    * and `cons h t` `λn c. c h t`, written as its cells with no library
    * term.
    */
  def list(elements: Vector[Term]): Term =
    elements.foldRight(nilValue)((head, tail) => Term.λ(_ => Term.λ(cell => cell(head)(tail))))

/** How the function of a CSES point is written ([[gezi.contest.corpora.reductions]]): directly,
  * as the problem's file gives it, or respelled, so that a compiler cannot
  * recognise the library by the spelling of its bodies. The program is a
  * pure λ term with top, with no label of its own to rename and no choice to
  * shuffle, so the respelling is β-expansion: at each node drawn, one in
  * four, the subterm M is written `(λx. x) M` or `(λx y. x) M (λz. z)`,
  * each drawn with even odds, both β-equal to M (⊢_β), so the respelled
  * program and the direct one have the same answers by Definition 14
  * (`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`). No
  * subterm is shifted, since M stays outside the binders added. The
  * literals are kept as they are: top, the bits `λt f. t` and `λt f. f` a
  * literal's variable arguments are, and each level `λx. x R top` or
  * `λx. x top R` of a variable arguments partial function, under which R is
  * respelled, and the application spine of such a function applied to the
  * bits of its literal (`literalApplication`), so that a literal stays a
  * literal (`Literals`), a program stays pure by `ProgramPurity` as its
  * direct spelling is, and the
  * snapshots write it as one: with every node respelled, the text of the
  * respelled program of minimizing_coins' bottom rung was 510,811 bytes
  * against the direct one's 6,763, its literals written out bit by bit
  * (2026-11-21). Each distinct subterm is respelled once: the terms are
  * interned, so a subterm met again takes the respelling drawn where it was
  * first met, and the work is linear in the term as a graph.
  */
object CsesSpelling:

  /** The term respelled by the draws, and the draws after it. */
  def respelled(term: DeBruijnTerm, draws: Draws): (DeBruijnTerm, Draws) =
    val (result, after, _) = walked(term, draws, Map.empty).result
    (result, after)

  private type Walked = TailRec[(DeBruijnTerm, Draws, Map[DeBruijnTerm, DeBruijnTerm])]

  /** `λx. x`. */
  private val identityTerm: DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** `λx y. x`. */
  private val constantTerm: DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))

  private def walked(term: DeBruijnTerm, draws: Draws, memo: Map[DeBruijnTerm, DeBruijnTerm]): Walked =
    memo.get(term) match
      case Some(found)          => done((found, draws, memo))
      case None if literal(term) => done((term, draws, memo))
      case None =>
        tailcall(walkedAnew(term, draws, memo)).map((inner, afterInner, afterMemo) =>
          val (wrapped, afterWrap) =
            if level(term) then (inner, afterInner)
            else if literalApplication(term) then (inner, expanded(inner, afterInner)._2)
            else expanded(inner, afterInner)
          (wrapped, afterWrap, afterMemo.updated(term, wrapped))
        )

  /** Whether the term is a variable arguments partial function applied to
    * bits of its literal, `P b1 … bk` with k ≥ 1, each argument of the
    * application spine the bit the level before it expects (`λx. x R top`
    * the bit 1, `λx. x top R` the bit 0). No node of such a spine is
    * β-expanded, so the spine stays whole: a reader that contracts the
    * literal one bit at a time along the spine (`ProgramPurity`) no longer
    * sees it as one once a prefix `P b1 … bj` is written
    * `(λx. x) (P b1 … bj)`. Each node still takes its draw, so that every
    * other node draws the expansion it drew before the spine was kept whole.
    * Before, all five functions' respelled twins read as impure by
    * `ProgramPurity`, the tops of the marker `(λ"$generic". λv. v) "$generic"`
    * looked at (scratch probe, 2026-11-21).
    */
  private def literalApplication(term: DeBruijnTerm): Boolean = term match
    case DeBruijnTerm.Apply(_, _) =>
      val (head, arguments) = gezi.ir.Spine.of(term)
      @scala.annotation.tailrec
      def consumed(current: DeBruijnTerm, remaining: List[DeBruijnTerm]): Boolean = (current, remaining) match
        case (_, Nil) => true
        case (DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), matched), missed)), bit :: rest)
            if missed == Literals.top && bit == bitOne =>
          consumed(matched, rest)
        case (DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), missed), matched)), bit :: rest)
            if missed == Literals.top && bit == bitZero =>
          consumed(matched, rest)
        case _ => false
      consumed(head, arguments.toList)
    case _ => false

  /** The bit 1 of a literal's variable arguments, `λt f. t`. */
  private val bitOne: DeBruijnTerm = StandardLibraryNormalForms.boolean(true)

  /** The bit 0 of a literal's variable arguments, `λt f. f`. */
  private val bitZero: DeBruijnTerm = StandardLibraryNormalForms.boolean(false)

  /** The subterm, β-expanded at one draw in four. */
  private def expanded(term: DeBruijnTerm, draws: Draws): (DeBruijnTerm, Draws) =
    val (shape, after) = draws.number(0 to 7)
    shape match
      case 0 => (DeBruijnTerm.Apply(identityTerm, term), after)
      case 1 => (DeBruijnTerm.Apply(DeBruijnTerm.Apply(constantTerm, term), identityTerm), after)
      case _ => (term, after)

  private def pair(
      left: DeBruijnTerm,
      right: DeBruijnTerm,
      draws: Draws,
      memo: Map[DeBruijnTerm, DeBruijnTerm],
      make: (DeBruijnTerm, DeBruijnTerm) => DeBruijnTerm
  ): Walked =
    for
      (walkedLeft, afterLeft, leftMemo) <- tailcall(walked(left, draws, memo))
      (walkedRight, afterRight, rightMemo) <- tailcall(walked(right, afterLeft, leftMemo))
    yield (make(walkedLeft, walkedRight), afterRight, rightMemo)

  /** The bits of a literal's variable arguments. */
  private val bits: Set[DeBruijnTerm] = Set(StandardLibraryNormalForms.boolean(true), StandardLibraryNormalForms.boolean(false))

  /** A literal's part, kept as it is: top or a bit. */
  private def literal(term: DeBruijnTerm): Boolean = term == Literals.top || bits.contains(term)

  /** A level of a variable arguments partial function, `λx. x R top` or
    * `λx. x top R`, never β-expanded itself.
    */
  private def level(term: DeBruijnTerm): Boolean = term match
    case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne), whenZero)) =>
      (whenOne == Literals.top) != (whenZero == Literals.top)
    case _ => false

  private def walkedAnew(term: DeBruijnTerm, draws: Draws, memo: Map[DeBruijnTerm, DeBruijnTerm]): Walked = term match
    case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne), whenZero))
        if whenZero == Literals.top && whenOne != Literals.top =>
      tailcall(walked(whenOne, draws, memo)).map((walkedOne, after, afterMemo) =>
        (DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), walkedOne), whenZero)), after, afterMemo)
      )
    case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne), whenZero))
        if whenOne == Literals.top && whenZero != Literals.top =>
      tailcall(walked(whenZero, draws, memo)).map((walkedZero, after, afterMemo) =>
        (DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne), walkedZero)), after, afterMemo)
      )
    case DeBruijnTerm.Lambda(body) =>
      tailcall(walked(body, draws, memo)).map((walkedBody, after, afterMemo) => (DeBruijnTerm.Lambda(walkedBody), after, afterMemo))
    case DeBruijnTerm.Apply(function, argument) => pair(function, argument, draws, memo, DeBruijnTerm.Apply(_, _))
    case DeBruijnTerm.Choice(left, right)       => pair(left, right, draws, memo, DeBruijnTerm.Choice(_, _))
    case DeBruijnTerm.Parallel(left, right)     => pair(left, right, draws, memo, DeBruijnTerm.Parallel(_, _))
    case other                                  => done((other, draws, memo))

  /** The closed instruction in the spelling as a closed HOAS term,
    * respelled from the draws when respelled, and the draws after it.
    */
  def spelled(instruction: Instruction, spelling: Spelling, draws: Draws): (Term, Draws) = spelling match
    case Spelling.Direct => (Term.closed(instruction), draws)
    case Spelling.Respelled =>
      val (respelledTerm, after) = respelled(Defunctionalization.instructionTerm(instruction), draws)
      (CsesEncodings.closed(respelledTerm), after)
