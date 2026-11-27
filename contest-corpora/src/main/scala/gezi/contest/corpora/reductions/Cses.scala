package gezi.contest.corpora.reductions

import java.nio.file.Path
import gezi.directorysugar.DirectoryTree
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Literals
import gezi.frontend.Term
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** The corpora are read under no facts. */
private given csesNoFacts: NoFacts.type = NoFacts

/** The functions of `problems/cses`, the port of the CSES Problem Set, that the
  * CSES families (`CsesFamilies.scala`) apply to their drawn inputs, and of the
  * problems outside it built as CSES families are
  * (`SpeculativeUntabling.scala`).
  *
  * Each problem is the file `problems/cses/<problem>/<problem>.lambdalattice`,
  * which exports one function. The function is the one member of the file's
  * tuple read by projection off the tree whose visible subtree is Gezi's
  * directory (`StandardLibrary.entryMember`), read back to a closed instruction
  * that holds what its imports gave (the library's prelude and binary naturals,
  * and `problems/cses/common/binary_modular`) and no name (a point carries the
  * bodies, never the names, [[gezi.contest.corpora.reductions]]). Each read
  * starts from the URI expansions the owner carries
  * (`ProblemFamilies.sharedExpansions`) and is made once, when first used.
  */
final case class CsesProblems(
    root: Path,
    expansions: Expansions[gezi.ir.NoFacts.type]
):

  /** The function the problem's file exports, as a closed instruction. */
  private def read(problem: String): Configured[NoFacts.type] =
    readFile(
      root
        .resolve("problems")
        .resolve(CsesProblems.directory)
        .resolve(problem)
        .resolve(problem + DirectoryTree.fileExtension)
    )

  /** The function the file exports, as a closed instruction. */
  private def readFile(file: Path): Configured[NoFacts.type] =
    StandardLibrary.entryMember(root, file, expansions)._1

  /** `dice_combinations n`. */
  lazy val diceCombinations: Configured[NoFacts.type] = read(
    "dice_combinations"
  )

  /** `minimizing_coins coins x`. */
  lazy val minimizingCoins: Configured[NoFacts.type] = read("minimizing_coins")

  /** `message_route n connections`. */
  lazy val messageRoute: Configured[NoFacts.type] = read("message_route")

  /** `counting_rooms map`. */
  lazy val countingRooms: Configured[NoFacts.type] = read("counting_rooms")

  /** `exponentiation a b`. */
  lazy val exponentiation: Configured[NoFacts.type] = read("exponentiation")

  // The second batch.

  /** `coin_combinations_ordered coins x`. */
  lazy val coinCombinationsOrdered: Configured[NoFacts.type] = read(
    "coin_combinations_ordered"
  )

  /** `coin_combinations_unordered coins x`. */
  lazy val coinCombinationsUnordered: Configured[NoFacts.type] = read(
    "coin_combinations_unordered"
  )

  /** `removing_digits n`. */
  lazy val removingDigits: Configured[NoFacts.type] = read("removing_digits")

  /** `grid_paths rows`. */
  lazy val gridPaths: Configured[NoFacts.type] = read("grid_paths")

  /** `book_shop books x`. */
  lazy val bookShop: Configured[NoFacts.type] = read("book_shop")

  /** `shortest_routes_single_source n flights`. */
  lazy val shortestRoutesSingleSource: Configured[NoFacts.type] = read(
    "shortest_routes_single_source"
  )

  /** `shortest_routes_queries n roads queries`. */
  lazy val shortestRoutesQueries: Configured[NoFacts.type] = read(
    "shortest_routes_queries"
  )

  /** `counting_divisors numbers`. */
  lazy val countingDivisors: Configured[NoFacts.type] = read(
    "counting_divisors"
  )

  /** `binomial_coefficients queries`. */
  lazy val binomialCoefficients: Configured[NoFacts.type] = read(
    "binomial_coefficients"
  )

  /** `distinct_numbers numbers`. */
  lazy val distinctNumbers: Configured[NoFacts.type] = read("distinct_numbers")

  // The third batch.

  /** `money_sums coins`. */
  lazy val moneySums: Configured[NoFacts.type] = read("money_sums")

  /** `rectangle_cutting a b`. */
  lazy val rectangleCutting: Configured[NoFacts.type] = read(
    "rectangle_cutting"
  )

  /** `increasing_subsequence numbers`. */
  lazy val increasingSubsequence: Configured[NoFacts.type] = read(
    "increasing_subsequence"
  )

  /** `array_description m entries`. */
  lazy val arrayDescription: Configured[NoFacts.type] = read(
    "array_description"
  )

  /** `building_roads n roads`. */
  lazy val buildingRoads: Configured[NoFacts.type] = read("building_roads")

  /** `road_reparation n roads`. */
  lazy val roadReparation: Configured[NoFacts.type] = read("road_reparation")

  /** `game_routes n flights`. */
  lazy val gameRoutes: Configured[NoFacts.type] = read("game_routes")

  /** `static_range_sums values queries`. */
  lazy val staticRangeSums: Configured[NoFacts.type] = read("static_range_sums")

  /** `trailing_zeros n`. */
  lazy val trailingZeros: Configured[NoFacts.type] = read("trailing_zeros")

  /** `sum_of_divisors n`. */
  lazy val sumOfDivisors: Configured[NoFacts.type] = read("sum_of_divisors")

  // The generators of the seeded top rungs.

  /** The members of `problems/cses/common/seeded_input`, in the order its
    * export gives them: `next_state`, `seeded_numbers`, `seeded_pairs`,
    * `seeded_triples`, `seeded_grid`, `trapped_first`, `trapped_last`,
    * `seeded_connections`, `seeded_tree`, `seeded_binomial_queries`
    * (`SeededInput` generates the same data natively).
    */
  lazy val seededInput: Vector[Configured[NoFacts.type]] =
    StandardLibrary
      .entryFields(
        root,
        root
          .resolve("problems")
          .resolve(CsesProblems.directory)
          .resolve("common")
          .resolve("seeded_input" + DirectoryTree.fileExtension),
        expansions,
        CsesProblems.seededInputArity
      )
      ._1

  /** `seeded_numbers seed count low high`. */
  lazy val seededNumbers: Configured[NoFacts.type] = seededInput(1)

  /** `seeded_pairs seed count low high`. */
  lazy val seededPairs: Configured[NoFacts.type] = seededInput(2)

  /** `seeded_triples seed count low high cost_low cost_high`. */
  lazy val seededTriples: Configured[NoFacts.type] = seededInput(3)

  /** `seeded_grid seed rows columns odds`. */
  lazy val seededGrid: Configured[NoFacts.type] = seededInput(4)

  /** `trapped_first grid`. */
  lazy val trappedFirst: Configured[NoFacts.type] = seededInput(5)

  /** `trapped_last grid`. */
  lazy val trappedLast: Configured[NoFacts.type] = seededInput(6)

  /** `seeded_connections seed count n`. */
  lazy val seededConnections: Configured[NoFacts.type] = seededInput(7)

  /** `seeded_tree seed n cost_low cost_high`. */
  lazy val seededTree: Configured[NoFacts.type] = seededInput(8)

  /** `seeded_binomial_queries seed count high`. */
  lazy val seededBinomialQueries: Configured[NoFacts.type] = seededInput(9)

  /** The members of `problems/cses/common/seeded_shapes`, in the order its
    * export gives them: `seeded_ranges`, `seeded_ordered_connections`,
    * `seeded_tree_edges`, `seeded_walk`, `seeded_rotation` (`SeededInput`
    * generates the same data natively).
    */
  lazy val seededShapes: Vector[Configured[NoFacts.type]] =
    StandardLibrary
      .entryFields(
        root,
        root
          .resolve("problems")
          .resolve(CsesProblems.directory)
          .resolve("common")
          .resolve("seeded_shapes" + DirectoryTree.fileExtension),
        expansions,
        CsesProblems.seededShapesArity
      )
      ._1

  /** `seeded_ranges seed count low high`. */
  lazy val seededRanges: Configured[NoFacts.type] = seededShapes(0)

  /** `seeded_ordered_connections seed count n`. */
  lazy val seededOrderedConnections: Configured[NoFacts.type] = seededShapes(1)

  /** `seeded_tree_edges seed n`. */
  lazy val seededTreeEdges: Configured[NoFacts.type] = seededShapes(2)

  /** `seeded_walk seed count bound`. */
  lazy val seededWalk: Configured[NoFacts.type] = seededShapes(3)

  /** `seeded_rotation seed n`. */
  lazy val seededRotation: Configured[NoFacts.type] = seededShapes(4)

  /** `append left right` of the prelude's lists,
    * `corpora/library/prelude/list`, whose export is
    * `nil cons append map length`.
    */
  lazy val append: Configured[NoFacts.type] =
    StandardLibrary
      .entryFields(
        root,
        root
          .resolve("corpora")
          .resolve("library")
          .resolve("prelude")
          .resolve("list" + DirectoryTree.fileExtension),
        expansions,
        5
      )
      ._1(2)

  // The fourth batch.

  /** `exponentiation_two a b c`. */
  lazy val exponentiationTwo: Configured[NoFacts.type] = read(
    "exponentiation_two"
  )

  /** `ferris_wheel x weights`. */
  lazy val ferrisWheel: Configured[NoFacts.type] = read("ferris_wheel")

  /** `missing_number n numbers`. */
  lazy val missingNumber: Configured[NoFacts.type] = read("missing_number")

  /** `repetitions letters`. */
  lazy val repetitions: Configured[NoFacts.type] = read("repetitions")

  /** `static_range_minimums values queries`. */
  lazy val staticRangeMinimums: Configured[NoFacts.type] = read(
    "static_range_minimums"
  )

  /** `string_matching text pattern`. */
  lazy val stringMatching: Configured[NoFacts.type] = read("string_matching")

  /** `subarray_sums x values`. */
  lazy val subarraySums: Configured[NoFacts.type] = read("subarray_sums")

  /** `sum_of_two_values x values`. */
  lazy val sumOfTwoValues: Configured[NoFacts.type] = read("sum_of_two_values")

  /** `tree_diameter n edges`. */
  lazy val treeDiameter: Configured[NoFacts.type] = read("tree_diameter")

  /** `tree_matching n edges`. */
  lazy val treeMatching: Configured[NoFacts.type] = read("tree_matching")

  // A problem built as the CSES problems are, outside problems/cses.

  /** `value steps root` of `problems/speculative_untabling/weighted_paths`
    * (`WeightedPaths`).
    */
  lazy val weightedPaths: Configured[NoFacts.type] =
    readFile(
      root
        .resolve("problems")
        .resolve(WeightedPaths.directory)
        .resolve(WeightedPaths.problem + DirectoryTree.fileExtension)
    )

/** The directory of the problems under `problems`. */
object CsesProblems:

  val directory: String = "cses"

  /** The number of members `problems/cses/common/seeded_input` exports. */
  val seededInputArity: Int = 10

  /** The number of members `problems/cses/common/seeded_shapes` exports. */
  val seededShapesArity: Int = 5

/** The CSES problems' data as the problem files' headers give their encodings:
  * the library's canonical binary naturals, Booleans and Scott lists
  * (`StandardLibraryNormalForms`), the prelude's pair `λp. p l r`
  * (`corpora/library/prelude/pair.lambdalattice`) and the Scott option of
  * `minimizing_coins` and `message_route`, none `λn s. n` and some k
  * `λn s. s k`. A site's data is a HOAS term whose atoms, each natural and each
  * Boolean, are closed instructions converted once (`Term.closed`), so that a
  * site costs its program's conversion a node for each atom and not the nodes
  * of the atom. MEASURED 2026-11-21 by a scratch probe in contest-corpora's
  * tests (CPUs 6, 7, 10 and 11 of contest.slice, nice 10, a 2.5 GB test heap,
  * the 1-minute load about 6): with each site's data written whole as one de
  * Bruijn term and converted, the 40,000 connections of a graph of 20,000
  * computers took 10.6 s to convert and a graph of CSES's size ran the heap
  * out; written as here, a site of `MessageRoute`'s top rung (about 10^5
  * computers and 2 · 10^5 connections) took 7.4 s for its data (the naturals
  * converted) and 7.6 s for its program's conversion (`Reduction.programRoot`),
  * and one of `CountingRooms`' top rung (up to 10^6 squares) 1.0 s and 13.6 s.
  */
object CsesEncodings:

  /** The option none, `λn s. n`, a normal form. */
  val none: DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))

  /** The option some of the closed normal form, `λn s. s k`. */
  def some(value: DeBruijnTerm): DeBruijnTerm = DeBruijnTerm.Lambda(
    DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value))
  )

  /** The closed normal form as a closed HOAS term, converted once. */
  def closed(term: ProblemDeBruijnTerm): ProblemTerm = Term.closed(
    Defunctionalization.thunkInstruction(term)(using gezi.ir.NoFacts)
  )

  /** The binary natural of the value, converted once. */
  def natural(value: BigInt): ProblemTerm = closed(
    StandardLibraryNormalForms.binary(value)
  )

  /** The natural of each distinct value, each converted once. */
  def naturals(values: Vector[Int]): Map[Int, ProblemTerm] =
    values.distinct.map(value => value -> natural(value)).toMap

  /** The Boolean true, converted once. */
  val trueValue: ProblemTerm = closed(StandardLibraryNormalForms.boolean(true))

  /** The Boolean false, converted once. */
  val falseValue: ProblemTerm = closed(
    StandardLibraryNormalForms.boolean(false)
  )

  /** The pair `λp. p l r`. */
  def pair(left: ProblemTerm, right: ProblemTerm): ProblemTerm =
    Term.λ(select => select(left)(right))

  /** The triple `pair a (pair b c)` of the shortest routes' flights and roads,
    * each end and the cost a natural of `naturals`.
    */
  def triple(
      naturals: Map[Int, ProblemTerm],
      from: Int,
      to: Int,
      cost: Int
  ): ProblemTerm =
    pair(naturals(from), pair(naturals(to), naturals(cost)))

  /** `[f a11 … a1k, …, f aR1 … aRk]`, the function let bound once,
    * `(λf. …) Function`, and applied at each site to that site's arguments, the
    * results in the library's Scott list.
    */
  def sites(
      function: ProblemTerm,
      arguments: Vector[Vector[ProblemTerm]]
  ): ProblemTerm =
    Term.λ(bound => list(arguments.map(Encodings.applied(bound, _))))(function)

  /** The empty list `λn c. n`, converted once. It is the term `trueValue` is,
    * and as one more atom it is one instruction with it: with `nil` written
    * inline, the list `[true]` held the closed term `λx y. x` as two
    * instructions, the atom and the inline `nil`, which the front end spells as
    * one (`Defunctionalization.thunkInstruction` of the readback), so its
    * exchange line read back as another instruction or, when the printer's
    * sharing differed, was refused as another spelling (`ExchangeText.term`):
    * measured 2026-11-21 on bb6ba0942 by a scratch probe in contest-judge's
    * tests, of the 48 repeated programs of `CountingRooms`' two lower rungs
    * (both twins, the seeds 0, 1, 2 and 20261031, R = 1 to 3) 16 read back as
    * another instruction and 24 were refused, while every program of the other
    * four problems read back as itself. With `nil` an atom, none of the 48
    * differs.
    */
  val nilValue: ProblemTerm = closed(
    StandardLibraryNormalForms.list(Vector.empty)
  )

  /** The library's Scott list of the terms, `nil` `λn c. n` (`nilValue`) and
    * `cons h t` `λn c. c h t`, written as its cells with no library term.
    */
  def list(elements: Vector[ProblemTerm]): ProblemTerm =
    elements.foldRight(nilValue)((head, tail) =>
      Term.λ(_ => Term.λ(cell => cell(head)(tail)))
    )

/** How the function of a CSES point is written
  * ([[gezi.contest.corpora.reductions]]): directly, as the problem's file gives
  * it, or respelled, so that a compiler cannot recognise the library by the
  * spelling of its bodies. The program is a pure λ term with top, with no label
  * of its own to rename and no choice to shuffle, so the respelling is
  * β-expansion: at each node drawn, one in four, the subterm M is written
  * `(λx. x) M` or `(λx y. x) M (λz. z)`, each drawn with even odds, both
  * β-equal to M (⊢_β), so the respelled program and the direct one have the
  * same answers by Definition 14
  * (`ContextualPreorder.contextualEquivalenceOfDerivableLatticeEta`). No
  * subterm is shifted, since M stays outside the binders added. The literals
  * are kept as they are: top, the bits `λt f. t` and `λt f. f` a literal's
  * variable arguments are, and each level `λx. x R top` or `λx. x top R` of a
  * variable arguments partial function, under which R is respelled, and the
  * application spine of such a function applied to the bits of its literal
  * (`literalApplication`), so that a literal stays a literal (`Literals`), a
  * program stays pure by `ProgramPurity` as its direct spelling is, and the
  * snapshots write it as one: with every node respelled, the text of the
  * respelled program of minimizing_coins' bottom rung was 510,811 bytes against
  * the direct one's 6,763, its literals written out bit by bit (2026-11-21).
  * Each distinct subterm is respelled once: the terms are interned, so a
  * subterm met again takes the respelling drawn where it was first met, and the
  * work is linear in the term as a graph.
  */
object CsesSpelling:

  /** The term respelled by the draws, and the draws after it. */
  def respelled(
      term: ProblemDeBruijnTerm,
      draws: Draws
  ): (ProblemDeBruijnTerm, Draws) =
    val (result, after, _) = walked(term, draws, Map.empty).result
    (result, after)

  private type Walked = TailRec[
    (ProblemDeBruijnTerm, Draws, Map[ProblemDeBruijnTerm, ProblemDeBruijnTerm])
  ]

  /** `λx. x`. */
  private val identityTerm: ProblemDeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** `λx y. x`. */
  private val constantTerm: ProblemDeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))

  private def walked(
      term: ProblemDeBruijnTerm,
      draws: Draws,
      memo: Map[ProblemDeBruijnTerm, ProblemDeBruijnTerm]
  ): Walked =
    memo.get(term) match
      case Some(found)           => done((found, draws, memo))
      case None if literal(term) => done((term, draws, memo))
      case None                  =>
        tailcall(walkedAnew(term, draws, memo)).map(
          (inner, afterInner, afterMemo) =>
            val (wrapped, afterWrap) =
              if level(term) then (inner, afterInner)
              else if literalApplication(term) then
                (inner, expanded(inner, afterInner)._2)
              else expanded(inner, afterInner)
            (wrapped, afterWrap, afterMemo.updated(term, wrapped))
        )

  /** Whether the term is a variable arguments partial function applied to bits
    * of its literal, `P b1 … bk` with k ≥ 1, each argument of the application
    * spine the bit the level before it expects (`λx. x R top` the bit 1,
    * `λx. x top R` the bit 0). No node of such a spine is β-expanded, so the
    * spine stays whole: a reader that contracts the literal one bit at a time
    * along the spine (`ProgramPurity`) no longer sees it as one once a prefix
    * `P b1 … bj` is written `(λx. x) (P b1 … bj)`. Each node still takes its
    * draw, so that every other node draws the expansion it drew before the
    * spine was kept whole. Before, all five functions' respelled twins read as
    * impure by `ProgramPurity`, the tops of the marker
    * `(λ"$generic". λv. v) "$generic"` looked at (scratch probe, 2026-11-21).
    */
  private def literalApplication(term: ProblemDeBruijnTerm): Boolean =
    term match
      case DeBruijnTerm.Apply(_, _) =>
        val (head, arguments) = gezi.ir.Spine.of(term)
        @scala.annotation.tailrec
        def consumed(
            current: ProblemDeBruijnTerm,
            remaining: List[ProblemDeBruijnTerm]
        ): Boolean = (current, remaining) match
          case (_, Nil) => true
          case (
                DeBruijnTerm.Lambda(
                  DeBruijnTerm.Apply(
                    DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), matched),
                    missed
                  )
                ),
                bit :: rest
              ) if missed == Literals.top && bit == bitOne =>
            consumed(matched, rest)
          case (
                DeBruijnTerm.Lambda(
                  DeBruijnTerm.Apply(
                    DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), missed),
                    matched
                  )
                ),
                bit :: rest
              ) if missed == Literals.top && bit == bitZero =>
            consumed(matched, rest)
          case _ => false
        consumed(head, arguments.toList)
      case _ => false

  /** The bit 1 of a literal's variable arguments, `λt f. t`. */
  private val bitOne: ProblemDeBruijnTerm =
    StandardLibraryNormalForms.boolean(true)

  /** The bit 0 of a literal's variable arguments, `λt f. f`. */
  private val bitZero: ProblemDeBruijnTerm =
    StandardLibraryNormalForms.boolean(false)

  /** The subterm, β-expanded at one draw in four. */
  private def expanded(
      term: ProblemDeBruijnTerm,
      draws: Draws
  ): (ProblemDeBruijnTerm, Draws) =
    val (shape, after) = draws.number(0 to 7)
    shape match
      case 0 => (DeBruijnTerm.Apply(identityTerm, term), after)
      case 1 =>
        (
          DeBruijnTerm.Apply(
            DeBruijnTerm.Apply(constantTerm, term),
            identityTerm
          ),
          after
        )
      case _ => (term, after)

  private def pair(
      left: ProblemDeBruijnTerm,
      right: ProblemDeBruijnTerm,
      draws: Draws,
      memo: Map[ProblemDeBruijnTerm, ProblemDeBruijnTerm],
      make: (ProblemDeBruijnTerm, ProblemDeBruijnTerm) => ProblemDeBruijnTerm
  ): Walked =
    for
      (walkedLeft, afterLeft, leftMemo) <- tailcall(walked(left, draws, memo))
      (walkedRight, afterRight, rightMemo) <- tailcall(
        walked(right, afterLeft, leftMemo)
      )
    yield (make(walkedLeft, walkedRight), afterRight, rightMemo)

  /** The bits of a literal's variable arguments. */
  private val bits: Set[ProblemDeBruijnTerm] = Set(
    StandardLibraryNormalForms.boolean(true),
    StandardLibraryNormalForms.boolean(false)
  )

  /** A literal's part, kept as it is: top or a bit. */
  private def literal(term: ProblemDeBruijnTerm): Boolean =
    term == Literals.top || bits.contains(term)

  /** A level of a variable arguments partial function, `λx. x R top` or
    * `λx. x top R`, never β-expanded itself.
    */
  private def level(term: ProblemDeBruijnTerm): Boolean = term match
    case DeBruijnTerm.Lambda(
          DeBruijnTerm.Apply(
            DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne),
            whenZero
          )
        ) =>
      (whenOne == Literals.top) != (whenZero == Literals.top)
    case _ => false

  private def walkedAnew(
      term: ProblemDeBruijnTerm,
      draws: Draws,
      memo: Map[ProblemDeBruijnTerm, ProblemDeBruijnTerm]
  ): Walked = term match
    case DeBruijnTerm.Lambda(
          DeBruijnTerm.Apply(
            DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne),
            whenZero
          )
        ) if whenZero == Literals.top && whenOne != Literals.top =>
      tailcall(walked(whenOne, draws, memo)).map(
        (walkedOne, after, afterMemo) =>
          (
            DeBruijnTerm.Lambda(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), walkedOne),
                whenZero
              )
            ),
            after,
            afterMemo
          )
      )
    case DeBruijnTerm.Lambda(
          DeBruijnTerm.Apply(
            DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne),
            whenZero
          )
        ) if whenOne == Literals.top && whenZero != Literals.top =>
      tailcall(walked(whenZero, draws, memo)).map(
        (walkedZero, after, afterMemo) =>
          (
            DeBruijnTerm.Lambda(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne),
                walkedZero
              )
            ),
            after,
            afterMemo
          )
      )
    case DeBruijnTerm.Lambda(body) =>
      tailcall(walked(body, draws, memo)).map((walkedBody, after, afterMemo) =>
        (DeBruijnTerm.Lambda(walkedBody), after, afterMemo)
      )
    case DeBruijnTerm.Apply(function, argument) =>
      pair(function, argument, draws, memo, DeBruijnTerm.Apply(_, _))
    case DeBruijnTerm.Choice(left, right) =>
      pair(left, right, draws, memo, DeBruijnTerm.Choice(_, _))
    case DeBruijnTerm.Parallel(left, right) =>
      pair(left, right, draws, memo, DeBruijnTerm.Parallel(_, _))
    case other => done((other, draws, memo))

  /** The closed instruction in the spelling as a closed HOAS term, respelled
    * from the draws when respelled, and the draws after it.
    */
  def spelled(
      instruction: Configured[NoFacts.type],
      spelling: Spelling,
      draws: Draws
  ): (ProblemTerm, Draws) = spelling match
    case Spelling.Direct    => (Term.closed(instruction), draws)
    case Spelling.Respelled =>
      val (respelledTerm, after) =
        respelled(Defunctionalization.instructionTerm(instruction), draws)
      (CsesEncodings.closed(respelledTerm), after)
