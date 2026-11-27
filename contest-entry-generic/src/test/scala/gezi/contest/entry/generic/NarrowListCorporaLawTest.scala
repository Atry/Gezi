package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import java.nio.file.Paths
import gezi.generatedinputs.GeneratedProperties
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.saturation.StopSignal
import gezi.jit.BackendChecks
import gezi.jit.NativesProvider
import gezi.narrowblocks.lists.NarrowBlockCompilation
import gezi.narrowblocks.DebugAttributes
import gezi.narrowblocks.lists.NarrowBlocks
import gezi.narrowblocks.lists.NarrowList
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Computed
import gezi.weakhead.Expansions
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState

private given narrowListCorporaLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the narrow lists' representation on the real library: the backend facts of the corpora's knowledge files that bind the
  * list family and the binary naturals (`tests/library_fixtures/narrow_lists`),
  * and lists built of the corpora's `nil` and `cons`
  * (`corpora/library/native_types/list`), each written under its constructor
  * marker, of canonical binary naturals of the corpora's `binary` library. A
  * list filtered at its root by `list_type (binary_set p)`, and at any of its
  * tails, decodes to the narrow list of its elements exactly when every filter
  * admits the elements from its place on; a list with no filter at its root
  * decodes to none. A fold of a list's elements by the library's
  * `merge_binary_plus`, and a recursion over two lists that walks the first
  * carrying the second and then folds it, written with the list branch's
  * filters, are each their program's one block, and the natural each block
  * computes reads as the program itself reads under tabling(weak_head) with
  * its parallels met head by head (`ParallelReading.HeadsMet`;
  * under `BothSides` that reading exhausted its tables after 108,271 steps
  * for a one-element fold and did not finish two lists within 30,000,000
  * steps, measured 2026-11-21). Their purpose is to catch a decoder that matches the
  * stand-in library of the narrow blocks' own tests (`NarrowListLibrary`) and
  * not the real one, whose constructors are marked, a list decoded with no
  * filter written in the term (the host decodes a value only where its term
  * carries an assertion), and
  * a list branch or a native call that computes another natural than the
  * library's definitions on the real library.
  */
class NarrowListCorporaLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The narrow check of the fixture's library, compiled and checked
    * against the natives.
    */
  private lazy val compilation =
    val natives = NativesProvider.loaded
    val library = StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/narrow_lists.lambdalattice"),
      Vector(BackendChecks(natives))
    )
    NarrowBlockCompilation(library.index, natives, gezi.weakhead.ReadingConfiguration.withoutFacts)

  /** The members of the JIT tests' library terms (`TermTables.jitLibraryTerms`). */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary.entryMembers(buildRoot, TermTables.jitLibraryTerms, Expansions.none)._1

  private def term(name: String): Configured[NoFacts.type] =
    terms.getOrElse(name, throw IllegalArgumentException(s"${TermTables.jitLibraryTerms.file} has no member $name"))

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => compilation, _ => terms, _ => plus)

  /** The canonical binary numeral of the value, of the library's
    * binary_zero, binary_even and binary_odd.
    */
  private def numeral(value: Int): Configured[NoFacts.type] =
    if value == 0 then term("binary_zero")
    else NoFacts.application(term(if (value & 1) == 1 then "binary_odd" else "binary_even"), numeral(value >> 1))

  /** `list_type (binary_set p)`, p true when the filter admits zero. */
  private def listCriterion(admitsZero: Boolean): Configured[NoFacts.type] =
    NoFacts.application(term("list_type"), NoFacts.application(term("binary_set"), term(if admitsZero then "true" else "false")))

  /** The list of the elements, each tail at whose place `filters` holds an
    * entry filtered by that entry's criterion, the root's at place 0.
    */
  private def list(elements: Vector[Int], filters: Map[Int, Boolean]): Configured[NoFacts.type] =
    elements.indices.foldRight(filtered(term("nil"), elements.size, filters))((place, rest) =>
      filtered(NoFacts.application(NoFacts.application(term("cons"), numeral(elements(place))), rest), place, filters)
    )

  private def filtered(tail: Configured[NoFacts.type], place: Int, filters: Map[Int, Boolean]): Configured[NoFacts.type] =
    filters.get(place).fold(tail)(admitsZero => NoFacts.parallel(tail, listCriterion(admitsZero)))

  /** A numeral's value, zero one time in three. */
  private val value: Gen[Int] = Gen.frequency1(1 -> Gen.constant(0), 2 -> Gen.int(Range.constant(1, 7)))

  stoppableProperty("a list of the real library decodes to its elements exactly when it is filtered at its root and every filter admits them") {
    _ =>
      for
        elements <- Gen.list(value, Range.linear(0, 6)).map(_.toVector).forAll
        rootFiltered <- Gen.boolean.forAll
        rootAdmitsZero <- Gen.boolean.forAll
        tailFilters <- Gen.list(for { place <- Gen.int(Range.constant(1, 6)); admitsZero <- Gen.boolean } yield (place, admitsZero), Range.linear(0, 3)).forAll
      yield
        val filters =
          tailFilters.filter(_._1 <= elements.size).toMap ++ Option.when(rootFiltered)(0 -> rootAdmitsZero)
        val admitted = filters.forall((place, admitsZero) => admitsZero || elements.drop(place).forall(_ > 0))
        val expected = Option.when(rootFiltered && admitted)(NarrowList(elements.map(number => BigInteger.valueOf(number.toLong)), 0))
        Result
          .diff(compilation.listDecoded(list(elements, filters)), expected)(_ == _)
          .log(s"the elements ${elements.mkString(", ")}, the filters ${filters.toVector.sorted.mkString(", ")}")
  }

  /** merge_binary_plus, of the problem generators' library terms
    * (`TermTables.problemLibraryTerms`), which the fixture binds to the
    * native `wren_binary_plus`.
    */
  private lazy val plus: Configured[NoFacts.type] =
    StandardLibrary.entryMembers(buildRoot, TermTables.problemLibraryTerms, Expansions.none)._1
      .getOrElse("merge_binary_plus", throw IllegalArgumentException(s"${TermTables.problemLibraryTerms.file} has no merge_binary_plus"))

  /** The steps within which the reference reads a program; a reading that
    * does not finish within the limit fails the law. The programs written
    * with no filter took at most 2,082 steps (two lists of up to six
    * elements, measured 2026-11-21), and the filtered ones under `HeadsMet`
    * finish within the limit (this law's run of 2026-11-21).
    */
  private val referenceLimit: Long = 10000

  /** tabling(weak_head)'s normal forms of the closed term, its parallels met
    * head by head (`ParallelReading.HeadsMet`, which loses answers and adds
    * none: an answer it gives is one of the program's); none when the reading
    * does not finish. Under `ParallelReading.BothSides` a fold over a list
    * filtered by `list_type (binary_set true)` does not finish: a
    * one-element fold exhausted its tables after 108,271 steps (measured
    * 2026-11-21).
    */
  private def referenceNormalForms(program: Configured[NoFacts.type]): Option[Vector[Configured[NoFacts.type]]] =
    val state = ReadingState.knowingTop(referenceLimit, gezi.weakhead.ReadingConfiguration.withoutFacts).copy(parallels = gezi.weakhead.ParallelReading.HeadsMet)
    NormalForms.normalForms(Mode.TablingWeakHead, program).result(state) match
      case Computed.Done(normalForms, _) => Some(normalForms)
      case Computed.Stopped(_)           => None

  private def closed(instruction: Configured[NoFacts.type]): Term = Term.closed(instruction)

  /** A recursion's list under `∥ list_type (binary_set true)`, the narrow
    * block's list branch.
    */
  private def read(list: Term): Term = list ∥ closed(listCriterion(true))

  /** λs l. (l ∥ list_type (binary_set true)) binary_zero (λh t. plus h (s t)),
    * the sum of a list's elements.
    */
  private val sum: Term =
    λ(self => λ(summand => read(summand)(closed(numeral(0)))(λ(head => λ(tail => closed(plus)(head)(self(tail)))))))

  /** λs a b. (a ∥ list_type (binary_set true)) (fixpoint sum b)
    * (λh t. plus h (s t b)), the sum of both lists' elements.
    */
  private val sumOfBoth: Term =
    λ(self =>
      λ(first =>
        λ(second =>
          read(first)(closed(NarrowBlocks.fixpointByValue)(sum)(second))(λ(head =>
            λ(tail => closed(plus)(head)(self(tail)(second)))
          ))
        )
      )
    )


  private def program(term: Term): Configured[NoFacts.type] = Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)

  /** A list's elements and the filters at its tails, its root filtered by
    * `list_type (binary_set true)`.
    */
  private val filteredList: Gen[(Vector[Int], Map[Int, Boolean])] =
    for
      elements <- Gen.list(value, Range.linear(1, 6)).map(_.toVector)
      tails <- Gen.list(Gen.int(Range.constant(1, 6)), Range.linear(0, 2))
    yield (elements, tails.filter(_ <= elements.size).map(_ -> true).toMap + (0 -> true))

  stoppableProperty("a fold and a recursion over two lists of the real library are one block each and answer as tabling(weak_head)") {
    stopped =>
      for
        (first, firstFilters) <- filteredList.forAll
        (second, secondFilters) <- filteredList.forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        val fixpoint = closed(NarrowBlocks.fixpointByValue)
        def written(elements: Vector[Int], filters: Map[Int, Boolean]) = closed(list(elements, filters))
        val programs = Vector(
          program(fixpoint(sum)(written(first, firstFilters))),
          program(fixpoint(sumOfBoth)(written(first, firstFilters))(written(second, secondFilters)))
        )
        Result
          .all(
            programs.toList.zipWithIndex.map { case (block, position) =>
              val computed = compilation.compiled(compilation.blocks(block), DebugAttributes.Omitted, stop).map(_.map(_.run(stop)))
              val answered = computed match
                case Right(Vector(Some(value))) => referenceNormalForms(numeral(value.intValueExact))
                case _                          => None
              Result
                .all(
                  List(
                    Result
                      .assert(compilation.blocks(block) == Vector(block))
                      .log(s"the program is not its one block: ${compilation.blocks(block).size} blocks"),
                    Result.assert(answered.nonEmpty).log(s"the block computed $computed"),
                    Result.diff(answered, referenceNormalForms(block))(_ == _).log("the block's answer and the reference's")
                  )
                )
                .log(s"the program $position")
            }
          )
          .log(s"the first list ${first.mkString(", ")} filtered at ${firstFilters.keys.toVector.sorted.mkString(", ")}, the second ${second
              .mkString(", ")} filtered at ${secondFilters.keys.toVector.sorted.mkString(", ")}")
  }
