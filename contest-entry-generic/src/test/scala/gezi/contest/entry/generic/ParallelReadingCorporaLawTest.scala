package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Computed
import gezi.weakhead.Expansions
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ParallelReading
import gezi.weakhead.ReadingState

/** `ParallelReading.HeadsMet` on a fold the tabled weak head did not finish
  * under `BothSides`, on the real library: a fold of a list's elements by `merge_binary_plus`, the list filtered by
  * `list_type (binary_set true)` at each call, over canonical binary naturals
  * of the library's `binary`. Under `BothSides` the fold is applied to the
  * type itself, whose sums are every natural, and the reading exhausted its
  * tables after 108,271 steps for one element (measured 2026-11-21); under
  * `HeadsMet` each filter meets its list cell by cell, so the fold
  * reads the list alone.
  */
class ParallelReadingCorporaLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The members of the JIT tests' library terms and of the problems'
    * (`merge_binary_plus`).
    */
  private lazy val terms: Map[String, Instruction] =
    StandardLibrary.entryMembers(buildRoot, TermTables.problemLibraryTerms, Expansions.none)._1 ++
      StandardLibrary.entryMembers(buildRoot, TermTables.jitLibraryTerms, Expansions.none)._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => terms)

  private def term(name: String): Instruction =
    terms.getOrElse(name, throw IllegalArgumentException(s"neither library terms file has a member $name"))

  private def closed(instruction: Instruction): Term = Term.closed(instruction)

  /** The steps of one reading: well above what the unfiltered fold of six
    * elements below 64 takes (2,082 steps at most for the issue's witness).
    */
  private val limit: Long = 200000

  private def numeral(value: Int): Instruction =
    if value == 0 then term("binary_zero")
    else Instruction.Apply(term(if (value & 1) == 1 then "binary_odd" else "binary_even"), numeral(value >> 1))

  private def list(elements: List[Int]): Instruction =
    elements.foldRight(term("nil"))((element, rest) => Instruction.Apply(Instruction.Apply(term("cons"), numeral(element)), rest))

  private val fixpoint: Term = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))

  /** The sum of the list's elements, the list filtered at each call when
    * `isFiltered`.
    */
  private def sum(isFiltered: Boolean, elements: List[Int]): Instruction =
    val criterion = closed(Instruction.Apply(term("list_type"), Instruction.Apply(term("binary_set"), term("true"))))
    val fold = fixpoint(
      λ(self =>
        λ(summand =>
          (if isFiltered then summand ∥ criterion else summand)(closed(term("binary_zero")))(
            λ(head => λ(tail => closed(term("merge_binary_plus"))(head)(self(tail))))
          )
        )
      )
    )
    Defunctionalization.thunkInstruction(fold(closed(list(elements))).deBruijnTerm(Map.empty))

  private def read(program: Instruction, parallels: ParallelReading): Either[String, (Set[Instruction], Long)] =
    val start = ReadingState.knowingTop(limit).copy(parallels = parallels)
    NormalForms.normalForms(Mode.TablingWeakHead, program).result(start) match
      case Computed.Done(forms, after) => Right((forms.toSet, after.budget.spent))
      case Computed.Stopped(after)     => Left(s"stopped (${after.exhausted}) after ${after.budget.spent} steps")

  /** Purpose: catch a met reading that still applies the fold to the type
    * (steps far beyond the unfiltered fold's, or a reading that does not
    * finish), or that loses the list the filter admits (another normal form
    * than the unfiltered fold's). The bound is set from the steps of lists of
    * 0 to 6 elements 63 (MEASURED 2026-11-21): unfiltered 775, 1,452, 1,740,
    * 2,021, 2,287, 2,550 and 2,816; filtered under `HeadsMet` 1,304, 1,543,
    * 1,839, 2,128, 2,402, 2,673 and 2,947, about 530 more for the nil filter
    * and about 100 more for each cell; under `BothSides` every one ran out
    * of its 50,000 tables at 108,242 to 108,840 steps.
    */
  property("aFilteredSumReadsTheUnfilteredSumsFormInLinearSteps") {
    for elements <- Gen.int(Range.linear(0, 63)).list(Range.linear(0, 6)).forAll
    yield
      val filteredReading = ParallelReading.HeadsMet
      (read(sum(false, elements), filteredReading), read(sum(true, elements), filteredReading)) match
        case (Right((unfiltered, unfilteredSteps)), Right((filtered, filteredSteps))) =>
          Result.all(
            List(
              Result.diff(unfiltered, filtered)(_ == _).log("the normal forms"),
              Result
                .assert(filteredSteps <= unfilteredSteps + 600 + 150 * elements.size)
                .log(s"steps: filtered $filteredSteps, unfiltered $unfilteredSteps, ${elements.size} elements")
            )
          )
        case other => Result.failure.log(s"a reading did not finish: $other")
  }
