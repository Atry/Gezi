package gezi.weakhead

import gezi.ir.NoFacts
import gezi.ir.Configured
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Literals
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Value
import gezi.standardlibrary.LibraryFiles
import gezi.weakhead.EvaluatorTesting.*

/** The knowledge file `corpora/compiler/top`:
  * top
  * noinline and the five equations that remove it. The law: on a generated
  * closed term M, under `weak_head` and `tabling(weak_head)`, the two sides
  * of each lemma applied to M both finish and read the same normal forms.
  * top M = top and top ∥ M = top read no operand, so they are held on every M; the
  * other three read M, so they are held wherever M's own reading finishes
  * within the limit, each side then given that limit and the steps of top
  * beside it. A side that does not finish fails the law, so that a run
  * cannot pass by comparing nothing. Its purpose is to catch a lemma of the
  * file written with a side the readers do not read as the other (the wrong
  * side kept, an operand lost, another term than top). The lemmas' proofs are
  * Lean's (`ContextualPreorderTop.lean`); this checks the file's statements
  * against the readers, not the theorems. The second test checks that the
  * term the file declares noinline is the front end's top, so that a path to
  * another file would fail it.
  */
class TopKnowledgeLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private lazy val library = LibraryFiles.compiled("corpora/compiler/top.lambdalattice", Vector.empty)

  /** The library of top's knowledge file, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => library)

  private val lemmas: Vector[String] =
    Vector("top_choice_left", "top_choice_right", "top_applied", "top_parallel_left", "top_parallel_right")

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  /** The steps of one reading, the limit of
    * `ClosedBesideOpenedVariableLawTest`'s readings of a generated term.
    */
  private val limit: Long = 20000

  /** The steps a side may take beyond the term's own reading: those of the
    * lemma's own abstraction and of top beside the term, the limit of
    * `ClosedBesideOpenedVariableLawTest`'s readings that read neither side.
    */
  private val besideLimit: Long = 400

  /** The lemmas neither of whose sides reads the term they are applied to. */
  private val readNoOperand: Set[String] = Set("top_applied", "top_parallel_left")

  private val closed = HoasGenerators.closedTerm

  private def sides(name: String): (Configured[NoFacts.type], Configured[NoFacts.type]) =
    val found = library.index
      .sides(library.index.lemmaIdentifier(name))
      .getOrElse(throw IllegalStateException(s"$name has no sides"))
    (found.left, found.right)

  property("theTwoSidesOfEachLemmaReadTheSameNormalFormsOnAGeneratedTerm") {
    for term <- closed.forAll
    yield
      val argument = valueOf(term)
      Result.all(
        for
          name <- lemmas.toList
          mode <- modes.toList
        yield
          val (left, right) = sides(name)
          def read(side: Configured[NoFacts.type]) =
            normalFormsWithin(mode, Value.Apply(Value.of(side), argument), limit + besideLimit)
          if readNoOperand(name) || normalFormsWithin(mode, argument, limit).finished then
            (read(left), read(right)) match
              case (Bounded.Finished(leftRead), Bounded.Finished(rightRead)) =>
                Result.diff(leftRead.toSet, rightRead.toSet)(_ == _).log(s"$name under $mode")
              case (leftEnd, rightEnd) =>
                Result.failure.log(s"$name under $mode: a side did not finish: $leftEnd, $rightEnd")
          else Result.success
      )
  }

  test("theNoinlineTermOfTheFileIsTheFrontEndsTop") {
    assertEquals(library.index.noinline, Set[Configured[NoFacts.type]](Defunctionalization.thunkInstruction[NoFacts.type](Literals.top)))
  }
