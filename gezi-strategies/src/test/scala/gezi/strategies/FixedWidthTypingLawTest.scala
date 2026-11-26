package gezi.strategies

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.frontend.Term
import gezi.ir.BuiltInRule
import gezi.ir.Instruction
import gezi.saturation.End
import gezi.generatedinputs.GeneratedProperties
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions

/** The law of the fixed-width integers' schemes in the zero universe
  * (corpora/compiler/fixed_width_unions.lambdalattice): the
  * HM baseline's saturation of a thin operation at 16 bits applied to two
  * words of a generated width, or to a boolean and a word, reaches a fixed
  * point within the budget, and its graph holds a clash exactly when an
  * operand is not a word of 16 bits. Its purpose is to catch a lemma whose
  * instances do not end on a program HM rejects (the unfolding of
  * word_structure, read from right to left, once grew without end on a
  * clash) and a scheme that types a mismatched width or misses the right one.
  * The program's library terms are members of fixture files read by
  * projection, closed instructions in the HOAS (`Term.closed`). The library
  * is the first field of the Prolog backend's fixed-width preset
  * (corpora/compiler/prolog_backend_fixed_width_preset.lambdalattice), read
  * as the one field of
  * tests/library_fixtures/fixed_width_preset.lambdalattice, its
  * backend and the native typing of the types it represents, words
  * included; native typing is enabled through a preset only.
  */
class FixedWidthTypingLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of FixedWidthTypingLawTest, "a thin operation's saturation ends, and clashes exactly on a mismatched operand", takes 12.572 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

  /** Measured on 2026-11-14: the preset's compilation with the
    * round options takes about 13.5 s; it is not charged to a test, nor is
    * the reading of the zero universe's heads the verdict recognizes.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => options, _ => terms, _ => FixpointVerdicts.zeroUniverseHeads)

  private lazy val library =
    LibraryFiles.compiled("tests/library_fixtures/fixed_width_preset.lambdalattice", Vector.empty)

  /** The budget of a run, in instances. Measured 2026-11-13 under the
    * fixed-width preset (its type check with the backend's shapes), int16_add
    * on the words of 5 and 6: at 16 bits the run reaches its fixed point at
    * 3,053 instances, at 15 and 17 bits at 4,317 and 3,432 (a clash), on true
    * and a word at 1,911 (a clash).
    */
  private val budget = 20000

  /** The options of every run: the lemmas of the round
    * `fixed_width_type_check`, the fixed-width preset's type-check round
    * (hindley_milner_unions', native_arithmetic_unions',
    * prolog_backend_shapes', fixed_width_unions' and fixed_width_shapes').
    */
  private lazy val options =
    BaselineRounds.saturationOptions(library, StrategyTesting.round("fixed_width_type_check"), BuiltInRule.all, budget)

  private val operations: Vector[String] =
    Vector("int16_add", "int16_subtract", "int16_multiply", "int16_less_than", "int16_equal")

  /** The library terms of the program, members of the fixture files
    * under Gezi's directory.
    */
  private lazy val terms: Map[String, Instruction] =
    val root = LibraryFiles.buildRoot
    StandardLibrary.entryMembers(root, TermTables.fixedWidthTerms, Expansions.none)._1 ++
      StandardLibrary.entryMembers(root, TermTables.jitLibraryTerms, Expansions.none)._1

  private def term(key: String): Term =
    Term.closed(terms.getOrElse(key, throw IllegalArgumentException(s"no fixture member $key")))

  private def word(width: Int, value: Long): Term =
    (0 until width).foldRight(term("word_end"))((position, above) =>
      term("word_cell")(term(if ((value >> position) & 1L) == 1L then "true" else "false"))(above)
    )

  stoppableProperty(
    "a thin operation's saturation ends, and clashes exactly on a mismatched operand",
    _.copy(testLimit = SuccessCount(12))
  ) { stopped =>
    for
      operation <- Gen.int(Range.constant(0, operations.size - 1)).map(operations).forAll
      width <- Gen.frequency1(1 -> Gen.constant(16), 1 -> Gen.int(Range.linear(13, 19))).forAll
      boolean <- Gen.frequency1(4 -> Gen.constant(false), 1 -> Gen.constant(true)).forAll
      value <- Gen.long(Range.linear(0L, (1L << 13) - 1L)).forAll
    yield
      val left = if boolean then term("true") else word(width, value)
      val program = term(operation)(left)(word(width, value + 1))
      val input = StrategyTesting.programInput(library, program)
      val run = FixpointEgraph.saturated(
        library.index,
        Vector(input),
        options,
        explained = false,
        StopSignal.completedWith(stopped)
      )
      val clash = FixpointVerdicts.ZeroUniverse(run.graph).clash
      Result.all(
        List(
          Result.assert(run.end.isInstanceOf[End.FixedPoint]).log(s"the run ended ${run.end}"),
          Result.diff(clash, boolean || width != 16)(_ == _)
        )
      )
  }
