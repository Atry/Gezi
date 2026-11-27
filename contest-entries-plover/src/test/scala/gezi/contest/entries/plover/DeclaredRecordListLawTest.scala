package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.jit.NativesProvider
import gezi.narrowblocks.lists.NarrowBlockCompilation
import gezi.narrowblocks.lists.NarrowConstant
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions

private given declaredRecordListLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the narrow blocks over declared data families. Decoding: on
  * generated lists of pairs written in normal form under the filter
  * `∥ list_type (plover_pair_type c d)`, to catch a column read from the wrong
  * field, a pair whose two fields are one term (which the front end spells with
  * one slot), an empty list, a field its criterion does not admit decoded
  * anyway, and a block that decodes records although the option is off.
  * Encoding: on generated programs of the fewest coins, to catch a block's root
  * value rebuilt with the wrong constructor, none and some alike, and a value
  * of a position or a number of fields the family does not have, or a field its
  * criterion does not admit, rebuilt anyway.
  */
class DeclaredRecordListLawTest extends GeneratedProperties:

  // The first property reads the entry's knowledge, as OrderedCompositionsEntrySnapshotTest does (about 15 s of that
  // suite's 16 to 33 s on 4 CPUs beside other sessions' runs), past the 3 s default.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(90, "s")

  private lazy val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val compilation =
    val (data, afterEntry) =
      EntryData.at(
        buildRoot,
        buildRoot.resolve("contest-entries-plover/entry.lambdalattice"),
        Defaults.entryDataState
      )
    GenericEntryProvider.initialized(
      data,
      ExecutorModules.registered(buildRoot),
      ExtractorModules.registered(buildRoot),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    ) match
      case generic: GenericEntry[?] => generic.compilation

  private lazy val withRecords = NarrowBlockCompilation(
    compilation.index,
    compilation.natives,
    gezi.weakhead.ReadingConfiguration.withoutFacts,
    declaredRecords = true
  )

  private lazy val withoutRecords = NarrowBlockCompilation(
    compilation.index,
    compilation.natives,
    gezi.weakhead.ReadingConfiguration.withoutFacts
  )

  private def field(
      file: String,
      arity: Int,
      position: Int
  ): Configured[NoFacts.type] =
    StandardLibrary
      .entryFields(buildRoot, buildRoot.resolve(file), Expansions.none, arity)
      ._1(position)

  private lazy val pairType = field(
    "corpora/library/plover_compositions/plover_pair_type.lambdalattice",
    2,
    1
  )
  private lazy val listType =
    field("corpora/library/native_types/list.lambdalattice", 4, 3)
  private lazy val binarySet =
    field("corpora/library/binary/natural.lambdalattice", 5, 4)
  private lazy val admitsZero = NoFacts.application(
    binarySet,
    field("corpora/library/native_types/boolean.lambdalattice", 4, 0)
  )
  private lazy val positive = NoFacts.application(
    binarySet,
    field("corpora/library/native_types/boolean.lambdalattice", 4, 1)
  )

  private def natural(number: Int): String =
    if number == 0 then "(λz e o. z)"
    else if number % 2 == 1 then s"(λz e o. o ${natural(number / 2)})"
    else s"(λz e o. e ${natural(number / 2)})"

  private def listText(records: List[(Int, Int)]): String =
    records.foldRight("(λn c. n)") { case ((first, second), rest) =>
      s"(λn c. c (λk. k ${natural(first)} ${natural(second)}) $rest)"
    }

  private def filtered(
      records: List[(Int, Int)],
      first: Configured[NoFacts.type],
      second: Configured[NoFacts.type]
  ): Configured[NoFacts.type] =
    NoFacts.parallel(
      Defunctionalization.thunkInstruction(
        Lambdalattice.term(listText(records))
      )(using gezi.ir.NoFacts),
      NoFacts.application(
        listType,
        NoFacts.application(NoFacts.application(pairType, first), second)
      )
    )

  private val drawnRecords: Gen[List[(Int, Int)]] =
    Gen.choice1(
      Gen.constant(Nil),
      (for
        first <- Gen.int(Range.linear(0, 40))
        second <- Gen.int(Range.linear(0, 40))
        same <- Gen.boolean
      yield (first, if same then first else second)).list(Range.linear(1, 12))
    )

  private def columns(
      constant: Option[NarrowConstant]
  ): Option[Vector[Vector[Int]]] =
    constant.collect { case NarrowConstant.RecordsOf(records) =>
      records.columns.map(_.map(_.intValueExact))
    }

  property(
    "a filtered list of pairs decodes column by column, and only with the option on"
  ) {
    for records <- drawnRecords.forAll
    yield
      val term = filtered(records, admitsZero, admitsZero)
      Result.all(
        List(
          Result.diff(
            columns(withRecords.constant(term)),
            Some(Vector(records.toVector.map(_._1), records.toVector.map(_._2)))
          )(_ == _),
          Result.diff(withoutRecords.constant(term), None)(_ == _)
        )
      )
  }

  property("a field its criterion does not admit leaves the list undecoded") {
    for records <- drawnRecords.forAll
    yield
      val decoded =
        columns(withRecords.constant(filtered(records, positive, admitsZero)))
      Result.diff(decoded.isDefined, records.forall(_._1 > 0))(_ == _)
  }

  private lazy val minimizingCoins = field(
    "corpora/library/plover_compositions/plover_minimizing_coins.lambdalattice",
    2,
    0
  )
  private lazy val typedMinimizingCoins = field(
    "corpora/library/plover_compositions/plover_minimizing_coins.lambdalattice",
    2,
    1
  )
  private lazy val optionNone = field(
    "corpora/library/plover_compositions/plover_option_type.lambdalattice",
    3,
    0
  )
  private lazy val optionSome = field(
    "corpora/library/plover_compositions/plover_option_type.lambdalattice",
    3,
    1
  )

  private def numeralInstruction(number: Int): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction(Lambdalattice.term(natural(number)))(
      using gezi.ir.NoFacts
    )

  private def naturalsText(numbers: List[Int]): String =
    numbers.foldRight("(λn c. n)")((number, rest) =>
      s"(λn c. c ${natural(number)} $rest)"
    )

  /** The least length of the sequences of coins that sum to the target. */
  private def fewest(coins: List[Int], remaining: Int): Option[Int] =
    if remaining == 0 then Some(0)
    else
      coins
        .filter(_ <= remaining)
        .flatMap(coin => fewest(coins, remaining - coin).map(_ + 1))
        .minOption

  // KNOWN FAILURE until https://github.com/Atry/private-overlay/issues/2238: the specialized spelling makes a program's
  // typed constants storages at construction (a binary natural's, a list's), and the narrow blocks do not yet take
  // storages (#2238, "块入口直接收到存储"): a constant storage is of no narrow kind and does not decode as a literal, so
  // no block is compiled.
  stoppableProperty(
    "a block whose root is a family's value is replaced by that constructor's term, none and some alike".fail
  ) { stopped =>
    for
      coins <- Gen.int(Range.linear(2, 9)).list(Range.linear(0, 3)).forAll
      target <- Gen.int(Range.linear(0, 12)).forAll
    yield
      val program = NoFacts.application(
        NoFacts.application(
          minimizingCoins,
          Defunctionalization.thunkInstruction(
            Lambdalattice.term(naturalsText(coins))
          )(using gezi.ir.NoFacts)
        ),
        numeralInstruction(target)
      )
      val expected = fewest(coins, target).fold(optionNone)(count =>
        NoFacts.application(optionSome, numeralInstruction(count))
      )
      val (_, rounds) = gezi.narrowblocks.ProgramCompiler.compiledProgram(
        compilation,
        program,
        false,
        gezi.saturation.StopSignal.completedWith(stopped)
      )
      Result.diff(rounds.flatMap(_.program), Some(expected))(_ == _)
  }

  property(
    "a family's value that is not the constructor's shape gives no term"
  ) {
    for field <- Gen.int(Range.linear(0, 9)).forAll
    yield
      val call = NoFacts.application(
        NoFacts.application(typedMinimizingCoins, numeralInstruction(1)),
        numeralInstruction(1)
      )
      val value = java.math.BigInteger.valueOf(field.toLong)
      Result.all(
        List(
          Result.diff(
            withRecords.constructedTerm(
              call,
              gezi.jit.ConstructedNaturals(2, Vector.empty)
            ),
            None
          )(_ == _),
          Result.diff(
            withRecords.constructedTerm(
              call,
              gezi.jit.ConstructedNaturals(0, Vector(value))
            ),
            None
          )(_ == _),
          Result.diff(
            withRecords.constructedTerm(
              call,
              gezi.jit.ConstructedNaturals(1, Vector.empty)
            ),
            None
          )(_ == _),
          Result.diff(
            withRecords.constructedTerm(
              call,
              gezi.jit.ConstructedNaturals(
                1,
                Vector(value.negate.subtract(java.math.BigInteger.ONE))
              )
            ),
            None
          )(_ == _),
          Result.diff(
            withRecords.constructedTerm(
              call,
              gezi.jit.ConstructedNaturals(1, Vector(value))
            ),
            Some(NoFacts.application(optionSome, numeralInstruction(field)))
          )(_ == _)
        )
      )
  }
