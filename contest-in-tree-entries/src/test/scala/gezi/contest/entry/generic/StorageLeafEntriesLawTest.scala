package gezi.contest.entry.generic

import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.frontend.Defunctionalization
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.Closed
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.StorageAccess
import gezi.ir.NativeStorage
import gezi.jit.NativesProvider
import gezi.narrowblocks.PreparedLemmaCompilation
import gezi.saturation.StopSignal
import gezi.strategies.FixpointEgraph
import gezi.frontend.Term
import gezi.frontend.TermOf
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.StorageEncoding
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import scala.util.Random

private given storageLeafEntriesLawTestNoFacts: NoFacts.type = NoFacts

/** The law that the in-tree entries' rounds read the native storages they are
  * given as leaves, never their views. For each of wren, solo and plover,
  * generated programs over the library's naturals (a natural's storage given to
  * `double`, `even` and `successor`, as the standard library families write
  * their sites) are run through the entry's rounds one after another, each
  * round saturated and extracted on its own, every round under the construction
  * that converts terms into storages (`gezi.jit.ConvertedTermConstruction`),
  * once with a capability that reads native data only
  * (`StorageAccess.dataOnly`), under which a view read throws, and once with
  * one that reads views. Derived before the run from the gateway
  * (`Store.expanded`), the pattern view and the walks that stop at a leaf
  * (`heldAsLeaf`): no round throws; each round's output is the output the round
  * gives when views are readable, since its graph sees the same leaves, hash
  * codes and criteria; and for each entry its rounds are given storage leaves
  * (the precondition that the law is not vacuous). The entries open a closure
  * only where their opening criterion says (wren's `calls_a_head`), which these
  * closures do not meet, so no body over a leaf is written back here;
  * `gezi.saturation.StorageLeafAbstractionLawTest` checks that path directly.
  * No lemma instance of the entries' rounds binds a leaf's class today: HM
  * types a literal by its constructors, which a storage leaf hides, until the
  * reverse lemma that types `x ∥ T` by T alone; `PatternViewMatchingLawTest`
  * checks the matching through a pattern view. TODO: require such an instance
  * once that lemma is in the entries' rounds
  * (https://github.com/Atry/private-overlay/issues/2188). The programs give a
  * storage to the first round too: the entries' rounds as written leave no
  * unique spelling of a natural in their outputs for these programs, so
  * storages reach the rounds through the input, as they will from the readers'
  * products and compile-time evaluation. A native the construction folds
  * (`gezi.ir.TermConstruction.folded`) reads a storage's native data, which the
  * data-only capability reads, so `double s` and `even s` fold in both runs
  * alike. It does not show that no view is read on paths these rounds do not
  * take. Its purpose is to catch a traversal of an entry's typed rounds, its
  * extraction or its write-back that reads a storage leaf's view.
  */
class StorageLeafEntriesLawTest extends gezi.generatedinputs.FailFastSuite:

  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(240, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The library's terms the problems read, by name
    * (`TermTables.problemLibraryTerms`).
    */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(buildRoot, TermTables.problemLibraryTerms, Expansions.none)
      ._1

  /** A natural's storage under the encoding (a leaf of the e-graph), given to
    * one to three of the library's operations on naturals (`double`, `even`,
    * `successor`), as the standard library families write their sites; every
    * other program is a closure whose body holds that application,
    * `λx. op x + op (… s)`, its filling a storage, which the saturator opens
    * and writes back (an applied closure would be reduced by β instead).
    */
  private def programs[C <: NativeSpecializer & Singleton](
      encoding: StorageEncoding & C
  ): Vector[Configured[C]] =
    given C = encoding
    given StorageAccess = StorageAccess.granted()
    val random = Random(20261201)
    val operationsIn = termsIn(encoding)
    def natural: TermOf[Configured[C]] =
      Term.closed(
        storageIn(
          encoding,
          Representation.BigInteger,
          NativeValue.Natural(BigInt(random.nextInt(40)))
        )
      )
    (0 until 6).toVector.map { position =>
      val operations = Vector.fill(1 + random.nextInt(3))(
        operationsIn(Vector("double", "even", "successor")(random.nextInt(3)))
      )
      val applied =
        operations.foldLeft(natural)((inner, operation) => operation(inner))
      val program = if position % 2 == 0 then applied
      else Term.λ(x => operations.head(x) + applied)
      Defunctionalization.thunkInstruction[C](program.deBruijnTerm(Map.empty))
    }

  /** The library's terms the problems read, as terms of the configuration of
    * the specializer given: the same objects.
    */
  private def termsIn[C <: NativeSpecializer & Singleton](
      specializer: C
  ): Map[String, TermOf[Configured[C]]] =
    terms.view
      .mapValues(term =>
        Term.closed(Configured.fromPure(specializer)(Pure.required(term)))
      )
      .toMap

  /** The storage of the value under the encoding, as a term of its
    * configuration: a storage holds no neutral value.
    */
  private def storageIn[C <: NativeSpecializer & Singleton](
      encoding: StorageEncoding & C,
      representation: Representation[Nothing],
      value: NativeValue[Nothing]
  )(using C, StorageAccess): Configured[C] =
    Closed
      .configured(encoding.operations.storageOf(representation, value))
      .getOrElse(throw IllegalStateException(s"a storage is closed: $value"))

  /** Every subterm, each once, a storage's view not read. */
  private def subterms[C <: NativeSpecializer & Singleton](
      root: Configured[C]
  ): Vector[Configured[C]] =
    @scala.annotation.tailrec
    def walked(
        pending: List[Configured[C]],
        seen: Set[Configured[C]],
        found: Vector[Configured[C]]
    ): Vector[Configured[C]] = pending match
      case Nil                        => found
      case term :: rest if seen(term) => walked(rest, seen, found)
      case term :: rest if NativeStorage.stored(term.representation) =>
        walked(rest, seen + term, found :+ term)
      case term :: rest =>
        val children = term.layer match
          case gezi.ir.Apply(function, argument) => List(function, argument)
          case gezi.ir.Parallel(left, right)     => List(left, right)
          case gezi.ir.Choice(left, right)       => List(left, right)
          case gezi.ir.Thunk(_, _, fillings)     => fillings.toList
          case _                                 => Nil
        walked(children ::: rest, seen + term, found :+ term)
    walked(List(root), Set.empty, Vector.empty)

  /** The entry of the directory, read as the judge's entry reads it, opened in
    * its configuration.
    */
  private def entryRounds(directory: String): EntryRounds[?] =
    val entryDirectory = buildRoot.resolve(directory)
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    EntryRounds.of(
      directory,
      GenericEntryProvider.initialized(
        data,
        gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory),
        gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory),
        NativesProvider.loaded,
        ArticleDestination.Discarded,
        afterEntry,
        Defaults.caches()
      )
    )

  /** The round with its saturation's options changed. */
  private def withOptions[C <: NativeSpecializer & Singleton](
      round: PreparedLemmaCompilation[C],
      change: gezi.strategies.SaturationOptions[
        C
      ] => gezi.strategies.SaturationOptions[C]
  ): PreparedLemmaCompilation[C] =
    val options = change(round.saturator.options)
    round.copy(saturator =
      round.saturator.copy(
        options = options,
        round = Some(FixpointEgraph.compiledRound(round.index, options))
      )
    )

  Vector(
    "contest-entries-wren",
    "contest-entries-solo",
    "contest-entries-plover"
  ).foreach(directory =>
    stoppableTest(
      s"$directory's rounds read storage leaves without their views and write back what they give reading views"
    ) { stopped =>
      entryRounds(directory).readNoView(StopSignal.completedWith(stopped))
    }
  )

  /** The law that the expansion direction of the storage's view changes no
    * output of the entries' typed rounds: for each of wren, solo and plover,
    * the generated programs above are run through the entry's rounds under the
    * converting construction, each round once with its storages as leaves and
    * once with the expansion direction enabled (`BuiltInRule.StorageView`), the
    * next round given the first's output. Derived before the run: with the
    * expansion, each leaf's class holds its view's nodes besides the leaf, so a
    * lemma that matches `?x ∥ ?T` or reads inside the value finds at least the
    * matches it finds on the leaf (the typed calls found with leaves are among
    * those found with the expansion), and none of these rounds' lemmas reads a
    * value's constructors (#2163 B2's audit of the typed rounds), so the
    * extraction gives the same term; where it reads a view's nodes in place of
    * the leaf, the write-back's construction converts them back into the same
    * storage. So the outputs are the same term; and some round expands a
    * storage (the precondition that the law is not vacuous). Its purpose is to
    * catch an expansion that loses or adds a rewrite of a typed round, or a
    * write-back that leaves a storage's view spelled out.
    */
  Vector(
    "contest-entries-wren",
    "contest-entries-solo",
    "contest-entries-plover"
  ).foreach(directory =>
    stoppableTest(
      s"$directory's rounds with the storage view's expansion write back what they write back with storage leaves"
    ) { stopped =>
      entryRounds(directory).expansionAlike(StopSignal.completedWith(stopped))
    }
  )

  /** The law of the extraction at a folded class, for each of wren, solo and
    * plover: a generated chain `double (… (double s))` of d doublings of a
    * natural's storage s = `Natural(k)`, d from 0 to 3, under `even` or not,
    * run through the entry's rounds one after another under the converting
    * construction, is extracted as the storage of the natives' result,
    * `Natural(2^d k)` or the truth of its parity. Derived before the run: the
    * first round folds each application from the innermost out (each argument's
    * class holds a storage leaf of the native's parameter place once the
    * application below it is folded), so the input's class holds the result's
    * storage; that storage is a leaf of constant cost, which the plan's cost
    * requirement on an extraction's model (B10: a storage of constant size
    * costs no more than any production of its class) makes the class's least
    * entry; a later round's input is that leaf and gives it back. Its purpose
    * is to catch an entry's cost model that prefers a spelling of the
    * computation to the value a fold gave, or a round that loses the storage.
    */
  Vector(
    "contest-entries-wren",
    "contest-entries-solo",
    "contest-entries-plover"
  ).foreach(directory =>
    stoppableTest(s"$directory's rounds extract the storage a fold gives") {
      stopped =>
        entryRounds(directory).foldExtracted(StopSignal.completedWith(stopped))
    }
  )

  /** An entry's rounds in its configuration `C`, with the laws' bodies. */
  private final case class EntryRounds[C <: NativeSpecializer & Singleton](
      directory: String,
      entry: GenericEntry[C]
  ):

    private given C = entry.specializer

    private given StorageAccess = StorageAccess.granted()

    /** The entry's rounds, each under the construction that converts terms into
      * storages, with the capability given.
      */
    private def converting(
        access: StorageAccess
    ): Vector[PreparedLemmaCompilation[C]] =
      val construction =
        gezi.jit.ConvertedTermConstruction[C](entry.encoding)(access)
      entry.rounds.map(round =>
        withOptions(round, _.copy(construction = construction))
      )

    private def output(
        round: PreparedLemmaCompilation[C],
        input: Configured[C],
        stop: StopSignal
    ): Configured[C] =
      round.extracted(
        input,
        round.saturated(input, explained = false, stop),
        stop
      )

    def readNoView(stop: StopSignal): Unit =
      val dataOnly = converting(StorageAccess.dataOnly())
      val readingViews = converting(StorageAccess.granted())
      val counts = programs(entry.encoding).zipWithIndex.map {
        (input, position) =>
          dataOnly
            .zip(readingViews)
            .zipWithIndex
            .foldLeft((input, 0)) {
              case (
                    (current, leavesGiven),
                    ((dataOnlyRound, viewRound), number)
                  ) =>
                val leaves = subterms(current).count(term =>
                  term.layer match
                    case storage: NativeStorage => storage.leafInEGraph
                    case _                      => false
                )
                val viewOutput = output(viewRound, current, stop)
                assert(
                  Configured
                    .same(output(dataOnlyRound, current, stop), viewOutput),
                  s"$directory, program $position, round $number"
                )
                (viewOutput, leavesGiven + leaves)
            }
            ._2
      }
      assert(
        counts.sum > 0,
        s"$directory: no round was given a storage leaf: the law is vacuous ($counts)"
      )

    def expansionAlike(stop: StopSignal): Unit =
      val rounds = converting(StorageAccess.granted())
      val expanding = rounds.map(round =>
        withOptions(
          round,
          options =>
            options.copy(builtInRules =
              options.builtInRules + BuiltInRule.StorageView
            )
        )
      )
      val counts = programs(entry.encoding).zipWithIndex.map {
        (input, position) =>
          rounds
            .zip(expanding)
            .zipWithIndex
            .foldLeft((input, 0)) {
              case (
                    (current, expansions),
                    ((leafRound, expandingRound), number)
                  ) =>
                val leafOutput = output(leafRound, current, stop)
                val expandedRun =
                  expandingRound.saturated(current, explained = false, stop)
                val expandedOutput =
                  expandingRound.extracted(current, expandedRun, stop)
                assert(
                  Configured.same(expandedOutput, leafOutput),
                  s"$directory, program $position, round $number"
                )
                val made = expandedRun.graph.unions.count(_.justification match
                  case gezi.egraph.Justification.StorageView(_) => true
                  case _                                        => false)
                (leafOutput, expansions + made)
            }
            ._2
      }
      assert(
        counts.sum > 0,
        s"$directory: no round expanded a storage: the law is vacuous ($counts)"
      )

    def foldExtracted(stop: StopSignal): Unit =
      val rounds = converting(StorageAccess.granted())
      val random = Random(20261140)
      val operationsIn = termsIn(entry.specializer)
      def stored(
          value: NativeValue[Nothing],
          representation: Representation[Nothing]
      ): Configured[C] =
        storageIn(entry.encoding, representation, value)
      (1 to 6).foreach { position =>
        val (value, doublings, parity) =
          (random.nextInt(40), random.nextInt(4), random.nextBoolean())
        val doubled = (1 to doublings).foldLeft(
          Term.closed(
            stored(
              NativeValue.Natural(BigInt(value)),
              Representation.BigInteger
            )
          )
        )((inner, _) => operationsIn("double")(inner))
        val program = if parity then operationsIn("even")(doubled) else doubled
        val input: Configured[C] = Defunctionalization.thunkInstruction[C](
          program.deBruijnTerm(Map.empty)
        )
        val result = BigInt(value) * BigInt(2).pow(doublings)
        val expected =
          if parity then
            stored(NativeValue.Truth(result % 2 == 0), Representation.Truth)
          else stored(NativeValue.Natural(result), Representation.BigInteger)
        val found = rounds.foldLeft(input)((current, round) =>
          output(round, current, stop)
        )
        assert(
          Configured.same(found, expected),
          s"$directory, program $position: natural $value, $doublings doublings, even $parity"
        )
      }

  private object EntryRounds:

    /** The entry's rounds opened in its configuration. */
    def of[C <: NativeSpecializer & Singleton](
        directory: String,
        entry: GenericEntry[C]
    ): EntryRounds[C] = EntryRounds(directory, entry)
