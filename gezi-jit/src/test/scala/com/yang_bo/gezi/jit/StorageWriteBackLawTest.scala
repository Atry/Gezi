package com.yang_bo.gezi.jit

import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.Closed
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.TermConstruction
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.jit.JitTesting.libraryTerm
import com.yang_bo.gezi.saturation.Run
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.strategies.BaselineModules
import com.yang_bo.gezi.strategies.CountedExtractor
import com.yang_bo.gezi.strategies.NativeRouteCompilation
import com.yang_bo.gezi.strategies.RoundModules
import com.yang_bo.gezi.strategies.StandardIndexer
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.strategies.BaselineRounds
import com.yang_bo.gezi.strategies.FixpointReport
import com.yang_bo.gezi.strategies.Round
import com.yang_bo.gezi.strategies.Schedule
import com.yang_bo.gezi.strategies.StandardSaturator
import com.yang_bo.gezi.strategies.SaturationOptions
import com.yang_bo.gezi.strategies.StrategyTesting
import com.yang_bo.gezi.weakhead.Mode
import scala.util.Random

/** The law of the e-graph's write-back under a construction that converts terms
  * into native storages (`StorageConstruction.termConstruction`, a round's
  * `SaturationOptions.construction`). Generated programs over the naturals,
  * each literal written in the unique spelling
  * `successor (… (zero ∥ nat) …) ∥ nat` and given to the fixture's operations
  * that natives implement (`double`, `even`, `successor`), are run through the
  * native route's rounds (the type check, then the erasure) under the
  * conversion and as written. Derived before the run from the construction,
  * which converts a layer as it is built, every child first: no subterm of an
  * output under the conversion is a parallel that the encoding converts (no
  * plain twin of a storage), and every storage in it is the very object the
  * conversion gives for its view; no storage s of criterion T stands in it as
  * `s ∥ T` (the extraction never spells a pattern view, `EGraph.patternViews`);
  * the output holds at least one storage (the precondition that the law is not
  * vacuous); both rounds reach their fixed point; and the outputs under the
  * conversion and as written have the same normal forms under the JIT. Its
  * purpose is to catch a write-back that interns a plain twin of a storage,
  * which would give one term two objects within one configuration, and a
  * storage leaf that changes what a program reads.
  */
class StorageWriteBackLawTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  given com.yang_bo.gezi.ir.StorageAccess = StorageWriteBackLawTest.storageAccess

  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(60, "s")

  private lazy val library = NativesTesting.nativesOn
  private lazy val facts = BackendFacts.of(library)
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private type Term = Configured[encoding.type]

  private lazy val index: StandardLibraryIndex[encoding.type] =
    encoding.operations.index

  /** The saturation options of the encoding's configuration: the lemmas and
    * rules given, the baseline's lemma encoding, backend, indexer and
    * orientation compiler, and the construction.
    */
  private def optionsUnder[E <: StorageEncoding & Singleton](
      under: E,
      lemmas: Vector[com.yang_bo.gezi.ir.LemmaIdentifier],
      builtInRules: Set[BuiltInRule],
      budget: Int,
      construction: TermConstruction[E]
  ): SaturationOptions[E] =
    SaturationOptions[E](
      lemmas,
      builtInRules,
      budget,
      BaselineRounds.modules.lemmaEncoding,
      BaselineRounds.modules.backend,
      StandardIndexer.of[E],
      BaselineRounds.modules.orientationCompiler,
      MemoRetention.Kept,
      construction
    )

  /** The native route's rounds under the construction given: the type check and
    * the erasure, 600 instances each.
    */
  private def scheduleUnder(
      construction: TermConstruction[encoding.type]
  ): Vector[Round[encoding.type]] =
    NativeRouteCompilation.nativeRouteSchedule[encoding.type](
      index,
      BaselineRounds
        .lemmas(library, StrategyTesting.round("prolog_backend_type_check")),
      BaselineRounds
        .lemmas(library, StrategyTesting.round("occurrence_erasure")),
      600,
      RoundModules[encoding.type](
        StandardSaturator[encoding.type](_),
        CountedExtractor[encoding.type](
          NativeRouteCompilation.extraction,
          BaselineModules.table[encoding.type]
        ),
        BaselineRounds.modules.lemmaEncoding,
        StandardIndexer.of[encoding.type],
        BaselineRounds.modules.backend,
        BaselineRounds.modules.orientationCompiler,
        construction
      )
    )

  private lazy val asWritten: Vector[Round[encoding.type]] = scheduleUnder(
    TermConstruction(encoding)
  )

  private lazy val converting: Vector[Round[encoding.type]] =
    scheduleUnder(
      com.yang_bo.gezi.jit.ConvertedTermConstruction[encoding.type](encoding)(
        com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )

  private lazy val zero = libraryTerm[encoding.type]("zero")
  private lazy val successor = libraryTerm[encoding.type]("successor")
  private lazy val natType = libraryTerm[encoding.type]("nat_type")

  /** The natural in the unique spelling: each layer filtered by `nat_type`. */
  private def natural(count: Int): TermOf[Term] =
    (1 to count).foldLeft(zero ∥ natType)((inner, _) =>
      successor(inner) ∥ natType
    )

  private val operations: Vector[String] = Vector("double", "even", "successor")

  /** One of the library's operations on naturals that natives implement,
    * applied once or twice to a literal.
    */
  private def program(random: Random): TermOf[Term] =
    val first =
      libraryTerm[encoding.type](operations(random.nextInt(operations.size)))
    val applied = first(natural(random.nextInt(4)))
    if random.nextBoolean() then libraryTerm[encoding.type]("double")(applied)
    else applied

  /** The program of the library under no facts, crossed into the configuration.
    */
  private def programInput(program: TermOf[Term]): Term =
    StrategyTesting.programInputIn[encoding.type](library, program)

  private def scheduled(
      stop: StopSignal,
      rounds: Vector[Round[encoding.type]],
      input: Term
  ): Term =
    val run = Schedule.run(index, Vector(input), rounds, stop)
    run.records.foreach(record =>
      record.report match
        case FixpointReport(End.FixedPoint(_)) => ()
        case other                             => fail(s"a round ended $other")
    )
    run.outputs match
      case Vector(output) => output
      case other          => fail(s"the schedule gave ${other.size} outputs")

  /** Every subterm, each once, a storage's view not read. */
  private def subterms(root: Term): Vector[Term] =
    @scala.annotation.tailrec
    def walked(
        pending: List[Term],
        seen: Set[Term],
        found: Vector[Term]
    ): Vector[Term] = pending match
      case Nil                        => found
      case term :: rest if seen(term) => walked(rest, seen, found)
      case term :: rest               =>
        val children = term.layer match
          case _: com.yang_bo.gezi.ir.NativeStorage          => Nil
          case com.yang_bo.gezi.ir.Apply(function, argument) => List(function, argument)
          case com.yang_bo.gezi.ir.Parallel(left, right)     => List(left, right)
          case com.yang_bo.gezi.ir.Choice(left, right)       => List(left, right)
          case com.yang_bo.gezi.ir.Thunk(_, _, fillings)     => fillings.toList
          case _                                 => Nil
        walked(children ::: rest, seen + term, found :+ term)
    walked(List(root), Set.empty, Vector.empty)

  stoppableTest(
    "the write-back under the conversion interns no plain twin of a storage and reads what the written one reads"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261130)
    val storagesFound = (1 to 4).map { round =>
      val input = programInput(program(random))
      val converted = scheduled(stop, converting, input)
      val written = scheduled(stop, asWritten, input)
      val parts = subterms(converted)
      parts.foreach { term =>
        term.layer match
          case storage: com.yang_bo.gezi.ir.NativeStorage =>
            val com.yang_bo.gezi.ir.StorageView(value, criterion) =
              encoding.viewOf(storage): @unchecked
            val again = encoding.parallel(value, criterion)
            assert(
              Configured.same(again, term),
              s"round $round: the storage $storage is not the one its view converts to: $again"
            )
          case com.yang_bo.gezi.ir.Parallel(left, right) =>
            assert(
              encoding.operations
                .convertedValue(Value.of(left), Value.of(right))
                .isEmpty,
              s"round $round: a plain twin of a storage in the output: $term"
            )
            left.layer match
              case storage: com.yang_bo.gezi.ir.NativeStorage =>
                assert(
                  !Configured.same(encoding.criterionOf(storage), right),
                  s"round $round: a storage's pattern view spelled in the output: $term"
                )
              case _ => ()
          case _ => ()
      }
      val jit = Jit(NativesTesting.configurationOf(encoding))
      def normalForms(output: Term) =
        NativesTesting
          .normalFormsSpent(
            jit,
            Value.of(output),
            NativesTesting.normalFormLimit
          )
          .outcome
      assert(
        JitTesting.sameOutcomes(normalForms(converted), normalForms(written)),
        s"round $round"
      )
      parts.count(_.layer.isInstanceOf[com.yang_bo.gezi.ir.NativeStorage])
    }
    assert(
      storagesFound.sum > 0,
      s"no output held a storage: the law is vacuous ($storagesFound)"
    )
  }

  /** The law that the rounds read the storages they are given as leaves, never
    * their views: the native route's output under the conversion (its storages
    * made by the write-back) is run through the converting rounds again twice,
    * once with a construction whose capability reads native data only
    * (`StorageAccess.dataOnly`), under which a view read throws, and once with
    * one that reads views. Derived before the run from the gateway
    * (`Store.expanded` keeps such a storage as a leaf by a class test), the
    * pattern view (made from the criterion, not the view) and the walks that
    * stop at a leaf (`heldAsLeaf`): no round throws; the two outputs are one
    * term, since the graph sees the same leaves, hash codes and criteria; and
    * some input holds a storage leaf (the precondition that the law is not
    * vacuous). No lemma instance of these rounds binds a leaf's class: HM types
    * a literal by its constructors, which a storage leaf hides, until the
    * reverse lemma that types `x ∥ T` by T alone; `PatternViewMatchingLawTest`
    * checks the matching through a pattern view. TODO: require such an instance
    * once that lemma is in the fixture's rounds
    * (https://github.com/Atry/private-overlay/issues/2188). Its purpose is to
    * catch a traversal of a round, its extraction or its write-back that reads
    * a storage leaf's view, which materializes the value the storage exists not
    * to materialize.
    */
  stoppableTest(
    "the rounds given storage leaves read none of their views and write back what they write back reading views"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261131)
    val dataOnly = scheduleUnder(
      com.yang_bo.gezi.jit.ConvertedTermConstruction[encoding.type](encoding)(
        com.yang_bo.gezi.ir.StorageAccess.dataOnly()
      )
    )
    val leafCounts = (1 to 4).map { round =>
      val converted = scheduled(stop, converting, programInput(program(random)))
      val withDataOnly = scheduled(stop, dataOnly, converted)
      val readingViews = scheduled(stop, converting, converted)
      assert(Configured.same(withDataOnly, readingViews), s"round $round")
      subterms(converted).count(term =>
        term.layer match
          case storage: com.yang_bo.gezi.ir.NativeStorage => storage.leafInEGraph
          case _                              => false
      )
    }
    assert(
      leafCounts.sum > 0,
      s"no input held a storage leaf: the law is vacuous ($leafCounts)"
    )
  }

  /** The law that storage leaves lose no rewrite the rounds make: a generated
    * program is run through the converting rounds and then the rounds as
    * written in the encoding, its literals storages and its outputs' storages
    * leaves of the graph, and the same program through the same rounds under no
    * facts, its literals spelled out. Derived before the run from the rounds'
    * lemmas, none of which reads a literal's constructors (B2's audit of the
    * typed rounds): the output under no facts, crossed into the encoding
    * (`crossedAllFromNoFacts`, which builds each unique spelling's storage), is
    * the encoding's output; and the encoding's intermediate output holds
    * storage leaves (the precondition that the law is not vacuous). No lemma
    * instance of these rounds binds a leaf's class, for the reason the law
    * above gives, so this shows that the rounds' rewrites inside the
    * spelled-out literals, if any, change nothing the leaves lose. TODO:
    * require an instance on a leaf's class once the reverse lemma is in the
    * fixture's rounds (https://github.com/Atry/private-overlay/issues/2188).
    * Its purpose is to catch a storage leaf that hides a match the spelled-out
    * term has, the cost of keeping a storage as a leaf.
    */
  stoppableTest(
    "the rounds given storage leaves write back what they write back given their Scott spelling"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261132)
    val noFactsIndex = StandardLibraryIndex.crossed(library.index, NoFacts)
    val leafCounts = (1 to 4).map { round =>
      val seed = random.nextLong()
      val converted =
        scheduled(stop, converting, programIn[encoding.type](seed))
      val withLeaves = scheduled(stop, asWritten, converted)
      val spelled = programIn[NoFacts.type](seed)(using NoFacts)
      val withSpelling = scheduledIn(
        stop,
        withoutFacts,
        noFactsIndex,
        scheduledIn(stop, withoutFacts, noFactsIndex, spelled)
      )
      val crossed =
        encoding.crossedAllFromNoFacts(Vector(withSpelling))(withSpelling)
      assert(Configured.same(crossed, withLeaves), s"round $round")
      subterms(converted).count(term =>
        term.layer match
          case storage: com.yang_bo.gezi.ir.NativeStorage => storage.leafInEGraph
          case _                              => false
      )
    }
    assert(
      leafCounts.sum > 0,
      s"no output held a storage leaf: the law is vacuous ($leafCounts)"
    )
  }

  /** The run of a round with no lemma and only the rules given, within the
    * budget given or the round's own 600, under the construction of the
    * configuration, on the input.
    */
  private def ruleRun(
      stop: StopSignal,
      rules: Set[BuiltInRule],
      budget: Option[Int],
      input: Term
  ): Run[encoding.type] =
    StandardSaturator[encoding.type](
      optionsUnder[encoding.type](
        encoding,
        Vector.empty,
        rules,
        budget.getOrElse(600),
        TermConstruction(encoding)
      )
    )
      .saturated(index, Vector(input), explained = false, stop)

  /** The storages' unions with their views in the graph a run left. */
  private def storageViewUnions(graph: com.yang_bo.gezi.egraph.EGraph[encoding.type]): Int =
    graph.unions.count(_.justification match
      case com.yang_bo.gezi.egraph.Justification.StorageView(_) => true
      case _                                        => false)

  /** The natural's storage under the encoding, as a term. */
  private def naturalStorageUnder[E <: StorageEncoding & Singleton](
      under: E,
      value: Int
  ): Configured[E] =
    under.operations.stored(
      JitTesting.storageOf(under)(
        Representation.BigInteger,
        NativeValue.Natural(BigInt(value))
      )
    )

  private def naturalStorage(value: Int): Term =
    naturalStorageUnder(encoding, value)

  /** filter_by, `λt x. x ∥ t`, in the configuration: a thunk whose body's
    * parallel is a code's, which no construction converts, so that the β rule
    * makes `x ∥ t` a node of the graph over the classes of its sides, the
    * parallel a term of the configuration cannot be written as when it is the
    * unique spelling of a storage.
    */
  private def filterByIn[E <: StorageEncoding & Singleton](
      under: E
  ): Configured[E] =
    given E = under
    Defunctionalization.thunkInstruction[E](
      NativesTesting.filterBy.deBruijnTerm(Map.empty)
    )

  /** `filter_by criterion value`, which one β step makes the node
    * `value ∥ criterion`.
    */
  private def filteredIn[E <: StorageEncoding & Singleton](
      under: E
  )(value: Configured[E], criterion: Configured[E]): Configured[E] =
    under.application(under.application(filterByIn(under), criterion), value)

  private def filtered(value: Term, criterion: Term): Term =
    filteredIn(encoding)(value, criterion)

  /** The criterion of the representation under the encoding, as a term: a
    * criterion is a closed term of no storage.
    */
  private def criterionTermIn[E <: StorageEncoding & Singleton](under: E)(
      representation: Representation[JitValue[E]]
  ): Configured[E] =
    given E = under
    Closed
      .configured(JitTesting.criterionOf(under)(representation))
      .getOrElse(
        throw IllegalStateException(s"a criterion is closed: $representation")
      )

  /** A constructor's define of the facts, as a term of the encoding. */
  private def constructorTerm(native: NativeName): Term =
    Configured.fromPure(encoding)(facts.constructorDefine(native))

  /** The facts of tests/library_fixtures/binary_natural_backend.lambdalattice,
    * whose binary naturals take the canonicity as a parameter.
    */
  private lazy val binaryFacts =
    BackendFacts.of(
      com.yang_bo.gezi.standardlibrary.LibraryFiles.compiled(
        "tests/library_fixtures/binary_natural_backend.lambdalattice",
        Vector(BackendChecks)
      )
    )

  private lazy val binaryEncoding: StorageEncoding = binaryFacts.storageEncoding

  /** The native route's rounds under no facts, as written: the same lemmas over
    * the library read with no facts.
    */
  private lazy val withoutFacts: Vector[Round[NoFacts.type]] =
    BaselineRounds.nativeRouteSchedule[NoFacts.type](
      library,
      StrategyTesting.round("prolog_backend_type_check"),
      600
    )(using NoFacts)

  /** The schedule's one output in the configuration, every round ended at its
    * fixed point.
    */
  private def scheduledIn[E <: NativeSpecializer & Singleton](
      stop: StopSignal,
      rounds: Vector[Round[E]],
      indexIn: StandardLibraryIndex[E],
      input: Configured[E]
  ): Configured[E] =
    val run = Schedule.run(indexIn, Vector(input), rounds, stop)
    run.records.foreach(record =>
      record.report match
        case FixpointReport(End.FixedPoint(_)) => ()
        case other                             => fail(s"a round ended $other")
    )
    run.outputs match
      case Vector(output) => output
      case other          => fail(s"the schedule gave ${other.size} outputs")

  /** The generated program of the seed in the configuration in scope, its
    * natural written in the unique spelling.
    */
  private def programIn[E <: NativeSpecializer & Singleton](seed: Long)(using
      E
  ): Configured[E] =
    val random = Random(seed)
    val zeroIn = libraryTerm[E]("zero")
    val successorIn = libraryTerm[E]("successor")
    val natTypeIn = libraryTerm[E]("nat_type")
    def naturalIn(count: Int): TermOf[Configured[E]] =
      (1 to count).foldLeft(zeroIn ∥ natTypeIn)((inner, _) =>
        successorIn(inner) ∥ natTypeIn
      )
    val first = libraryTerm[E](operations(random.nextInt(operations.size)))
    val applied = first(naturalIn(random.nextInt(4)))
    StrategyTesting.programInputIn[E](
      library,
      if random.nextBoolean() then libraryTerm[E]("double")(applied)
      else applied
    )

  /** The native route's rounds as written with the expansion direction of the
    * storage's view enabled, each round's saturator and extractor.
    */
  private lazy val expanding: Vector[
    (StandardSaturator[encoding.type], CountedExtractor[encoding.type])
  ] =
    Vector("prolog_backend_type_check", "occurrence_erasure").map(round =>
      (
        StandardSaturator[encoding.type](
          optionsUnder[encoding.type](
            encoding,
            BaselineRounds.lemmas(library, StrategyTesting.round(round)),
            BuiltInRule.beforeOptIn + BuiltInRule.StorageView,
            600,
            TermConstruction(encoding)
          )
        ),
        CountedExtractor[encoding.type](
          NativeRouteCompilation.extraction,
          BaselineModules.table[encoding.type]
        )
      )
    )

  /** The law of the expansion's count: a choice of generated natural storages
    * (a natural's view `successor (m ∥ nat) ∥ nat` holds the storage of its
    * predecessor m, zero's view holds none), saturated by a round with no lemma
    * and only the expansion direction of the storage's view
    * (`BuiltInRule.StorageView`). Derived before the run: every storage reached
    * through the views becomes a leaf once and is united with its view once, so
    * the storages' unions with their views are the naturals from the greatest
    * down to zero, its value plus one; the round counts each as one instance
    * and makes no other; and none of it happens with the rule not enabled.
    * Within a budget below that count the run ends with the budget exhausted at
    * exactly the budget, each expansion an instance; and a natural of 30,000
    * nested storages expands to its fixed point, the loop taking one leaf at a
    * time with no stack growing with the nesting. Its purpose is to catch an
    * expansion that misses a nested storage, expands one twice, is not bounded
    * by the budget, recurses with the nesting, or runs in a round that does not
    * enable it.
    */
  stoppableTest(
    "the storage view's expansion unites each storage reached once with its view, one instance each"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261134)
    (1 to 8).foreach { round =>
      val values =
        Vector.fill(1 + random.nextInt(4))(random.nextInt(12)).distinct
      val input =
        values.map(naturalStorage(_)).reduceRight(encoding.choice(_, _))
      val expanded =
        ruleRun(stop, Set(com.yang_bo.gezi.ir.BuiltInRule.StorageView), None, input)
      val notExpanded = ruleRun(stop, Set.empty, None, input)
      val cut = ruleRun(
        stop,
        Set(com.yang_bo.gezi.ir.BuiltInRule.StorageView),
        Some(values.max),
        input
      )
      assertEquals(
        (
          storageViewUnions(expanded.graph),
          expanded.graph.instances,
          storageViewUnions(notExpanded.graph),
          notExpanded.graph.instances,
          values.max == 0 || (cut.end == com.yang_bo.gezi.saturation.End.BudgetExhausted(
            values.max
          ) && storageViewUnions(cut.graph) == values.max)
        ),
        (values.max + 1, values.max + 1, 0, 0, true),
        s"round $round, values $values"
      )
    }
    val deep = ruleRun(
      stop,
      Set(com.yang_bo.gezi.ir.BuiltInRule.StorageView),
      Some(40000),
      naturalStorage(30000)
    )
    assertEquals(
      (deep.end, storageViewUnions(deep.graph)),
      (com.yang_bo.gezi.saturation.End.FixedPoint(30001), 30001)
    )
  }

  /** The law that the expansion direction loses nothing the Scott spelling has:
    * a generated program is run through the converting rounds and then the
    * rounds as written in the encoding with the expansion direction enabled,
    * and the same program through the rounds under no facts, its literals
    * spelled out. Derived before the run: with the expansion, each storage
    * leaf's class holds the nodes of its view, which are the nodes the
    * spelled-out term has, so the rounds match what they match on the spelling;
    * the extraction reads a leaf or its view's nodes, which spell the same
    * term, and the rounds' rewrites inside a spelled-out literal change nothing
    * extracted (the law above); so the output under no facts, crossed into the
    * encoding, is the encoding's output; and some round expands a storage (the
    * precondition that the law is not vacuous). Its purpose is to catch an
    * expansion that adds a view other than the storage's, or unites it with
    * another class.
    */
  stoppableTest(
    "the rounds given storage leaves with the expansion write back what they write back given their Scott spelling"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261133)
    val noFactsIndex = StandardLibraryIndex.crossed(library.index, NoFacts)
    val expansions = (1 to 4).map { round =>
      val seed = random.nextLong()
      val converted =
        scheduled(stop, converting, programIn[encoding.type](seed))
      val (withExpansion, count) = expanding.foldLeft((converted, 0)) {
        case ((current, sofar), (saturator, extractor)) =>
          val run =
            saturator.saturated(index, Vector(current), explained = false, stop)
          extractor.extracted(
            index,
            run.graph,
            run.inputNodes,
            Vector(current),
            stop
          ) match
            case Vector(output) =>
              (output, sofar + storageViewUnions(run.graph))
            case outputs =>
              fail(s"one output for one input, not ${outputs.size}")
      }
      val spelled = programIn[NoFacts.type](seed)(using NoFacts)
      val withSpelling = scheduledIn(
        stop,
        withoutFacts,
        noFactsIndex,
        scheduledIn(stop, withoutFacts, noFactsIndex, spelled)
      )
      val crossed =
        encoding.crossedAllFromNoFacts(Vector(withSpelling))(withSpelling)
      assert(Configured.same(crossed, withExpansion), s"round $round")
      count
    }
    assert(
      expansions.sum > 0,
      s"no round expanded a storage: the law is vacuous ($expansions)"
    )
  }

  /** The article of the equation `left = right`, the two terms joined in the
    * graph a round with no lemma left on the inputs, written by the article
    * writer and checked by the opentheory tool: the tool's status and errors.
    */
  private def equationChecked(
      stop: StopSignal,
      rules: Set[BuiltInRule],
      inputs: Vector[Term],
      left: Term,
      right: Term
  ): (Int, String) =
    val run = StandardSaturator[encoding.type](
      optionsUnder[encoding.type](
        encoding,
        Vector.empty,
        rules,
        600,
        TermConstruction(encoding)
      )
    )
      .saturated(index, inputs, explained = true, stop)
    val proof = com.yang_bo.gezi.strategies.GraphProof.proof(
      run.graph,
      Vector((left, right)),
      Vector.empty
    )
    com.yang_bo.gezi.proofs.ProofTestFiles.textChecked(
      com.yang_bo.gezi.proofs.OpentheoryArticle.text(index, left, right, proof)
    )

  /** The law that the article proves the unions of storage leaves: for a
    * generated natural storage s of view `v ∥ T`, the article of
    * `filter_by T s = s` in the graph of that input with no lemma and the β
    * rule alone, and the article of `filter_by T v = s` in the graph of the
    * inputs s and `filter_by T v` with no lemma, the β rule and the expansion
    * direction. Derived before the run: one β step makes `s ∥ T`, the leaf's
    * pattern view (one layer over the same classes), united with the leaf; one
    * β step makes `v ∥ T` over the nodes the expansion adds for the leaf's view
    * (its nested storages leaves with their own pattern views), united with the
    * leaf; the β step is proved by the β rule, the pattern view's union by (4)
    * and the idempotence of ∥ from (6) and (5), and the storage view's by the
    * congruence of the parallel, the article writing a storage as its view; so
    * the opentheory tool accepts both articles. The equations are stated, not
    * read off an extraction, which may keep an input's own spelling. A parallel
    * `s ∥ T` or `v ∥ T` written as a term of the encoding is s itself (the
    * specializer builds the storage of a unique spelling), so each is reached
    * through `filter_by`. Its purpose is to catch an article that cannot prove,
    * or proves wrongly, a union of a storage leaf.
    */
  stoppableTest(
    "the articles of a storage leaf's pattern view and of its view are accepted by the opentheory tool"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261135)
    (1 to 3).foreach { round =>
      val value = random.nextInt(6)
      val storage = naturalStorage(value)
      val view = storage.layer match
        case stored: com.yang_bo.gezi.ir.NativeStorage =>
          encoding.viewOf(stored)(using com.yang_bo.gezi.ir.StorageAccess.granted())
        case other => fail(s"no storage of a natural: $other")
      val throughPattern = filtered(storage, view.criterion)
      val throughView = filtered(view.value, view.criterion)
      assertEquals(
        (
          equationChecked(
            stop,
            Set(BuiltInRule.Beta),
            Vector(throughPattern),
            throughPattern,
            storage
          ),
          equationChecked(
            stop,
            Set(BuiltInRule.Beta, BuiltInRule.StorageView),
            Vector(storage, throughView),
            throughView,
            storage
          )
        ),
        ((0, ""), (0, "")),
        s"round $round, natural $value"
      )
    }
  }

  /** The law of the construction direction: a list cell in the unique spelling
    * `cons (h ∥ E) (s ∥ list_type E) ∥ list_type E`, reached as
    * `filter_by L (cons h s)` (h a generated natural's storage, s the empty
    * list's storage, L the list's criterion), run through a round with no lemma
    * and the β rule alone whose write-back converts, with a capability that
    * reads native data only, so that a view read throws. Derived before the
    * run: one β step makes the cell's parallel, one layer over the classes of
    * h's leaf and s; the write-back builds the output through the round's
    * construction, one layer over the children it built first, so the output is
    * the cell's storage, whose item and tail are h and s themselves; nothing
    * reads h's view (the graph keeps h as a leaf, and the conversion reads a
    * field's class, criterion and hash code). Its purpose is to catch a
    * construction that expands a field storage, copies it, or leaves the cell a
    * plain parallel, so that a storage built over storages in the graph does
    * not stay one.
    */
  stoppableTest(
    "the write-back builds a cell over storage leaves as the cell's storage, its fields the leaves themselves"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261136)
    val listRepresentation = Representation.ListOf(
      JitTesting.criterionOf(encoding)(Representation.BigInteger)
    )
    val listCriterion = criterionTermIn(encoding)(listRepresentation)
    val empty = encoding.operations.stored(
      JitTesting.storageOf(encoding)(
        listRepresentation,
        NativeValue.Listed(
          com.yang_bo.gezi.weakhead.ListRepresentation.Items(0, Vector.empty)
        )
      )
    )
    val cons = Configured.fromPure(encoding)(facts.cons)
    val saturator = StandardSaturator[encoding.type](
      optionsUnder[encoding.type](
        encoding,
        Vector.empty,
        Set(BuiltInRule.Beta),
        600,
        com.yang_bo.gezi.jit.ConvertedTermConstruction[encoding.type](encoding)(
          com.yang_bo.gezi.ir.StorageAccess.dataOnly()
        )
      )
    )
    val extractor = CountedExtractor[encoding.type](
      NativeRouteCompilation.extraction,
      BaselineModules.table[encoding.type]
    )
    (1 to 4).foreach { round =>
      val item = naturalStorage(random.nextInt(1000))
      val input = filtered(
        encoding.application(encoding.application(cons, item), empty),
        listCriterion
      )
      val run =
        saturator.saturated(index, Vector(input), explained = false, stop)
      val cell = encoding.operations.stored(
        JitTesting.storageOf(encoding)(
          listRepresentation,
          NativeValue.Listed(
            com.yang_bo.gezi.weakhead.ListRepresentation
              .Cell(Value.of(item), Value.of(empty))
          )
        )
      )
      extractor.extracted(
        index,
        run.graph,
        run.inputNodes,
        Vector(input),
        stop
      ) match
        case Vector(output) =>
          assert(
            Configured.same(output, cell),
            s"round $round: the output is no cell's storage over the leaves: $output"
          )
        case outputs =>
          fail(s"round $round: one output for one input, not ${outputs.size}")
    }
  }

  /** The run of a round with no lemma and no rule, as written or under the
    * converting construction, on the input.
    */
  private def constructionRun[E <: StorageEncoding & Singleton](
      under: E,
      stop: StopSignal,
      converting: Boolean,
      input: Configured[E],
      rules: Set[BuiltInRule] = Set.empty,
      explained: Boolean = false
  ): Run[E] =
    val construction: TermConstruction[E] =
      if converting then
        com.yang_bo.gezi.jit.ConvertedTermConstruction[E](under)(
          com.yang_bo.gezi.ir.StorageAccess.granted()
        )
      else TermConstruction(under)
    StandardSaturator[E](
      optionsUnder[E](under, Vector.empty, rules, 600, construction)
    )
      .saturated(under.operations.index, Vector(input), explained, stop)

  /** The law of the construction one layer up: `successor s ∥ N`, reached as
    * `filter_by N (successor s)`, s the generated natural storage `Natural(k)`
    * (its view `successor … ∥ N`, the unique spelling), and the same nested
    * twice, are saturated by a round with no lemma and the β rule alone under
    * the converting construction, and as written. Derived before the run: the β
    * step makes the parallel, which is queued when it is made; its criterion's
    * class is N's node, its left side's class holds successor's define applied
    * to s's class, which holds the leaf s; so the construction builds
    * `Natural(k + 1)`, adds it as a leaf and unites it with its view, which is
    * that parallel itself (the view's nodes are the β step's, shared): one
    * union by the storage's view, one instance (a β step is no instance).
    * Nested, the inner class's new leaf queues the outer parallel through the
    * application above it, so `Natural(k + 2)` follows: two unions, two
    * instances. As written, nothing is built. Its purpose is to catch a
    * construction that misses its parallel, builds over the wrong class, unites
    * the storage elsewhere than with its view, is not counted, or runs where
    * the construction converts nothing.
    */
  stoppableTest(
    "the converting construction builds a natural one layer up from its field's storage leaf, nested twice"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261137)
    val successorDefine =
      constructorTerm(NativeName.Constructor(BigIntegerFamily.identity, 1))
    val natural = criterionTermIn(encoding)(Representation.BigInteger)
    def layer(inner: Term): Term =
      filtered(encoding.application(successorDefine, inner), natural)
    (1 to 4).foreach { round =>
      val value = random.nextInt(20)
      val once = layer(naturalStorage(value))
      val twice = layer(once)
      def observed(converting: Boolean, input: Term, expected: Int) =
        val graph = constructionRun(
          encoding,
          stop,
          converting,
          input,
          Set(BuiltInRule.Beta)
        ).graph
        val inputRoot = graph.root(
          graph.instructionNode(input).getOrElse(fail(s"no node of $input"))
        )
        val built = graph
          .instructionNode(naturalStorage(value + expected))
          .map(graph.root)
        (storageViewUnions(graph), graph.instances, built.contains(inputRoot))
      assertEquals(
        (
          observed(true, once, 1),
          observed(true, twice, 2),
          observed(false, once, 1),
          observed(false, twice, 2)
        ),
        ((1, 1, true), (2, 2, true), (0, 0, false), (0, 0, false)),
        s"round $round, natural $value"
      )
    }
  }

  /** The law of the construction's base case: a constant of a converted family
    * filtered by its criterion, `zero ∥ N`, `true ∥ B` or `false ∥ B`, reached
    * as `filter_by N zero` and so on, and `successor (zero ∥ N) ∥ N` above it,
    * saturated by a round with no lemma and the β rule alone under the
    * converting construction, and as written. Derived before the run: the β
    * step makes the parallel, which is queued when it is made; its left side's
    * class is the constructor's define, a spine of no field; so the
    * construction builds the constant's storage, adds it as a leaf and unites
    * it with the parallel, its view: one union by the storage's view, one
    * instance; with successor above it, the new leaf queues the outer parallel,
    * so `Natural(1)` follows: two unions, two instances. As written, nothing is
    * built. Its purpose is to catch a construction that builds no storage of a
    * constructor of no field, which leaves a written literal with no first
    * storage to build the next layer on.
    */
  stoppableTest(
    "the converting construction builds a constant's storage from its parallel, and the layer above it"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val zeroDefine =
      constructorTerm(NativeName.Constructor(BigIntegerFamily.identity, 0))
    val successorDefine =
      constructorTerm(NativeName.Constructor(BigIntegerFamily.identity, 1))
    val natural = criterionTermIn(encoding)(Representation.BigInteger)
    val boolean = criterionTermIn(encoding)(Representation.Truth)
    val truthDefine =
      constructorTerm(NativeName.Constructor(BooleanFamily.identity, 0))
    val falsityDefine =
      constructorTerm(NativeName.Constructor(BooleanFamily.identity, 1))
    val zeroLayer = filtered(zeroDefine, natural)
    val cases = Vector(
      (zeroLayer, naturalStorage(0), 1),
      (
        filtered(encoding.application(successorDefine, zeroLayer), natural),
        naturalStorage(1),
        2
      ),
      (filtered(truthDefine, boolean), truthStorage(true), 1),
      (filtered(falsityDefine, boolean), truthStorage(false), 1)
    )
    cases.foreach { (input, storage, expected) =>
      def observed(converting: Boolean) =
        val graph = constructionRun(
          encoding,
          stop,
          converting,
          input,
          Set(BuiltInRule.Beta)
        ).graph
        val inputRoot = graph.root(
          graph.instructionNode(input).getOrElse(fail(s"no node of $input"))
        )
        (
          storageViewUnions(graph),
          graph.instances,
          graph.instructionNode(storage).map(graph.root).contains(inputRoot)
        )
      assertEquals(
        (observed(true), observed(false)),
        ((expected, expected, true), (0, 0, false)),
        s"$input"
      )
    }
  }

  /** The law of the construction of a family with a finite value parameter in
    * the graph: a natural n in the unique spelling at P (zero
    * `binary_zero ∥ T`, 2h `binary_even (h ∥ binary_set false) ∥ T`, 2h + 1
    * `binary_odd (h ∥ binary_set true) ∥ T`, the criteria spelled with the
    * library's own terms), each parallel reached through `filter_by`, for n = 0
    * at true, a number 2^k − 1, an even number and one of mixed bits, at both P
    * where n is a member, saturated by a round with no lemma and the β rule
    * alone under the converting construction. Derived before the run: the
    * innermost parallel is a constant's, which the construction builds; each
    * layer above then finds its field's class holding the storage leaf below
    * and builds its own, one union by the storage's view and one instance a
    * layer (a β step is no instance); so the input's class holds the storage of
    * n, and the instances are the layers, n's bit length plus 1 for n > 0 and 1
    * for 0. Its purpose is to catch a construction that stops at a layer of the
    * positive naturals or builds none under a criterion with a parameter.
    */
  stoppableTest(
    "the converting construction builds a binary natural layer by layer under binary_set P"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261138)
    given binaryEncoding.type = binaryEncoding
    def term(key: String): Configured[binaryEncoding.type] =
      JitTesting.libraryInstruction[binaryEncoding.type](key)
    def set(canonical: Boolean): Configured[binaryEncoding.type] =
      binaryEncoding.application(
        term("binary_set"),
        term(if canonical then "true" else "false")
      )
    def written(
        value: BigInt,
        canonical: Boolean
    ): Configured[binaryEncoding.type] =
      val layer =
        if value == 0 then term("binary_zero")
        else if value.testBit(0) then
          binaryEncoding.application(
            term("binary_odd"),
            written(value >> 1, true)
          )
        else
          binaryEncoding.application(
            term("binary_even"),
            written(value >> 1, false)
          )
      filteredIn(binaryEncoding)(layer, set(canonical))
    val values = Vector(
      BigInt(0),
      (BigInt(1) << (1 + random.nextInt(6))) - 1,
      BigInt(2 + 2 * random.nextInt(500)),
      BigInt(random.nextInt(100000))
    )
    for
      value <- values; canonical <- Vector(true, false)
      if canonical || value > 0
    do
      val input = written(value, canonical)
      val graph = constructionRun(
        binaryEncoding,
        stop,
        true,
        input,
        Set(BuiltInRule.Beta)
      ).graph
      val representation = if canonical then BinaryNaturalNatives.canonical
      else BinaryNaturalNatives.positive
      val storage = binaryEncoding.operations.stored(
        JitTesting
          .storageOf(binaryEncoding)(representation, BinaryNatural(value))
      )
      val inputRoot = graph.root(
        graph.instructionNode(input).getOrElse(fail(s"no node of $input"))
      )
      val layers = if value == 0 then 1 else value.bitLength + 1
      assertEquals(
        (
          graph.instructionNode(storage).map(graph.root).contains(inputRoot),
          graph.instances
        ),
        (true, layers),
        s"$value at $canonical"
      )
  }

  /** The unions by a native's fold in the graph a run left. */
  private def foldingUnions[E <: StorageEncoding & Singleton](
      graph: com.yang_bo.gezi.egraph.EGraph[E]
  ): Int =
    graph.unions.count(_.justification match
      case com.yang_bo.gezi.egraph.Justification.Folding(_, _, _) => true
      case _                                          => false)

  /** The boolean's storage under the fixture's facts, as a term. */
  private def truthStorage(value: Boolean): Term =
    encoding.operations.stored(
      JitTesting
        .storageOf(encoding)(Representation.Truth, NativeValue.Truth(value))
    )

  /** The law of folding: `double s` and `even s`, s the generated natural
    * storage `Natural(k)`, written as plain applications of the library's
    * defines bound to the natives `natural_double` and `natural_even`, are
    * saturated by a round with no lemma and no rule under the converting
    * construction. Derived before the run: each application is queued when it
    * is made; its function's class is the bound define's node; its argument's
    * class holds the leaf s, a storage of the native's parameter place
    * (`big_integer`); so the native is called once and its result, the storage
    * `Natural(2k)` or `Truth(k even)`, is added as a leaf and united with the
    * application: one union by the fold, one instance. No fold where the
    * argument is a choice of two naturals (no storage leaf in its class), where
    * it is a boolean (not the place's representation), as written, or where
    * `double`'s native declares no result filter (the fixture's facts with
    * `natural_double`'s result place a list's tail, the argument a storage
    * under those facts; the same facts with the native unchanged fold once, so
    * the encoding is not what refuses). The fold's article, the native's
    * equation imported as an axiom (`Axiom.Native`), is accepted by the
    * opentheory tool. For the chain `double (double s)` the inner fold reads
    * `double` on s and the outer one `double` on the inner result's storage
    * `Natural(2k)`, the leaf the inner fold put in its argument's class, so the
    * two folds record exactly those instances and the chain's article, whose
    * axioms state them, is accepted; its trace has the two folds as its two
    * commands, each a native value (`TraceCommand.Native`), the last putting
    * `Natural(4k)` at the root, in the replay's spelling
    * (`ReplaySpelling.term`, a storage written as its view). Its purpose is to
    * catch a fold that calls a native on a value outside its places, adds an
    * answer at a choice, unites the result elsewhere than with its application,
    * or writes an article the tool refuses.
    */
  stoppableTest(
    "the converting construction folds a native on its arguments' storage leaves, and nowhere else"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261138)
    val double = JitTesting.libraryInstruction[encoding.type]("double")
    val even = JitTesting.libraryInstruction[encoding.type]("even")
    (1 to 4).foreach { round =>
      val (value, other) = (random.nextInt(30), random.nextInt(30))
      def folded(converting: Boolean, input: Term, expected: Term) =
        val graph = constructionRun(encoding, stop, converting, input).graph
        val inputRoot = graph.root(
          graph.instructionNode(input).getOrElse(fail(s"no node of $input"))
        )
        (
          foldingUnions(graph),
          graph.instructionNode(expected).map(graph.root).contains(inputRoot)
        )
      val doubled = encoding.application(double, naturalStorage(value))
      val evened = encoding.application(even, naturalStorage(value))
      val chosen = encoding.application(
        double,
        encoding.choice(
          naturalStorage(value),
          naturalStorage(value + 1 + other)
        )
      )
      val mismatched =
        encoding.application(double, truthStorage(value % 2 == 0))
      val backend = facts.nativeBackend
      val doubleName = NativeName.Function("natural_double")
      val doubleNative = backend.natives.getOrElse(
        doubleName,
        fail("no natural_double in the fixture's backend")
      )
      def doubledUnder(native: Native) =
        val under = facts.copy(nativeBackend =
          backend.copy(natives = backend.natives.updated(doubleName, native))
        )
        val underEncoding: StorageEncoding = under.storageEncoding
        given underEncoding.type = underEncoding
        foldingUnions(
          constructionRun(
            underEncoding,
            stop,
            true,
            underEncoding.application(
              JitTesting.libraryInstruction[underEncoding.type]("double"),
              naturalStorageUnder(underEncoding, value)
            )
          ).graph
        )
      assertEquals(
        (
          folded(true, doubled, naturalStorage(2 * value)),
          folded(true, evened, truthStorage(value % 2 == 0)),
          foldingUnions(constructionRun(encoding, stop, true, chosen).graph),
          foldingUnions(
            constructionRun(encoding, stop, true, mismatched).graph
          ),
          folded(false, doubled, naturalStorage(2 * value))._1,
          doubledUnder(doubleNative),
          doubledUnder(doubleNative.copy(result = NativePlace.Tail))
        ),
        ((1, true), (1, true), 0, 0, 0, 1, 0),
        s"round $round, natural $value"
      )
      val run = constructionRun(encoding, stop, true, doubled, explained = true)
      val proof = com.yang_bo.gezi.strategies.GraphProof.proof(
        run.graph,
        Vector((doubled, naturalStorage(2 * value))),
        Vector.empty
      )
      assertEquals(
        com.yang_bo.gezi.proofs.ProofTestFiles.textChecked(
          com.yang_bo.gezi.proofs.OpentheoryArticle
            .text(index, doubled, naturalStorage(2 * value), proof)
        ),
        (0, ""),
        s"round $round: the fold's article"
      )
      val chain = encoding.application(double, doubled)
      val chainRun =
        constructionRun(encoding, stop, true, chain, explained = true)
      val chainGraph = chainRun.graph
      def rootOf(term: Term): Int = chainGraph.root(
        chainGraph.instructionNode(term).getOrElse(fail(s"no node of $term"))
      )
      // A fold's record names its define and its arguments by their nodes: the classes of the terms are compared.
      val instances = chainGraph.unions
        .collect(_.justification match
          case com.yang_bo.gezi.egraph.Justification.Folding(native, define, arguments) =>
            (native, chainGraph.root(define), arguments.map(chainGraph.root)))
        .toSet
      val chainProof = com.yang_bo.gezi.strategies.GraphProof.proof(
        chainGraph,
        Vector((chain, naturalStorage(4 * value))),
        Vector.empty
      )
      val trace = com.yang_bo.gezi.proofs.RewriteTrace.trace(
        com.yang_bo.gezi.proofs.OpentheoryArticle
          .derivation(index, chain, naturalStorage(4 * value), chainProof)
      )
      val replayed = trace.replayed(chain).flatten
      assertEquals(
        (
          instances,
          com.yang_bo.gezi.proofs.ProofTestFiles.textChecked(
            com.yang_bo.gezi.proofs.OpentheoryArticle
              .text(index, chain, naturalStorage(4 * value), chainProof)
          ),
          trace.rounds.flatten.map(_.getClass.getSimpleName)
        ),
        (
          Set(
            (
              "natural_double",
              rootOf(double),
              Vector(rootOf(naturalStorage(value)))
            ),
            (
              "natural_double",
              rootOf(double),
              Vector(rootOf(naturalStorage(2 * value)))
            )
          ),
          (0, ""),
          Vector("Native", "Native")
        ),
        s"round $round: the chain's folds and article"
      )
      assert(
        replayed.lastOption.exists(step =>
          Configured.same(
            step.replacement,
            com.yang_bo.gezi.rewritetrace.ReplaySpelling.term(naturalStorage(4 * value))
          )
        ),
        s"round $round: the chain's last replacement"
      )
    }
  }

  /** The law of the obligation the fold trusts of the fixture's folded natives,
    * `native = define` on single values, checked independently of the native
    * (the natives of the entries' facts are checked by their own laws,
    * `wren_binary_equality` by NarrowNativesCorporaLawTest): the tabling weak
    * head reads `double n` and `even n`, n a generated Scott numeral with no
    * filter, to the normal forms of the numeral of 2n and of the boolean of n's
    * parity, written with the library's zero, successor, true and false. Its
    * purpose is to catch a native whose binding states an equation its define
    * does not have, which a fold would merge into the graph.
    */
  test(
    "the fixture's folded natives compute what their defines compute on single values"
  ) {
    val random = Random(20261139)
    def numeral(count: Int): TermOf[Term] =
      (1 to count).foldLeft(zero)((inner, _) => successor(inner))
    def normalForms(term: TermOf[Term]) =
      NativesTesting
        .normalFormsSpent(
          Mode.TablingWeakHead,
          JitTesting.plainConfiguration(encoding),
          JitTesting.termValue(term),
          NativesTesting.normalFormLimit
        )
        .outcome
    (1 to 4).foreach { round =>
      val value = random.nextInt(8)
      val parity = if value % 2 == 0 then libraryTerm[encoding.type]("true")
      else libraryTerm[encoding.type]("false")
      assert(
        JitTesting.sameOutcomes(
          normalForms(libraryTerm[encoding.type]("double")(numeral(value))),
          normalForms(numeral(2 * value))
        ) &&
          JitTesting.sameOutcomes(
            normalForms(libraryTerm[encoding.type]("even")(numeral(value))),
            normalForms(parity)
          ),
        s"round $round, natural $value"
      )
    }
  }

object StorageWriteBackLawTest:

  /** The capability the tests read a storage's view with, granted as a test
    * sets up.
    */
  val storageAccess: com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
