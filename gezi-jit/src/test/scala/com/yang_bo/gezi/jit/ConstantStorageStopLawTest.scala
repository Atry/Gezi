package com.yang_bo.gezi.jit

import com.yang_bo.gezi.ematching.Match
import com.yang_bo.gezi.ematching.SeedKind
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.strategies.BaselineModules
import com.yang_bo.gezi.strategies.BaselineRounds
import com.yang_bo.gezi.strategies.CountedExtractor
import com.yang_bo.gezi.strategies.NativeRouteCompilation
import com.yang_bo.gezi.strategies.SaturationOptions
import com.yang_bo.gezi.strategies.StandardIndexer
import com.yang_bo.gezi.saturation.ConstantStorageStop
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.strategies.FixpointEgraph
import com.yang_bo.gezi.strategies.StandardSaturator
import com.yang_bo.gezi.strategies.StrategyTesting
import scala.util.Random

/** The laws of a round's constant storage stop
  * (`com.yang_bo.gezi.saturation.ConstantStorageStop`) under the converting construction,
  * with the knowledge of
  * tests/library_fixtures/constant_storage_stop.lambdalattice: two lemmas, one
  * rooted at an application of `double` (bound to the native `natural_double`
  * with a declared result filter), one at a bare parallel. The stop's exact
  * matching is checked against a naive oracle on generated graphs by
  * `com.yang_bo.gezi.backendcomparison.ConstantStorageStopMatchingLawTest`; these laws
  * check the stop inside a round, where folding makes the stopped classes.
  */
class ConstantStorageStopLawTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(120, "s")

  private lazy val library =
    LibraryFiles.compiled(
      "tests/library_fixtures/constant_storage_stop.lambdalattice",
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private lazy val index: StandardLibraryIndex[encoding.type] =
    encoding.operations.index

  private val storageAccess: com.yang_bo.gezi.ir.StorageAccess =
    com.yang_bo.gezi.ir.StorageAccess.granted()

  /** The round's options: the lemmas given, the converting construction, and
    * the stop or not, with the baseline's lemma encoding, backend, indexer and
    * orientation compiler (`BaselineRounds.modules`).
    */
  private def optionsOf(
      lemmas: Vector[com.yang_bo.gezi.ir.LemmaIdentifier],
      builtInRules: Set[BuiltInRule],
      budget: Int,
      stopped: Boolean
  ): SaturationOptions[encoding.type] =
    SaturationOptions[encoding.type](
      lemmas,
      builtInRules,
      budget,
      BaselineRounds.modules.lemmaEncoding,
      BaselineRounds.modules.backend,
      StandardIndexer.of[encoding.type],
      BaselineRounds.modules.orientationCompiler,
      MemoRetention.Kept,
      com.yang_bo.gezi.jit
        .ConvertedTermConstruction[encoding.type](encoding)(storageAccess),
      constantStorageStop = stopped
    )

  /** The round: the fixture's lemmas named, no built-in rule, the converting
    * construction, and the stop or not.
    */
  private def options(
      lemmaNames: Vector[String],
      stopped: Boolean
  ): SaturationOptions[encoding.type] =
    optionsOf(lemmaNames.map(index.lemmaIdentifier), Set.empty, 2000, stopped)

  /** A natural's storage under the fixture's facts, as an instruction. */
  private def naturalStorage(value: Int): Configured[encoding.type] =
    encoding.operations.stored(
      JitTesting.storageOf(encoding)(
        Representation.BigInteger,
        NativeValue.Natural(BigInt(value))
      )
    )

  /** A generated program over naturals' storages, of the depth at most. */
  private def program(random: Random, depth: Int): Configured[encoding.type] =
    def natural = naturalStorage(random.nextInt(20))
    if depth <= 0 then natural
    else
      random.nextInt(5) match
        case 0 => natural
        case 1 =>
          encoding.application(
            JitTesting.libraryInstruction[encoding.type]("double"),
            program(random, depth - 1)
          )
        case 2 =>
          encoding.application(
            JitTesting.libraryInstruction[encoding.type]("even"),
            program(random, depth - 1)
          )
        case 3 =>
          encoding.choice(
            program(random, depth - 1),
            program(random, depth - 1)
          )
        case _ =>
          encoding.parallel(
            program(random, depth - 1),
            JitTesting.libraryInstruction[encoding.type]("nat_type")
          )

  /** A match's instance key on the graph: its orientation, its root's class and
    * its bound classes.
    */
  private def keyOf(
      graph: EGraph[encoding.type],
      found: Match
  ): (Int, Int, Vector[Option[Int]]) =
    (
      found.orientation,
      graph.root(found.root),
      found.bindings.map(_.map(graph.root))
    )

  /** The law of the stop's count: the round with the lemma rooted at `double`
    * alone, the input `double (double s)`, s a natural's storage. Derived
    * before the run: the saturation takes the construction queue before any
    * delta (`Saturation.loop`); the inner application is queued when it is made
    * (its argument's class holds s's leaf) and folds into `Natural(2k)`, whose
    * union queues the outer one through the walk up its users, which folds into
    * `Natural(4k)`; so both applications' classes hold a storage of constant
    * size before any delta is taken. A round that stops skips both
    * applications' deltas and filters them out of the users the instruction
    * `double`'s seed climbs to: no instance of the lemma. A round that does not
    * stop makes one instance at each application, each adding a parallel and a
    * choice joined to the application's class: two unions by the lemma. Its
    * purpose is to catch a stop that does not reach the first-order matcher, or
    * one that stops a round that did not choose it.
    */
  stoppableTest(
    "a round that stops at constant storages matches no lemma at the applications it folded"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val lemma = index.lemmaIdentifier("constant_storage_stop_judged_double")
    val double = JitTesting.libraryInstruction[encoding.type]("double")
    val random = Random(20261141)
    (1 to 3).foreach { round =>
      val value = random.nextInt(30)
      val input = encoding.application(
        double,
        encoding.application(double, naturalStorage(value))
      )
      def lemmaUnions(stopped: Boolean): Int =
        val graph = StandardSaturator(
          options(Vector("constant_storage_stop_judged_double"), stopped)
        )
          .saturated(index, Vector(input), explained = false, stop)
          .graph
        graph.unions.count(_.justification match
          case com.yang_bo.gezi.egraph.Justification.Lemma(found, _) => found == lemma
          case _                                         => false)
      assertEquals(
        (lemmaUnions(stopped = true), lemmaUnions(stopped = false)),
        (0, 2),
        s"round $round, natural $value"
      )
    }
  }

  /** The law that the stop only takes matches away, inside a round: each
    * generated program is the choice of `double n`, `m ∥ nat_type` and a random
    * program over naturals' storages (applications of `double` and `even`,
    * choices, parallels with `nat_type`), saturated by the round with both
    * lemmas that stops. On the graph the run leaves, for every live node that
    * is not hidden, every seed kind and every key the saturation matches it
    * under (`Saturation.deltaSeeds`), the instance keys (orientation, root
    * class, bound classes) the matchers find through the stop's view are a
    * subset of those they find on the graph itself. Derived before the run: the
    * stop's view answers a subset of the graph's answers, and a match is a path
    * of answers. Not vacuous, by the program's fixed parts: `double n` folds
    * before any delta, so its class holds a leaf and hides the application, at
    * which the lemma rooted at `double` matches on the graph and not through
    * the view; and every leaf storage's pattern view is a bare parallel, at
    * which the idempotence lemma matches through the view, rooted at a stopped
    * class, and at the parallel `(m1 + m2) ∥ nat_type`, whose class holds no
    * leaf (a choice is no constructor, so nothing converts it into a storage),
    * rooted at a class not stopped. Its purpose is to catch a stop that adds a
    * match inside a round, or a round whose folds leave no class to stop at.
    */
  stoppableTest(
    "a round's constant storage stop finds a subset of the graph's matches, and hides some"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261142)
    val both = Vector(
      "constant_storage_stop_judged_double",
      "constant_storage_stop_parallel_idempotent"
    )
    val counts = (1 to 6).map { position =>
      val input = encoding.choice(
        encoding.choice(
          encoding.application(
            JitTesting.libraryInstruction[encoding.type]("double"),
            naturalStorage(random.nextInt(20))
          ),
          encoding.parallel(
            encoding.choice(
              naturalStorage(random.nextInt(20)),
              naturalStorage(20 + random.nextInt(20))
            ),
            JitTesting.libraryInstruction[encoding.type]("nat_type")
          )
        ),
        program(random, 3)
      )
      val stopping = options(both, stopped = true)
      val progress = FixpointEgraph.begunIn(
        FixpointEgraph.compiledRound(index, stopping),
        Vector(input),
        stopping.budget,
        None,
        explained = false,
        stop
      )
      val graph = progress.run.graph
      val view = ConstantStorageStop.view(graph)
      val visible = graph.liveNodes
        .map(_.node)
        .filterNot(ConstantStorageStop.hidden(graph, _))
      val runs = for
        node <- visible
        kind <- SeedKind.values.toVector
        key <- Saturation.deltaSeeds(graph, node)
      yield (
        progress.compiled
          .matches(kind, key, view, node)
          .found
          .map(keyOf(graph, _))
          .toSet,
        progress.compiled
          .matches(kind, key, graph, node)
          .found
          .map(keyOf(graph, _))
          .toSet
      )
      runs.foreach((stopped, whole) =>
        assert(
          stopped.subsetOf(whole),
          s"program $position: the stop found ${stopped -- whole} the graph does not"
        )
      )
      (
        graph.liveNodes.count(live =>
          ConstantStorageStop.hidden(graph, live.node)
        ),
        runs
          .map(
            _._1.count((_, root, _) => ConstantStorageStop.stopped(graph, root))
          )
          .sum,
        runs
          .map(
            _._1
              .count((_, root, _) => !ConstantStorageStop.stopped(graph, root))
          )
          .sum,
        runs.map((stopped, whole) => (whole -- stopped).size).sum
      )
    }
    assert(
      counts.map(_._1).sum > 0,
      s"no hidden member: the law is vacuous ($counts)"
    )
    assert(
      counts.map(_._2).sum > 0,
      s"no match through a pattern view of a stopped class ($counts)"
    )
    assert(
      counts.map(_._3).sum > 0,
      s"no match through the stop's view at a class not stopped ($counts)"
    )
    assert(counts.map(_._4).sum > 0, s"the stop hid no match ($counts)")
  }

  /** The type-check round of the native route with the fixture library's lemmas
    * of `prolog_backend_type_check`, under the converting construction,
    * stopping at constant storages; its extraction is the native route's.
    */
  private def typeCheckRound(
      stopped: Boolean
  ): (StandardSaturator[encoding.type], CountedExtractor[encoding.type]) =
    (
      StandardSaturator[encoding.type](
        optionsOf(
          BaselineRounds.lemmas(
            library,
            StrategyTesting.round("prolog_backend_type_check")
          ),
          BuiltInRule.beforeOptIn,
          600,
          stopped
        )
      ),
      CountedExtractor[encoding.type](
        NativeRouteCompilation.extraction,
        BaselineModules.table[encoding.type]
      )
    )

  /** The law that the number of storages in a round's inputs does not change
    * the rest of its saturation (#2172's acceptance, with `double`, the
    * fixture's natural native with a declared result filter, where the plan's
    * example names a two-place native): the inputs are `double (double s)`, s a
    * generated natural's storage, and n distinct natural storages, each an
    * input of its own, as a previous round's write-back spells them, for n = 10
    * and n = 1000, saturated and extracted by the type-check round under the
    * converting construction, stopping at constant storages and not. Expected:
    * the folds put `Natural(4k)` in the root's class before any delta (as in
    * the count law above), so the extraction of the first input is that
    * storage, a leaf, and of each other input its own storage; the storages
    * enter as leaves, whose layer no pattern reads, so no lemma instance unites
    * anything with a class holding a storage leaf and the saturation's
    * instances are the same for the two n; no class unites two storages of one
    * criterion, so no storage analysis is a conflict. With this round that
    * holds with the stop and without it: the round's lemmas find nothing at a
    * storage leaf's class, and the stop's own effect, at the classes of folded
    * applications that a lemma is rooted at, is the count law above. Its
    * purpose is to catch storages that cost the saturation work (an input
    * storage expanded, a lemma that reads a leaf), an extraction that spells a
    * fold's class otherwise than by its storage, or a union of two distinct
    * values.
    */
  stoppableTest(
    "the number of storages among a round's inputs does not change the rest of its saturation"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261146)
    val double = JitTesting.libraryInstruction[encoding.type]("double")
    (1 to 2).foreach { round =>
      val value = random.nextInt(30)
      val start = 200 + random.nextInt(1000)
      def run(count: Int, stopped: Boolean) =
        val inputs = encoding.application(
          double,
          encoding.application(double, naturalStorage(value))
        ) +:
          (0 until count).toVector.map(index => naturalStorage(start + index))
        val (saturator, extractor) = typeCheckRound(stopped)
        val saturated =
          saturator.saturated(index, inputs, explained = false, stop)
        val graph = saturated.graph
        val outputs =
          extractor.extracted(index, graph, saturated.inputNodes, inputs, stop)
        def holdsLeaf(root: Int) = graph
          .analysisValue(graph.storageLeaves, graph.root(root))
          .exists(_.storages.nonEmpty)
        val instances = saturated.end match
          case com.yang_bo.gezi.saturation.End.FixedPoint(instances)      => instances
          case com.yang_bo.gezi.saturation.End.BudgetExhausted(instances) =>
            fail(s"the budget ran out at $instances instances")
          case com.yang_bo.gezi.saturation.End.Stopped(instances) =>
            fail(s"stopped at $instances instances")
        (
          instances,
          graph.liveNodes
            .map(live => graph.root(live.node))
            .distinct
            .count(root =>
              graph
                .analysisValue(graph.storageLeaves, root)
                .exists(_.conflicting)
            ),
          graph.unions.count(union =>
            union.justification match
              case com.yang_bo.gezi.egraph.Justification.Lemma(_, _) =>
                holdsLeaf(union.first) || holdsLeaf(union.second)
              case _ => false
          ),
          outputs.headOption.exists(
            Configured.same(_, naturalStorage(4 * value))
          ),
          outputs
            .drop(1)
            .zipWithIndex
            .forall((output, position) =>
              Configured.same(output, naturalStorage(start + position))
            )
        )
      Vector(true, false).foreach { stopped =>
        val (few, many) = (run(10, stopped), run(1000, stopped))
        assertEquals(
          (
            few._1 == many._1,
            few._2,
            many._2,
            few._3,
            many._3,
            few._4,
            many._4,
            few._5,
            many._5
          ),
          (true, 0, 0, 0, 0, true, true, true, true),
          s"round $round, natural $value, stopped $stopped: ten storages $few, a thousand $many"
        )
      }
    }
  }
