package gezi.strategies

import gezi.egraph.MemoRetention
import gezi.ematching.Backend
import gezi.lemmaencoding.LemmaEncoding
import gezi.ir.BuiltInRule
import gezi.ir.LemmaIdentifier
import gezi.orientation.OrientationCompiler
import gezi.standardlibrary.StandardLibraryIndex

/** The implementations a schedule's rounds are built from: the saturator of
  * a round's saturation options, the extractor, the lemma encoding that
  * encodes every round's lemmas into patterns, the indexer, the orientation
  * compiler and the e-matching backend of each saturation. The caller
  * chooses them; the
  * framework's defaults are chosen in one place,
  * `gezi.contest.entry.Defaults`.
  */
final case class RoundModules(
    saturatorOf: SaturationOptions => Saturator,
    extractor: Extractor,
    lemmaEncoding: LemmaEncoding,
    indexer: Indexer,
    backend: Backend,
    orientationCompiler: OrientationCompiler
)

/** The schedules that compile a program on the native route, the port of
  * `gezi/prolog/gezi/baseline/native_route_compilation.pl`,
  * whose module documentation this follows: rounds over a program the front
  * end tagged, the library native_types with hindley_milner_unions,
  * closure_application and occurrence_erasure compiled. Every round is the
  * baseline's search strategy `FixpointEgraph`, one least fixed point of the
  * round's lemmas. `nativeRouteSchedule` has two rounds:
  *
  *   - the type check: the lemmas given, whose
  *     lemmas judge each occurrence in the zero universe, unify its types by
  *     unions of classes and put the typed version beside each application
  *     whose function's type holds a function type of the library's named
  *     types and whose argument's type holds the domain;
  *   - the erasure: the lemmas given, occurrence_erasure's, on the type
  *     check's output.
  *
  * `beyondHindleyMilnerSchedule` puts before the two a round of
  * closure_application's lemma alone: a program HM rejects may be typed by
  * its beta-reduct, the round's budget bounding what the beta rule unfolds.
  *
  * The budget, the caller's, bounds each round's saturation, in instances.
  * The round modules, the caller's (`RoundModules`), give every round its
  * saturator, extractor, lemma encoding, indexer and e-matching backend;
  * the caller's extractor is meant to extract with `extraction`, the modules
  * specialization_attraction and compression. Every round's lemmas are the
  * caller's, by identity, those of a knowledge term
  * (`StandardLibrary.lemmas`); no lemma, combinator or knowledge file is
  * named here.
  *
  * The FIXME of native_route_compilation.pl:62 referred to the one at the
  * Prolog JIT's `fallback_point_head/3` (an operand whose heads do not all
  * end gives no value at a fallback point), which is carried to its port,
  * `gezi.jit.Jit`'s `fallbackPointHeads`.
  *
  * FIXME: the native route's rounds fix every built-in rule https://github.com/Atry/private-overlay/issues/2032
  * (`BuiltInRule.all`), one budget for every round, the extraction modules (`extraction`), and a graph that keeps its
  * respellings (`MemoRetention.Kept`). Each is to become an
  * option of one interface chosen by configuration (entry data and `Defaults`).
  */
object NativeRouteCompilation:

  /** The type check and the erasure, the type check enabling the lemmas
    * `typeCheck` and the erasure the lemmas `erasure` (occurrence_erasure's),
    * each saturation bounded by the budget.
    */
  def nativeRouteSchedule(
      index: StandardLibraryIndex,
      typeCheck: Vector[LemmaIdentifier],
      erasure: Vector[LemmaIdentifier],
      budget: Int,
      modules: RoundModules
  ): Vector[Round] =
    require(budget >= 0, s"a budget is not negative: $budget")
    Vector(
      round(index, typeCheck, BuiltInRule.all, budget, modules),
      round(index, erasure, BuiltInRule.all, budget, modules)
    )

  /** The round of the lemmas `closureApplication` (closure_application's
    * lemma), the type check and the erasure, each saturation bounded by the
    * budget.
    */
  def beyondHindleyMilnerSchedule(
      index: StandardLibraryIndex,
      closureApplication: Vector[LemmaIdentifier],
      typeCheck: Vector[LemmaIdentifier],
      erasure: Vector[LemmaIdentifier],
      budget: Int,
      modules: RoundModules
  ): Vector[Round] =
    round(index, closureApplication, BuiltInRule.all, budget, modules) +:
      nativeRouteSchedule(index, typeCheck, erasure, budget, modules)

  /** The extraction of every round. */
  val extraction: ExtractionOptions = ExtractionOptions(Vector("specialization_attraction", "compression"))

  /** A round enabling the lemmas and the built-in rules given. */
  private def round(
      index: StandardLibraryIndex,
      lemmas: Vector[LemmaIdentifier],
      builtInRules: Set[BuiltInRule],
      budget: Int,
      modules: RoundModules
  ): Round =
    Round(
      FixpointEgraph(
        index,
        modules.saturatorOf(
          SaturationOptions(lemmas, builtInRules, budget, modules.lemmaEncoding, modules.backend, modules.indexer, modules.orientationCompiler, MemoRetention.Kept)
        ),
        modules.extractor
      ),
      None
    )
