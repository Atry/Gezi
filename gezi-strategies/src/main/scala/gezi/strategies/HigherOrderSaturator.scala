package gezi.strategies

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.egraph.LiveNode
import gezi.ematching.indexing.Indexing
import gezi.ir.{Configured, NativeSpecializer}
import gezi.ir.Layer
import gezi.ir.Pattern
import gezi.ir.Reachability
import gezi.lemmaencoding.EncodedLemma
import gezi.orientation.Orientations
import gezi.saturation.BodyOpening
import gezi.saturation.End
import gezi.saturation.HigherOrderMatching
import gezi.saturation.MatchKey
import gezi.ir.LemmaIdentifier
import gezi.saturation.Opening
import gezi.saturation.OpeningCriterion
import gezi.saturation.OpeningCriterionChoice
import gezi.saturation.ReverseBeta
import gezi.saturation.Run
import gezi.saturation.Saturation
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.Thunk

/** The baseline's saturation with the lemmas' higher-order occurrences matched
  * by beta (`HigherOrderMatching`): the root case of the reverse beta on the
  * inputs' spellings (`ReverseBeta`, for a left side that is a metavariable
  * applied to names); the first-order saturation of `FixpointEgraph.begun` run
  * to its fixed point or its budget; then every enabled lemma whose left side
  * has a higher-order occurrence matched against the graph, and each instance
  * written (the left side's thunks united with the thunks they matched, the
  * right side's with their beta normal forms, by the β rule), one instance of
  * the budget for each that changes the graph; then the first-order saturation
  * again, which unites the two sides of each instance, until no instance
  * changes the graph or the budget is spent.
  *
  * With `writeBack` given, the closures are opened and their bodies written
  * back as well (`BodyOpening`): every closure that calls a name some lemma's
  * left side applies opened at fresh eigenvariables once, the closures of the
  * bodies opened in turn in the same round, each body saturated with the rest,
  * and written back by the abstraction rule in the next round, spelled by
  * `writeBack`.
  *
  * Which lemmas, where and with what values is the lemmas' matching; the order
  * is the lemmas' by identifier and the classes' by node, so nothing here reads
  * a type or names a lemma (`CONTRIBUTING.md`, "Types live only in the term").
  */
final case class HigherOrderSaturator[C <: NativeSpecializer & Singleton](
    options: SaturationOptions[C],
    writeBack: Option[LocalExtraction[C]],
    round: Option[FixpointEgraph.CompiledRound[C]],
    openingChoice: OpeningCriterionChoice
) extends Saturator[C]:

  private given C = options.construction.specializer

  round.foreach(compiled =>
    require(
      compiled.options == options,
      s"the compiled round's options are the saturator's: ${compiled.options}"
    )
  )

  def saturated(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      explained: Boolean,
      stop: StopSignal
  ): Run[C] =
    begun(index, inputs, options.budget, explained, stop).run

  def lemmas(index: StandardLibraryIndex[C]): Vector[EncodedLemma[C]] =
    compiledRound(index).fold(FixpointEgraph.lemmas(index, options))(_.lemmas)

  /** The compiled round given, checked to be of this index; none when no round
    * was given, and the round is compiled for each input.
    */
  private def compiledRound(
      index: StandardLibraryIndex[C]
  ): Option[FixpointEgraph.CompiledRound[C]] =
    round.map(compiled =>
      require(
        compiled.index eq index,
        "the compiled round is of the index the saturator is given"
      )
      compiled
    )

  /** A saturator that compiles its round once for the index, to be kept and
    * given every input of the round.
    */
  def prepared(index: StandardLibraryIndex[C]): HigherOrderSaturator[C] =
    copy(round = Some(FixpointEgraph.compiledRound(index, options)))

  def begun(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      budget: Int,
      explained: Boolean,
      stop: StopSignal
  ): SaturationProgress[C] =
    require(budget >= 0, s"a budget is not negative: $budget")
    val enabled = lemmas(index)
    val higherOrder = enabled.filter(lemma =>
      HigherOrderMatching.higherOrderMetavariables(lemma.left).nonEmpty
    )
    rounds(
      index,
      rootReversed(index, inputs, enabled, budget, None, explained, stop),
      higherOrder,
      Vector.empty,
      Map.empty,
      None,
      Map.empty,
      budget,
      stop
    )

  /** `begun` on the graph the shared rounds before this one left
    * (`FixpointEgraph.begunOn`), with at most `budget` instances added to those
    * the graph already counts. The saturator is prepared (`prepared`), and its
    * round is one of `shared`.
    */
  def begunOn(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      shared: Vector[FixpointEgraph.CompiledRound[C]],
      inputs: Vector[Configured[C]],
      budget: Int,
      stop: StopSignal
  ): SaturationProgress[C] =
    require(budget >= 0, s"a budget is not negative: $budget")
    require(
      compiledRound(index).exists(compiled => shared.exists(_ eq compiled)),
      "a saturator on a shared graph is prepared with one of its rounds"
    )
    val enabled = lemmas(index)
    val higherOrder = enabled.filter(lemma =>
      HigherOrderMatching.higherOrderMetavariables(lemma.left).nonEmpty
    )
    val start = graph.instances
    rounds(
      index,
      // The shared graph records the terms made or not as it was made.
      rootReversed(
        index,
        inputs,
        enabled,
        budget,
        Some((graph, shared)),
        graph.explained,
        stop
      ),
      higherOrder,
      Vector.empty,
      Map.empty,
      None,
      Map.empty,
      start + budget,
      stop
    )

  /** The run begun with the root case of the reverse beta (`ReverseBeta`): for
    * every enabled lemma whose left side is a metavariable applied to names,
    * every subterm of an input whose spelling holds them all united with its
    * redex over them, by the β rule, one instance of the budget each; then the
    * first-order saturation on the budget left. It began as
    * `ReverseBetaSaturator.begun` of the module contest-modules-wren.
    */
  private def rootReversed(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      enabled: Vector[EncodedLemma[C]],
      budget: Int,
      sharedGraph: Option[(EGraph[C], Vector[FixpointEgraph.CompiledRound[C]])],
      explained: Boolean,
      stop: StopSignal
  ): SaturationProgress[C] =
    // FIXME (2026-11-07, found in a review): on a shared https://github.com/Atry/private-overlay/issues/1955
    // graph, the root case enumerates the subterms of the inputs only, not
    // the nodes the earlier rounds added. The general e-matching sees those
    // nodes (EGraph.everyNodeRedone), but a later round's lemma whose left
    // side is a reverse beta redex at the root does not get its redex for
    // a term only an earlier round derived. No entry in the tree reaches
    // it yet: read 2026-11-07 (main 277904984), the one lemma of the
    // standard library whose left side is a metavariable applied to names
    // is wren_typed_block's, and both entries (contest-entries-solo and
    // contest-entries-wren) enable that module in their first round only,
    // where the inputs are the graph. A later round that enables such a
    // lemma meets the gap. Candidate fix: enumerate the root case over the
    // graph's classes, each spelled by a canonical extraction.
    val nameLists =
      enabled.flatMap(lemma => ReverseBeta.abstractedNames(lemma.left)).distinct
    val abstractions = (for
      names <- nameLists
      subterm <- ReverseBeta.holdingAll(inputs, names)
    yield (subterm, ReverseBeta.redex(subterm, names, options.construction)))
      .take(budget)
    val subterms = abstractions.map(_._1)
    val roots = inputs ++ subterms ++ abstractions.map(_._2)
    val begun = (compiledRound(index), sharedGraph) match
      case (Some(compiled), Some((graph, shared))) =>
        FixpointEgraph.begunOn(compiled, shared, graph, roots, stop)
      case (Some(compiled), None) =>
        FixpointEgraph.begunIn(compiled, roots, 0, None, explained, stop)
      case (None, None) =>
        FixpointEgraph.begun(
          index,
          roots,
          options.copy(budget = 0),
          explained,
          stop
        )
      case (None, Some(_)) =>
        throw IllegalStateException("a saturator on a shared graph is prepared")
    val nodes = begun.run.inputNodes
    // β conversion, not one β step: the redex's n applications contract to
    // the subterm with its closures captured otherwise than in the
    // subterm's own spelling (a closed `fixpoint g` of the subterm is one
    // filling, its abstraction's body has `x g` with x a variable, two
    // fillings), so the two are one λ-term spelled as two IR terms.
    val united = abstractions.indices.foldLeft(begun.run.graph) {
      (graph, position) =>
        graph.unionWorked(
          nodes(inputs.size + position),
          nodes(inputs.size + subterms.size + position),
          Justification.BetaConversion(nodes(inputs.size + position)),
          None
        )
    }
    val started = begun.copy(run =
      begun.run.copy(
        graph = Saturation.agendaWorked(
          begun.program,
          begun.compiled,
          begun.builtInRules,
          united
        ),
        inputNodes = nodes.take(inputs.size)
      )
    )
    val left = budget - abstractions.size
    if left == 0 then
      started.copy(run =
        started.run.copy(end = End.BudgetExhausted(started.run.graph.instances))
      )
    else started.resumed(left, stop)

  /** After each first-order fixed point: the higher-order instances; then, when
    * the saturator writes bodies back, the write-back of every body opened in
    * an earlier round (saturated since) by its spelling under `writeBack`, and
    * the opening of every closure not yet opened; each step that changes the
    * graph one instance of the budget.
    *
    * FIXME: the order of the phases is fixed here (the
    * https://github.com/Atry/private-overlay/issues/2032 first-order fixed
    * point, then the write-back, the higher-order instances and the opening as
    * this method runs them, then the first-order saturation again), and so is
    * how they share one instance budget, each phase taking what the ones before
    * it left (with `rootReversed`'s root case before them all). The schedule of
    * phases and its division of the budget are to become options of one
    * interface chosen by configuration (entry data and `Defaults`).
    */
  @scala.annotation.tailrec
  private def rounds(
      index: StandardLibraryIndex[C],
      progress: SaturationProgress[C],
      higherOrder: Vector[EncodedLemma[C]],
      openings: Vector[Opening[C]],
      written: Map[Int, Int],
      spellings: Option[CarriedSpellings[C, ModuleCost]],
      matchesWritten: Map[LemmaIdentifier, Set[MatchKey[C]]],
      budget: Int,
      stop: StopSignal
  ): SaturationProgress[C] =
    progress.run.end match
      case End.Stopped(_) | End.BudgetExhausted(_) => progress
      case End.FixedPoint(_)                       =>
        val graph = progress.run.graph
        val (afterWriteBack, writtenAfter, spellingsAfter) =
          writeBack.fold((graph, written, spellings))(spelling =>
            writtenBack(
              index,
              spelling,
              budget,
              graph,
              openings,
              written,
              spellings
            )
          )
        val keyed = higherOrder.map(lemma =>
          val seen = matchesWritten
            .getOrElse(lemma.lemma, Set.empty)
            .map(HigherOrderMatching.canonical(graph, _))
          (
            lemma.lemma,
            seen,
            HigherOrderMatching.unseenInstances(
              graph,
              lemma.left,
              lemma.right,
              seen
            )
          )
        )
        val matchesAfter = keyed
          .map((lemma, seen, found) => lemma -> (seen ++ found.map(_._1)))
          .toMap
        val instances = keyed.flatMap(_._3.map(_._2))
        val afterInstances =
          instances.foldLeft(afterWriteBack)((current, instance) =>
            counted(
              budget,
              current,
              HigherOrderMatching.written(current, instance)
            )
          )
        val (afterOpening, opened) = writeBack match
          case Some(_) if afterInstances.instances < budget =>
            val (next, made) = BodyOpening.opened(
              afterInstances,
              openings,
              budget - afterInstances.instances,
              openingScope(index, afterInstances, openings),
              leftHeads(index),
              leafRoots(index, afterInstances),
              openingCriterion(index)
            )
            (
              made.foldLeft(next)((counting, _) => counting.instanceCounted),
              made
            )
          case _ => (afterInstances, Vector.empty)
        if afterOpening.canonicalNodeCount == graph.canonicalNodeCount && afterOpening.joiningUnionCount == graph.joiningUnionCount
        then progress
        else
          val synced = codesSynced(progress, afterOpening)
          val worked = Saturation.agendaWorked(
            synced.program,
            synced.compiled,
            synced.builtInRules,
            afterOpening
          )
          val left = budget - worked.instances
          val after = synced.copy(run = synced.run.copy(graph = worked))
          if left <= 0 then
            after.copy(run =
              after.run.copy(end = End.BudgetExhausted(worked.instances))
            )
          else
            rounds(
              index,
              after.resumed(left, stop),
              higherOrder,
              openings ++ opened,
              writtenAfter,
              spellingsAfter,
              matchesAfter,
              budget,
              stop
            )

  /** The names an enabled lemma's left side applies, at the head of an
    * application spine anywhere in it, each with the largest number of
    * arguments a left side applies it to: the names under which the index seeds
    * a match, so that a closure that calls one, or calls one applied to fewer
    * arguments than that, may hold a match once opened.
    */
  private def leftHeads(
      index: StandardLibraryIndex[C]
  ): Map[Configured[C], Int] =
    lemmas(index)
      .flatMap(lemma => Orientations.positions(lemma.left))
      .collect { case (_, application @ Pattern.Apply(_, _)) =>
        Orientations.spineHead(application)
      }
      .flatten
      .foldLeft(Map.empty[Configured[C], Int]) { case (bounds, (head, arity)) =>
        bounds.updated(head, bounds.get(head).fold(arity)(_ max arity))
      }

  /** The criterion the round opens closures by, as `openingChoice` says: every
    * closure that calls a head (`OpeningCriterion.CallsAHead`), or those whose
    * calls have arguments that may match a left side's spine
    * (`OpeningCriterion.CallsAHeadWithMatchingArguments`, its patterns the
    * round's enabled left sides').
    */
  private def openingCriterion(
      index: StandardLibraryIndex[C]
  ): OpeningCriterion[C] =
    openingChoice match
      case OpeningCriterionChoice.CallsAHead => OpeningCriterion.CallsAHead[C]()
      case OpeningCriterionChoice.CallsAHeadWithMatchingArguments =>
        OpeningCriterion.CallsAHeadWithMatchingArguments(
          leftArgumentPatterns(index)
        )

  /** The argument patterns of every application spine in an enabled lemma's
    * left side, by the name at its head: the spines `leftHeads` bounds, each
    * with its arguments.
    */
  private def leftArgumentPatterns(
      index: StandardLibraryIndex[C]
  ): Map[Configured[C], Vector[Vector[Pattern[C]]]] =
    lemmas(index)
      .flatMap(lemma => Orientations.positions(lemma.left))
      .collect { case (_, application @ Pattern.Apply(_, _)) =>
        gezi.ir.Spine.of(application)
      }
      .collect { case (Pattern.InstructionReference(head), arguments) =>
        head -> arguments
      }
      .foldLeft(Map.empty[Configured[C], Vector[Vector[Pattern[C]]]]) {
        case (spines, (head, arguments)) =>
          spines.updated(
            head,
            spines.getOrElse(head, Vector.empty) :+ arguments
          )
      }

  /** The classes whose closures the saturator may open: every class of the
    * graph and of the bodies opened so far, except under a library define,
    * whose body is knowledge the lemmas state, not the program's. Which of them
    * are opened is the round's opening criterion, as `openingChoice` chooses
    * (`openingCriterion`), and the budget bounds the rest. No marker is read:
    * Scala recognizes no hint, a hint being for the lemmas' matching, not for
    * Scala.
    */
  private def openingScope(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      openings: Vector[Opening[C]]
  ): Set[Int] =
    BodyOpening.classesUnder(
      graph,
      graph.liveNodes.map(_.root) ++ openings.map(_.body),
      leafRoots(index, graph)
    )

  /** The classes of the round's leaves (`StandardLibraryIndex.noinline`), whose
    * bodies are not opened: noinline is what keeps a term unexpanded.
    */
  private def leafRoots(
      index: StandardLibraryIndex[C],
      graph: EGraph[C]
  ): Set[Int] =
    index.noinline.flatMap(graph.instructionNode).map(graph.root)

  /** The graph after a step, counted as one instance when it changed the graph;
    * the graph before when the budget is spent. The agenda is worked once for
    * the round, after the program has every code the round's steps made
    * (`codesSynced`).
    */
  private def counted(
      budget: Int,
      before: EGraph[C],
      after: EGraph[C]
  ): EGraph[C] =
    if before.instances >= budget then before
    else if after.canonicalNodeCount > before.canonicalNodeCount || after.joiningUnionCount > before.joiningUnionCount
    then after.instanceCounted
    else after

  /** The saturation's program with the building of every code under the graph's
    * thunks that it has not (`Indexing.codeBuilding`), compiled again by the
    * options' backend: the codes the higher-order matching, the openings and
    * the write-backs made, which the β rule reads like any other.
    */
  private def codesSynced(
      progress: SaturationProgress[C],
      graph: EGraph[C]
  ): SaturationProgress[C] =
    val thunkCodes = graph.liveNodes.collect {
      case LiveNode(_, _, Thunk(code, _, _)) => code
    }
    val missing = Reachability
      .codesUnder(thunkCodes)
      .filterNot(progress.program.codes.contains)
    if missing.isEmpty then progress
    else
      val program = progress.program.copy(codes =
        progress.program.codes ++ missing.map(code =>
          code -> Indexing.codeBuilding(code.layer)
        )
      )
      progress.copy(
        program = program,
        compiled = options.backend.compiled(program)
      )

  /** Every opened body written back by its spelling, the innermost first (the
    * openings in the reverse of the order they were made, a closure inside a
    * body opened after the body), each spelled from the graph the write-backs
    * before it left, so that an outer body is spelled with its inner closures
    * written back; a body whose class has the members it had when it was last
    * written back (`written`, by the closure's node) is not spelled again, a
    * cost only.
    *
    * The spelling cache is kept from one body to the next within the pass and
    * dropped at the next pass under `SpellingRetention.KeptWithinAPass`,
    * dropped after every body under `NotKept`, and under `KeptAcrossPasses`
    * started from the cache the pass before left (`spellings`), its entries of
    * classes changed since dropped (`LocalExtraction.carriedCache`), and left
    * to the next pass with the marks of the graph this pass starts from, so
    * that the next pass drops what the write-backs, instances, openings and
    * saturation in between change (the write-back's
    * `LocalExtraction.spellingRetention`). The carried cache lives as long as
    * one run of `rounds`.
    */
  private def writtenBack(
      index: StandardLibraryIndex[C],
      spelling: LocalExtraction[C],
      budget: Int,
      graph: EGraph[C],
      openings: Vector[Opening[C]],
      written: Map[Int, Int],
      spellings: Option[CarriedSpellings[C, ModuleCost]]
  ): (EGraph[C], Map[Int, Int], Option[CarriedSpellings[C, ModuleCost]]) =
    val eigenvariables = openings.flatMap(_.eigenvariables).toMap
    val prepared = spelling.prepared(index, graph)
    val openedClosures = openings.map(_.closure).toSet
    val start = spelling.spellingRetention match
      case SpellingRetention.KeptAcrossPasses =>
        spellings.fold(SpellingCache.empty[C, ModuleCost])(
          LocalExtraction.carriedCache(_, graph, prepared, openedClosures)
        )
      case SpellingRetention.KeptWithinAPass | SpellingRetention.NotKept =>
        SpellingCache.empty[C, ModuleCost]
    val (afterAll, finalCache, writtenAfter) =
      openings.reverse.foldLeft((graph, start, written)) {
        case ((current, cache, done), opening) =>
          val bodySize = current.classMembers(opening.body).size
          if done.get(opening.closure).contains(bodySize) then
            (current, cache, done)
          else
            val (bodySpelling, nextCache) = spelling.spelled(
              prepared,
              current,
              opening.body,
              cache,
              openedClosures
            )
            val next = counted(
              budget,
              current,
              BodyOpening.writtenBack(
                current,
                opening,
                bodySpelling,
                eigenvariables
              )
            )
            val keptCache = spelling.spellingRetention match
              case SpellingRetention.KeptWithinAPass |
                  SpellingRetention.KeptAcrossPasses =>
                nextCache
              case SpellingRetention.NotKept =>
                SpellingCache.empty[C, ModuleCost]
            (
              next,
              keptCache,
              done.updated(
                opening.closure,
                next.classMembers(opening.body).size
              )
            )
      }
    val carried = spelling.spellingRetention match
      case SpellingRetention.KeptAcrossPasses =>
        Some(
          CarriedSpellings(
            finalCache,
            prepared,
            graph.nodeCount,
            graph.unionCount
          )
        )
      case SpellingRetention.KeptWithinAPass | SpellingRetention.NotKept => None
    (afterAll, writtenAfter, carried)
