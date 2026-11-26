package gezi.contest.entries.osprey

import gezi.orientation.StandardOrientationCompiler
import gezi.saturation.StopSignal
import java.nio.file.Path
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.ClosureBackend
import gezi.hotspot.Cache
import gezi.jit.StorageEncoding
import gezi.jit.DispatchMode
import gezi.jit.Jit
import gezi.jit.JitConfiguration
import gezi.jit.PredicatePerCode
import gezi.jit.CompilationStrategy
import gezi.jit.StrategyDispatch
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryProvider
import gezi.contest.entry.Interaction
import gezi.contest.entry.Judgments
import gezi.contest.entry.OutputDisplay
import gezi.weakhead.Computed
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.Reading
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.standardlibrary.StandardLibrary
import gezi.strategies.DispatchStrategies
import gezi.strategies.NativeRouteCompilation
import gezi.ematching.closures.ClosureCompilation
import gezi.strategies.BaselineModules
import gezi.strategies.RoundModules
import gezi.strategies.CountedExtractor
import gezi.strategies.StandardIndexer
import gezi.strategies.StandardSaturator
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.OccurrenceMarkers
import gezi.frontend.Occurrences
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.LemmaIdentifier
import gezi.ir.Layer
import scala.annotation.tailrec
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}
import gezi.ir.{Closed, Configured, NativeSpecializer, StorageAccess}
import gezi.frontend.DeBruijnTermOf
import gezi.weakhead.ScottADTChoices

/** The entry `contest-entries-osprey`. It started from the
  * baseline entry, `gezi.contest.entries.baseline`, since deleted (the library, the schedule, the dispatch, the JIT reading and the program
  * size below are its code, copied because an entry depends only on the
  * framework's projects). Each program is first read by the JIT as it is,
  * within `OspreyEntry.directLimit` steps; a program that reading does not
  * finish is compiled the baseline's way, untagged, and read again; a cost
  * remembered from the point before (`compileFirst`) shortens the direct
  * reading to `OspreyEntry.probeLimit` steps when the point before was
  * compiled after its direct reading gave up and its compiled reading
  * finished. The reading of each program met is kept for the next points
  * (`OspreyEntry.readings`).
  */
final class OspreyEntryProvider extends EntryProvider:

  /** The baseline's library, backend facts, occurrence markers and JIT,
    * with the judge's cache service and an empty reading cache. Nothing is saturated,
    * extracted, compiled by the JIT or evaluated here.
    */
  def initial(entryDirectory: Path, caches: Cache, articles: ArticleDestination): Entry[?] =
    // TODO: here stood `StandardLibrary.compiledFromText(Vector(sourceTree), OspreyEntry.libraryKnowledge, ...)`,
    // the library of a knowledge text of relative paths from corpora (OspreyEntry.libraryKnowledge, deleted with
    // it), which no longer read since the corpora's conversion to the tuple module encoding (f26d54657).
    // compiledFromText was deleted when the library became files reached by paths: the
    // library is the member `knowledge` of a file of the tree, read by StandardLibrary.compiledAt, as
    // the deleted baseline entry's provider read its baseline.lambdalattice. Porting this entry,
    // its file contest-entries-osprey/osprey.lambdalattice included, is its author's. The deleted code:
    // git show 1346b2038:lambda_jit/contest-entries-osprey/src/main/scala/lambdajit/contest/entries/osprey/OspreyEntry.scala.
    val library: StandardLibrary = throw NotImplementedError("the library: osprey's entry is not ported to G3")
    val encoding = BackendFacts.of(library).storageEncoding
    OspreyEntryProvider.built[encoding.type](encoding, library, caches)

object OspreyEntryProvider:

  /** The entry of the configuration `C` of the encoding of the library's facts. */
  private def built[C <: NativeSpecializer & Singleton](encoding: StorageEncoding & C, library: StandardLibrary, caches: Cache): OspreyEntry[C] =
    val jit = Jit[C](
      JitConfiguration[C](
        encoding,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.Dispatch(DispatchStrategies.fallback),
        instanceTable = false,
        storageAccess = StorageAccess.granted()
      )
    )
    OspreyEntry[C](
      library,
      // TODO: here stood `library.lemmasOf(OspreyEntry.closureApplicationKnowledge)`, the lemmas of the round before
      // the type check, read from knowledge files named by paths. lemmasOf was deleted when the library became files reached by paths: a round's
      // knowledge is a term the entry writes, read by projection off a file of the tree, as the deleted baseline
      // entry's provider read its rounds.
      // Porting this entry is its author's. The deleted call:
      // git show 346ae8b00:lambda_jit/contest-entries-osprey/src/main/scala/lambdajit/contest/entries/osprey/OspreyEntry.scala.
      throw NotImplementedError("the closure application round's lemmas: osprey's entry is not ported to G3"),
      // TODO: here stood `library.lemmasOf(OspreyEntry.typeCheckKnowledge)`, the type check round's lemmas; deleted
      // and to be ported as the TODO above says.
      throw NotImplementedError("the type check round's lemmas: osprey's entry is not ported to G3"),
      // TODO: here stood `library.lemmasOf(OspreyEntry.erasureKnowledge)`, the erasure round's lemmas; deleted and
      // to be ported as the TODO above says.
      throw NotImplementedError("the erasure round's lemmas: osprey's entry is not ported to G3"),
      encoding,
      library.index.occurrenceMarkers,
      // TODO: here stood `library.index.definitions`, the library's define instructions. The index has no definitions
      // since the library became files reached by paths; the deleted baseline entry's
      // provider passed the leaves (`library.index.noinline`) in their place. Porting this entry is its author's, as the TODO above says.
      // The deleted line:
      // git show c30720a56:lambda_jit/contest-entries-osprey/src/main/scala/lambdajit/contest/entries/osprey/OspreyEntry.scala.
      throw NotImplementedError("the library's define instructions: osprey's entry is not ported to G3"),
      jit,
      caches,
      NoJitState,
      Map.empty,
      false,
      Cells.initialState
    )

/** The entry between two points: the baseline's fields and `readings`, the
  * reading of each program met so far in this pass, keyed by the program's
  * instruction after the front end (the library's modules and the schedule are
  * fixed for the entry, so they are part of every key). A value is the
  * program's normal forms as IR instructions, or `None` when all three
  * readings of `read` stopped (a give-up, a cost). The key holds no type, and the
  * value is used only as the answer it is. `compileFirst` is a cost remembered from the point before
  * (`CONTRIBUTING.md`, "Types live only in the term"): whether that point's direct reading
  * gave up and its compiled reading finished; then the next point's direct
  * reading gets only `OspreyEntry.probeLimit` steps before it is compiled.
  * A direct reading that finishes, and a compiled reading that stops,
  * clear the flag. It holds no type and names no program. `cellState` is
  * the state after the cells run so far, a term (`Cells.nextState`).
  */
final case class OspreyEntry[C <: NativeSpecializer & Singleton](
    library: StandardLibrary,
    closureApplicationLemmas: Vector[LemmaIdentifier],
    typeCheckLemmas: Vector[LemmaIdentifier],
    erasureLemmas: Vector[LemmaIdentifier],
    specializer: StorageEncoding & C,
    markers: Option[OccurrenceMarkers],
    defines: Set[Configured[C]],
    jit: Jit[C],
    caches: Cache,
    jitState: JitState[C],
    readings: Map[Configured[C], Option[Vector[Configured[C]]]],
    compileFirst: Boolean,
    cellState: DeBruijnTermOf[Configured[C]]
) extends Entry[C]:

  private given C = specializer
  private given StorageAccess = jit.configuration.storageAccess

  /** The backend facts the entry's encoding is made of. */
  def facts: BackendFacts = specializer.facts

  /** The cell's Output (`Cells.output`) read by `read`, ported from the
    * methods `answered` and `judged` of the interface before cells became
    * closed terms `State → (State, Output)`. An Output `N ∥ T`, a
    * parallel filter, is displayed `N` exactly when N is among the normal
    * forms the reading of T derived (N ∥ T = N then, by absorption), and
    * not evaluated otherwise, a stopped reading included. Any other Output
    * is displayed as its normal forms (`Cells.displayed`) when its reading
    * finishes, and not evaluated when it stops. The signal is not read.
    *
    * FIXME: the expansion source is not read either, while https://github.com/Atry/private-overlay/issues/2052
    * `readings` and the JIT state's instance tables are kept from cell to cell: under an adapter that gives a new
    * source because its files changed (the Jupyter kernel gives one for each cell), a program read before answers from
    * the contents of an earlier source, which `Entry.run` forbids. The judge runs every cell under one source, so its
    * readings are not affected. The candidate fix, the entry's own: keep the source the memos were read under, and on
    * another drop `readings` and the JIT state's answers (`JitState.withoutAnswers`), as `ReadingExecutor` does.
    */
  def run(cell: DeBruijnTermOf[Configured[C]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[C] =
    val output = Cells.output(cell, cellState)
    val (after, display) = output match
      case DeBruijnTerm.Parallel(candidate, program) =>
        val (afterRead, normalForms) = read(program)
        val candidateInstruction = Defunctionalization.thunkInstruction[C](candidate)
        val proved = normalForms.exists(_.exists(Configured.same(_, candidateInstruction)))
        val shown = ScottADTChoices.ofNormalForm(candidateInstruction).filter(_ => proved)
        (afterRead, shown.fold(OutputDisplay.remainder[C](output))(OutputDisplay.Values(_)))
      case _ =>
        val (afterRead, normalForms) = read(output)
        (
          afterRead,
          normalForms.fold(OutputDisplay.remainder[C](output))(found =>
            Judgments
              .scottADTValues(found, OspreyEntry.readingLimit, stop, jit.readingConfiguration)
              .fold(OutputDisplay.remainder[C](output))(values => OutputDisplay.Values(values.choices))
          )
        )
    Interaction.Finished(display, Vector.empty, after.copy(cellState = Cells.nextState(cell, cellState)))

  /** An entry that runs no FFI program is given no value to display. */
  def displayed(value: Closed[C], source: gezi.hotspot.ExpansionSource, stop: StopSignal): (Entry[C], OutputDisplay[C]) =
    throw IllegalStateException("osprey's entry runs no FFI program, and is given no value to display")

  /** The point through the front end (defunctionalized and interned), and
    * its reading: the one in `readings` when the program was read before;
    * else the JIT's reading of the program as it is, within
    * `OspreyEntry.directLimit` steps, or `probeLimit` under `compileFirst`;
    * and, when that reading stops, the reading of the program compiled the
    * baseline's way (`compiledReading`), and the direct reading again within
    * `readingLimit` when that one stops too (`compiledThen`). A program read before leaves
    * `compileFirst` as it was; otherwise the result is added to `readings`,
    * and `compileFirst` is set when the compiled reading ran and finished,
    * cleared when the direct reading finished or the compiled reading
    * stopped. Families are read one point
    * after another, so a family whose points need the compiled path pays one
    * full direct reading that gives up and then a short one a point.
    *
    * The direct reading runs no round: the JIT compiles each code the
    * reading meets, and under the dispatch strategy `fallback` a native
    * fires only on an operand already in its representation, every other
    * call running its define's body: a backend may reject an input that is
    * not specialized, or hand it to a generic semantics such as weak head
    * (`CONTRIBUTING.md`, "Terms", specialization). MEASURED (2026-10-31
    * 18:36 UTC, the 81 practice points of seed 20261031, all 16 of their
    * families, judgeSupervisor on CPUs 0 and 1, entry heap 1g, the direct
    * reading alone with the full `readingLimit`): every point correct, and
    * every family's total lower than the entry merged at 7eea986c0 and than
    * the baseline, e.g. repeated_general_compositions 0.044 s against
    * 0.578 s and 4.04 s, repeated_reduction_problems_fibonacci 0.83 s
    * against 2.86 s and 3.66 s.
    */
  private def read(point: DeBruijnTermOf[Configured[C]]): (OspreyEntry[C], Option[Vector[Configured[C]]]) =
    val input = Defunctionalization.thunkInstruction[C](point)
    readings.get(input) match
      // FIXME (2026-10-31): a hit returns the earlier reading with no https://github.com/Atry/private-overlay/issues/1994
      // derivation of its own, while a reused
      // answer's article must carry the derivation of the first reading. The
      // entry builds no article yet (the article check is not implemented).
      // Candidate fix: keep the first reading's derivation in the cache's
      // value beside its normal forms and hand it out on a hit.
      case Some(reading) => (this, reading)
      case None =>
        val limit = if compileFirst then OspreyEntry.probeLimit else OspreyEntry.directLimit
        val (afterDirect, direct) = jitReading(input, jitState, limit)
        val directed = copy(jitState = afterDirect.jitState)
        val (after, reading) = direct match
          case Some(_) => (directed.copy(compileFirst = false), direct)
          case None    => compiledThen(directed, input)
        (after.copy(readings = after.readings.updated(input, reading)), reading)

  /** The compiled reading of the point from the entry given, and the entry
    * after it with `compileFirst` set when the reading finished; when it
    * stopped, the direct reading of the program again within `readingLimit`
    * steps, so that a program the compiled path does not answer gets the
    * steps the direct reading would have had with no compiled path.
    */
  private def compiledThen(entry: OspreyEntry[C], program: Configured[C]): (OspreyEntry[C], Option[Vector[Configured[C]]]) =
    val (after, reading) = entry.compiledReading(program)
    reading match
      case Some(_) => (after.copy(compileFirst = true), reading)
      case None =>
        val (afterDirect, direct) = after.jitReading(program, after.jitState, OspreyEntry.readingLimit)
        (after.copy(jitState = afterDirect.jitState, compileFirst = false), direct)

  /** The JIT's normal forms of the term at the instruction within the limit of
    * steps, or `None` when the reading stopped, and the reading's state
    * after it.
    */
  private def jitReading(
      term: Configured[C],
      readingJitState: JitState[C],
      limit: Long
  ): (ReadingState[C], Option[Vector[Configured[C]]]) =
    NormalForms
      .normalForms(Mode.Jit, Value.of(term))
      .result(ReadingState.fresh(limit, jit.readingConfiguration).copy(jitState = readingJitState)) match
      case Computed.Done(normalForms, state) => (state, Some(normalForms))
      case Computed.Stopped(state)           => (state, None)

  /** The program at the instruction (interned untagged, as `read` interned it)
    * compiled the baseline's way, untagged: compiled
    * under `beyondHindleyMilnerSchedule` with each round's budget linear in
    * the program's size, dispatched under `fallback`, and its normal forms
    * read by the JIT within `readingLimit` steps.
    */
  private def compiledReading(program: Configured[C]): (OspreyEntry[C], Option[Vector[Configured[C]]]) =
    // TODO: occurrence tagging on the IR outside the e-graph was deleted. What stands here when
    // the entry is ported is either the public front end
    // (`Occurrences.tagged(LibraryRecognition.recognised(point, defines).term, markers)`
    // before defunctionalization, as the deleted baseline entry's
    // `frontEnd` did) or a rewrite through the framework's e-graph in the entry's
    // own schedule rounds. The deleted code reads back with
    // `git show fb52420956a830ec5439e8b2139338ea2e04217e:lambda_jit/contest-entries-osprey/src/main/scala/lambdajit/contest/entries/osprey/NamedOccurrences.scala`.
    val input = program
    val schedule = NativeRouteCompilation.beyondHindleyMilnerSchedule[C](
      specializer.operations.index,
      closureApplicationLemmas,
      typeCheckLemmas,
      erasureLemmas,
      OspreyEntry.roundBudget(OspreyEntry.programSize(input)),
      RoundModules[C](
        StandardSaturator[C](_),
        CountedExtractor(NativeRouteCompilation.extraction, BaselineModules.table[C]),
        BaselineLemmaEncoding,
        StandardIndexer.of[C],
        ClosureCompilation,
        StandardOrientationCompiler,
        gezi.jit.ConvertedTermConstruction[C](specializer)(jit.configuration.storageAccess)
      )
    )
    val dispatched = StrategyDispatch.dispatched[C](
      CompilationStrategy(DispatchStrategies.fallback, schedule),
      input,
      specializer,
      caches,
      StopSignal.NeverStopped
    )
    val (after, reading) = jitReading(dispatched.refined, jitState, OspreyEntry.readingLimit)
    (copy(jitState = after.jitState), reading)

/** The entry's configuration: the baseline entry's (`gezi.contest.entries.baseline`,
  * deleted), copied, and the two budgets
  * of the direct reading, `directLimit` and `probeLimit`.
  */
object OspreyEntry:

  /** The steps the direct reading of a program may take before the program
    * is compiled: the steps that stand for 4 seconds (`Reading.budgetSteps`,
    * 2,000,000 a second, the reference evaluator's rate). MEASURED
    * (2026-10-31 18:48 UTC, a probe that is not committed, the direct
    * reading of the 81 practice points of seed 20261031 in a forked test JVM
    * on CPUs 0 to 3 under load 14): the JIT ran about 5,000,000 steps a
    * second, and the longest reading took 2,097,897 steps (0.43 s,
    * repeated_reduction_problems_fibonacci at R = 21), so every such point is
    * read directly within these steps. MEASURED (2026-11-01 05:16 UTC, a
    * probe that is not committed, a published points file, CPUs 0 and 1):
    * with the occurrence tagging since deleted, the compiled reading of an unshared
    * doublings or binary point takes 0.6 to 4.4 s (the first, cold), while
    * its direct reading takes 11,294,133 to 75,328,659 steps (4.8 to 37 s);
    * the direct readings of repeated_reduction_problems_grids take 4,786,926
    * to 6,338,401 steps (1.4 to 1.7 s, compiled 2.0 to 2.4 s) and of
    * repeated_reduction_problems_sums at R = 13 5,336,072 (4.3 s, compiled
    * 6.1 s), so the limit sits above those and below the unshared points';
    * the 10 seconds' steps it had before made the first unshared point of a
    * family give up only after 20,000,000. A point the compiled reading does
    * not answer is read directly again within `readingLimit`
    * (`compiledThen`), so this limit costs time on such a point, never its
    * answer.
    */
  val directLimit: Long = Reading.budgetSteps(4)

  /** The steps the direct reading of a point may take under `compileFirst`,
    * before the point is compiled: the steps that stand for half a second,
    * a choice, not a measurement. A point of a light family, met after a
    * heavy one, finishes within them and clears the flag; a point of a heavy
    * family loses at most these steps before it is compiled. MEASURED, the
    * defects this replaces (a judge's pass and a reading of its
    * published points, 2026-11-01 03:05 UTC, CPU 1): with no direct reading
    * under the flag, the families after repeated_library_unshared_binary were
    * compiled point by point (repeated_closures direct at R = 4 to 16, 0.37
    * to 0.42 s a point against 0.04 s read directly); with the flag kept only
    * after compiled work of a quarter of `directLimit`, the light families
    * read directly again (repeated_closures 0.08 s in all), but
    * unshared_binary's compiled points were light enough to clear the flag,
    * so each of its points spent `directLimit` reading directly first (44.4 s
    * in all against 1.7 s in that pass).
    */
  val probeLimit: Long = Reading.budgetSteps(0.5)

  /** The knowledge files the type check round enables, the baseline's, by
    * their paths; the entry keeps the lemmas they declare (`typeCheckLemmas`).
    */
  val typeCheckKnowledge: Vector[String] =
    Vector("corpora/compiler/hindley_milner_unions", "corpora/compiler/native_arithmetic_unions", "corpora/compiler/prolog_backend_shapes")

  /** The knowledge file of the round before the type check, the baseline's. */
  val closureApplicationKnowledge: Vector[String] = Vector("corpora/compiler/closure_application")

  /** The knowledge file of the round after the type check, the baseline's. */
  val erasureKnowledge: Vector[String] = Vector("corpora/compiler/occurrence_erasure")

  /** The instances a round may take for each node of the program, four times
    * the 8 of the deleted baseline entry (`BaselineEntry.instancesPerNode`),
    * chosen under an
    * occurrence tagging since deleted, which gave each instruction one tag, so
    * that a program had fewer nodes than under the front end's tagging while
    * its type check took as many instances. The readings below were taken
    * with that tagging; the untagged program the entry now compiles was not
    * measured.
    * MEASURED (2026-10-31 22:29 UTC, a probe that is not committed, CPUs 0
    * and 1): double applied to the Scott numeral of 2000, inlined and tagged
    * by that tagging, 2,048 nodes: at 8 per node the type check round
    * ran out of its budget (16,384) and the reading called no native
    * (118,038 steps); at 32 it reached its fixed point at 22,104 instances
    * (10.8 per node), and the reading called natural_double's natives 2,002
    * times in 60,015 steps. MEASURED (2026-11-01 04:59 UTC, a probe that is
    * not committed, CPUs 0 and 1, the type check round with no budget on
    * every evaluation point of a published points file, tagged by that
    * tagging): every point reaches the round's fixed point, at 16.4 instances a
    * node at most (repeated_reduction_interpreter at R = 128), so no point
    * HM checks meets this budget, as no point HM checks may (`CONTRIBUTING.md`,
    * "Ordinary programs compile as a native typed compiler compiles them").
    */
  val instancesPerNode: Int = 32

  /** The budget of each round on a program of the size. */
  def roundBudget(size: Int): Int = instancesPerNode * size

  /** The steps the compiled reading of a point may take, and the direct
    * reading after it when it stops (`compiledThen`): the steps that stand
    * for 10 seconds, 20,000,000. A family's points share one budget of 60
    * seconds, so a point no reading answers must stop well
    * within it, or the family's later points are not read: in a judge's pass
    * one judgment trap first in repeated_set_free_scope_judgments' order
    * took 58.7 s with the 60 seconds' steps this limit had before, and the
    * other seven points read STOPPED, for every entry.
    */
  val readingLimit: Long = Reading.budgetSteps(10)

  /** The size of the program at the instruction: the distinct layers reachable
    * from it and the distinct codes their thunks name, each counted once;
    * an opaque instruction counts as a leaf.
    */
  def programSize[C <: NativeSpecializer & Singleton](root: Configured[C])(using C): Int =
    val (layers, codes) = reachable(List(root), Set.empty, Set.empty)
    layers.size + codesReachable(codes.toList, Set.empty).size

  @tailrec
  private def reachable[C <: NativeSpecializer & Singleton](
      pending: List[Configured[C]],
      layers: Set[Configured[C]],
      codes: Set[Code]
  )(using C): (Set[Configured[C]], Set[Code]) = pending match
    case Nil => (layers, codes)
    case instruction :: rest if layers.contains(instruction) => reachable(rest, layers, codes)
    case instruction :: rest =>
      val (children, named) =
        if instruction.heldAsLeaf then (Nil, codes)
        else
          instruction.layer match
            case Thunk(code, _, fillings) => (fillings.toList, codes + code)
            case Apply(function, argument) => (List(function, argument), codes)
            case Parallel(left, right)     => (List(left, right), codes)
            case Choice(left, right)       => (List(left, right), codes)
            case _: gezi.ir.UriNode | _: gezi.ir.Opaque | _: gezi.ir.NativeStorage => (Nil, codes)
      reachable(children ::: rest, layers + instruction, named)

  @tailrec
  private def codesReachable(pending: List[Code], seen: Set[Code]): Set[Code] =
    pending match
      case Nil => seen
      case code :: rest if seen.contains(code) => codesReachable(rest, seen)
      case code :: rest =>
        val parts = code.layer match
          case Slot(_)                   => Nil
          case Apply(function, argument) => List(function, argument)
          case Parallel(left, right)     => List(left, right)
          case Choice(left, right)       => List(left, right)
          case Thunk(inner, _, fillings) => inner :: fillings.toList
        codesReachable(parts ::: rest, seen + code)
