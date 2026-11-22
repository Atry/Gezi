package gezi.jmh.pipeline

import java.nio.file.Files
import java.nio.file.Paths
import gezi.contest.entry.Defaults
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.RepeatedVariants
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.EntryData
import gezi.contest.entry.Interaction
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.Defunctionalization
import gezi.frontend.ReadableText
import gezi.jit.NativesProvider
import gezi.proofs.LeanStatements
import gezi.rewritetrace.Conversion
import gezi.rewritetrace.TraceCommand
import gezi.rewritetrace.TraceSourceMaps
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSources
import gezi.strategies.TraceFiles
import gezi.weakhead.Expansions

/** The entry `contest-entries-wren` under `ArticleDestination.WrittenWithTraces` on a generated
  * hot point whose proof holds β conversions: the trace of the point is
  * written as `trace-1.lambdalattice`, its text reads back as the trace
  * player reads it (`gezi.traceplayer.TraceReading`: `TraceText.read`
  * within one evaluator step per character), the text of its start beside it
  * (`TraceFiles.startFile`) reads back as the point's program
  * (`TraceStart.readLocated`), the trace replays from it, it holds a `convert` command of a higher-order conversion, and no
  * two of its commands side by side replay as an identity together; every
  * lemma of the trace finds, by its location, its declaration, the library's
  * lemma of that name with its sides, and the name of the Lean declaration
  * of its soundness (`LeanStatements.names`); the point's article, whose
  * proof crosses the abstraction rule ξ, is written.
  * Its purpose: catch a destination that writes no trace or no article for
  * such a point, a trace the player cannot replay, a step whose term has a
  * binder its carried map gives no origin, a lemma whose location leads to
  * no declaration of its sides or whose name has no Lean declaration, a trace that
  * keeps a detour the inlined point's proof takes (`RewriteTrace`'s
  * `detoursDropped`). Under
  * `ArticleDestination.Written` no such trace is written (the judge's
  * article re-read; `GenericEntry`'s Scaladoc).
  *
  * It reads a contributed entry, so a change of
  * `contest-entries-wren/entry.lambdalattice` can break it: no in-tree
  * configuration of the generic entry other than the contributed ones
  * reaches a β conversion on a hot point (the in-tree entries are the
  * framework's fixture, `contest-entries-osprey`, `contest-entries-solo` and
  * `contest-entries-wren`, and the fixture has no higher-order round,
  * 2026-11-17). A round of the fixture's that reaches one would free it
  * from that file.
  */
class EntryTracesTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-17 on 2 CPUs (contest.slice, CPUs 10,11, nice 10), each test alone, since the entry writes the
  // article of a point whose proof crosses the abstraction rule: the calls test 33.2 s and 25.4 s, the inlined test
  // 38.5 s and 27.0 s, the 1-minute load 4.8 to 8.9. In a JFR profile of the calls test, GenericEntry.run has 1,358
  // samples: writing the article 58, and writing the trace files 104, of which the article's copy is about half (the
  // rest is trace-1, written before too); flattening the trace 846, and reading the entry, outside the run, 772. The
  // bound is 1.5 times the slowest, rounded up to 5 s. Under the markers' spelling as tags, (λ"$t". M) "$t", measured 2026-11-19
  // on 8 CPUs (contest.slice, CPUs 0-7, nice 10), each test alone: the calls test 31.9 s, the inlined test 35.6 s, the
  // 1-minute load 6.4 and 7.5; carrying the maps over the calls trace's 62 steps (TraceSourceMaps.carried) took 0.74 s.
  // FIXME: this suite exceeds the 3 s default: it reads a whole in-tree entry, as InTreeEntriesTest does; a smaller entry https://github.com/Atry/private-overlay/issues/1925
  // with one higher-order round would make it fast.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(60, "s")

  stoppableTest("wren's entry under WrittenWithTraces writes a replayable trace and an article of a hot point") { stopped =>
    traced("repeated_library_hotspots_calls_1000_hot", stopped)
  }

  /** The point whose proof crosses an expansion union to a node a β step
    * of the saturator made with an inner lambda closed but kept inline,
    * whose trace threw before the trace replayed in the replay's spelling
    * (`gezi.rewritetrace.ReplaySpelling`, 085cde60f).
    */
  stoppableTest("wren's entry under WrittenWithTraces writes a replayable trace and an article of an inlined hot point") { stopped =>
    traced("repeated_library_hotspots_inlined_calls_10000_hot", stopped)
  }

  /** The law above on the direct variant of the family's first point. */
  private def traced(family: String, stopped: scala.concurrent.Future[Unit]): Unit =
    val root = Paths.get(sys.props("gezi.buildRoot"))
    val directory = Files.createTempDirectory("entry-traces")
    val (data, afterEntry) = EntryData.read(root.resolve("contest-entries-wren"), Defaults.entryDataState)
    val (library, initialized) = GenericEntryProvider.initializedWithLibrary(
      data,
      gezi.contest.entry.ExecutorModules.registeredFor(root.resolve("contest-entries-wren")),
      gezi.contest.entry.ExtractorModules.registeredFor(root.resolve("contest-entries-wren")),
      NativesProvider.loaded,
      ArticleDestination.WrittenWithTraces(directory),
      afterEntry,
      gezi.contest.entry.Defaults.caches()
    )
    val entry = GenericEntryProvider.withLemmaTexts(initialized, root.resolve("contest-entries-wren"))
    val group = ReductionGroup(root, Expansions.none, gezi.contest.entry.Defaults.caches())
    val Vector(variant) = RepeatedVariants.families
      .filter((name, _) => name == family)
      .flatMap(_._2)
      .filter(_.stem.endsWith("direct")): @unchecked
    val point = variant.point(group, 20261116L, variant.nominal.repetitions.start).program.deBruijnTerm(Map.empty)
    val traceFile = directory.resolve("trace-1.lambdalattice")
    // The trace is written when the lemma rounds end; what the entry does after (compiling and evaluating the
    // point, 10^4 calls on the inlined family) is no part of the law, so the run is asked to stop once the trace
    // exists and ends early with what it has. Run whole, the inlined point exceeded the 25 s bound (25.02 s, alone,
    // the 1-minute load 13.4, 2026-11-16).
    val traceWritten = new StopSignal:
      def stopRequested: Boolean = stopped.isCompleted || Files.exists(traceFile)
    entry.run(Cells.cell(point), gezi.hotspot.ExpansionSource.fresh(), traceWritten) match
      case Interaction.Finished(_, _, _) => ()
    assert(Files.exists(traceFile), s"no trace written in $directory")
    // Measured 2026-11-17: each of the two points' graphs holds one union by the abstraction rule (and 28 and 31 by β
    // conversion, which the article imports); the article is written before the trace.
    // The article's round certificate is not checked here: it imports the entry's lemmas, whose statements
    // `gezi.contest.entry.generic.EntryArticleVerification` writes from the entry's library, and the check of one
    // article takes minutes. Measured 2026-11-17 on 2 CPUs: the calls point's article (110,660 lines) verified in
    // 129 s and the inlined point's (185,589 lines) in 257 s, the entry's lemmas all theorems of Lean
    // (`#print axioms`: propext, Classical.choice and Quot.sound only). SelectedStatementsCertificateTest checks its
    // selected statements and temporary package on smaller articles.
    assert(Files.exists(directory.resolve("round-1.art")), s"no article written in $directory")
    val text = Files.readString(traceFile)
    val trace = TraceText.read(text, TraceText.readingLimit(text))
    val start = TraceStart.readLocated(Files.readString(TraceFiles.startFile(traceFile)), java.net.URI("trace:start"))
    assertEquals(start.start, Defunctionalization.thunkInstruction(point))
    assert(trace.replayed(start.start).flatten.nonEmpty, "the trace replays no step")
    assert(
      trace.rounds.flatten.exists {
        case TraceCommand.Convert(Conversion.HigherOrder(_, _, _), _, _, _) => true
        case _                                                            => false
      },
      "the trace holds no higher-order conversion"
    )
    val steps = trace.replayed(start.start).flatten
    val detours = steps
      .zip(steps.drop(1))
      .count((first, second) =>
        first.command.at == second.command.at && (first.replaced eq second.replacement) && (first.replacement eq second.replaced)
      )
    assertEquals(detours, 0, "two commands side by side replay as an identity together (RewriteTrace's detoursDropped)")
    // The lemmas the trace names are written from the entry's knowledge files, with their locations:
    // every lemma of the trace is one of the library's, attributed to its file.
    val located = TraceText.readLocated(text, TraceText.readingLimit(text))
    assertEquals(
      located.lemmaLocations.count(_.isEmpty),
      0,
      s"lemmas of the trace with no location: ${located.trace.lemmas.zip(located.lemmaLocations).filter(_._2.isEmpty)}"
    )
    // Every lemma of the trace finds, by its location, its declaration in the knowledge file, the library's lemma
    // of that name with the trace's two sides, and the Lean declaration of its soundness: the
    // trace's other use is end-to-end verification in Lean, which must find each lemma's proof.
    assert(located.trace.lemmas.nonEmpty, "the trace names no lemma")
    val leanNames = LeanStatements.names(library).toSet
    located.trace.lemmas.zip(located.lemmaLocations).foreach {
      case (lemma, Some(location)) =>
        val file = Paths.get(location.uri)
        val name = LemmaSources
          .declared(file, Files.readString(file))
          .filter(declaration => declaration.left.start == location.span.start && declaration.right.end == location.span.end) match
          case Vector(declaration) => declaration.name
          case found               => fail(s"${found.size} declarations at $location")
        val sameSides = library.index.lemmaNames.exists(named =>
          named.name == name && library.index.sides(named.lemma).exists(sides => (sides.left eq lemma.left) && (sides.right eq lemma.right))
        )
        assert(sameSides, s"the library's lemma $name does not have the sides of the trace's lemma at $location")
        assert(leanNames.contains(name), s"no Lean declaration of the lemma $name")
      case (lemma, None) => fail(s"the trace's lemma $lemma has no location")
    }
    // Every binder of every step's term has an origin in the map carried to it: the printer names
    // binders from their origins only and throws at one with none. The point's trace holds the higher-order
    // conversions and the abstraction rule, which build thunks of codes the trace has not met.
    val locatedSteps = located.trace.replayed(start.start).flatten
    val carriedMaps = TraceSourceMaps.carried(start.map, locatedSteps)
    (start.start +: locatedSteps.map(_.after)).zip(carriedMaps).foreach((term, map) =>
      ReadableText.printed(term, map)
    )
