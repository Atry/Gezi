package com.yang_bo.gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import com.yang_bo.gezi.locations.Location
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.orientation.StandardOrientationCompiler
import com.yang_bo.gezi.proofs.OpentheoryArticle
import com.yang_bo.gezi.proofs.RewriteTrace
import com.yang_bo.gezi.rewritetrace.PositionSegment
import com.yang_bo.gezi.rewritetrace.Positions
import com.yang_bo.gezi.rewritetrace.ReplayedStep
import com.yang_bo.gezi.rewritetrace.Trace
import com.yang_bo.gezi.rewritetrace.TraceSourceMaps
import com.yang_bo.gezi.rewritetrace.TraceStart
import com.yang_bo.gezi.rewritetrace.TraceText
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.LemmaSides
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import snapshot4s.generated.snapshotConfig

/** The laws of the source maps carried through a trace
  * (`TraceSourceMaps.carried`), on the rounds of `RewriteTraceLawTest`'s
  * first-order strategy, each trace's start written from its program's source
  * (`TraceStart.written`) and read back with its map
  * (`TraceStart.readLocated`), and the trace written and read back
  * (`TraceText.readLocated`):
  *
  *   1. every map fits its term: a place has the term's subterms below it, or
  *      none, and a code map only at a thunk;
  *   2. a place a map locates has the layer (the constructor, and a thunk's
  *      code and holes) the start has at a place of that location, so that no
  *      step moves a location to another layer; the subterms below a place have
  *      their own locations, and a step under the place changes them and not
  *      its layer;
  *   3. a step keeps the map of every place off its position, and gives each
  *      place its provenance copies a subtree to the map of the place the
  *      subtree came from.
  *
  * Purpose: catch a map that drifts off its term (a child index off by one, a
  * sibling dropped), a location that lands on a subterm the source never wrote
  * there, and a subterm a step moves that loses its places.
  */
class TraceSourceMapsLawTest
    extends GeneratedProperties
    with com.yang_bo.gezi.generatedinputs.SeededSnapshots:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  private given NoFacts.type = NoFacts

  /** The law of a trace written with its lemmas' texts, run alone in a fresh
    * test JVM, took 2.90 to 3.63 s over five seeds (measured 2026-11-19 on
    * cores 0-5, the 1-minute load 5.9 to 7.2, with a deadline of 120 s). Each
    * input runs the strategy and reads the trace's text twice, by the writer's
    * check in `TraceText.writtenWith` and by the law's located read; a text of
    * 400 to 1,800 characters, its lemmas' texts included, took 15 to 150 ms to
    * read warm. 6 s leaves that reading room for a slower seed or a busier
    * machine.
    */
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(6, "s")

  import RewriteTraceLawTest.closed
  import RewriteTraceLawTest.equation

  /** The lemmas' sides as closed texts. */
  private val sideTexts: Vector[(String, String)] = Vector(
    ("λa. λb. (a + b)", "λa. λb. (b + a)"),
    ("λa. λb. λc. ((a + b) + c)", "λa. λb. λc. (a + (b + c))"),
    ("λa. (a + a)", "λa. a"),
    ("λa. λb. (λx. λy. x) a b", "λa. λb. a")
  )

  private val lemmas: Vector[LemmaSides[NoFacts.type]] =
    sideTexts.zipWithIndex.map { case ((left, right), number) =>
      equation(number, left, right)
    }

  /** The lemmas as a knowledge file would write them: each side on a line of
    * one file, whose URI is as long as a file's of the corpora (82 characters,
    * read bit by bit as a string literal), at its span; the last lemma's left
    * side written with a name, `konst`, bound to K, so that the trace binds it
    * by the β redex around the data.
    */
  private val lemmaTexts: Map[
    (Configured[NoFacts.type], Configured[NoFacts.type]),
    com.yang_bo.gezi.locations.LemmaText[NoFacts.type]
  ] =
    val written = sideTexts.updated(3, ("λa. λb. konst a b", "λa. λb. a"))
    val names = Vector(
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector("konst" -> closed("λx. λy. x"))
    )
    val (texts, _) = written
      .zip(lemmas)
      .zip(names)
      .foldLeft(
        (
          Map.empty[
            (Configured[NoFacts.type], Configured[NoFacts.type]),
            com.yang_bo.gezi.locations.LemmaText[NoFacts.type]
          ],
          0
        )
      ) { case ((found, offset), (((left, right), sides), bound)) =>
        val leftSpan = com.yang_bo.gezi.locations.Span(offset, offset + left.length)
        val rightSpan =
          com.yang_bo.gezi.locations.Span(leftSpan.end + 1, leftSpan.end + 1 + right.length)
        (
          found.updated(
            (sides.left, sides.right),
            com.yang_bo.gezi.locations.LemmaText(
              java.net
                .URI("file:///gezi/corpora/compiler/test_lemmas.lambdalattice"),
              leftSpan,
              rightSpan,
              left,
              right,
              bound
            )
          ),
          rightSpan.end + 1
        )
      }
    texts

  private val index: StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      lemmas,
      Vector.empty,
      Vector.empty
    )

  /** The instances a round may add, `RewriteTraceLawTest`'s budget for the same
    * lemmas and programs, measured there.
    */
  private val budget: Int = 24

  private val strategy: FixpointEgraph[NoFacts.type] = FixpointEgraph(
    index,
    StandardSaturator(
      SaturationOptions(
        lemmas.map(_.lemma),
        BuiltInRule.beforeOptIn,
        budget,
        BaselineLemmaEncoding,
        ClosureCompilation,
        StandardIndexer.of[com.yang_bo.gezi.ir.NoFacts.type],
        StandardOrientationCompiler,
        MemoRetention.Kept,
        com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts)
      )
    ),
    CountedExtractor(
      ExtractionOptions(Vector("compression")),
      BaselineModules.table[com.yang_bo.gezi.ir.NoFacts.type]
    )
  )

  private val closedText: Gen[String] =
    HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** `RewriteTraceLawTest`'s programs: a choice of two to four closed terms, or
    * a closed term in choice with K applied to two.
    */
  private val programs: Gen[String] =
    Gen.choice1(
      closedText
        .list(Range.linear(2, 4))
        .map(_.map(member => s"($member)").mkString(" + ")),
      for
        context <- closedText
        first <- closedText
        second <- closedText
      yield s"($context) + (λk. λl. k) ($first) ($second)"
    )

  /** The start of the strategy's round on the program, read back from the text
    * `TraceStart` writes of it from the program's source, the trace read back
    * from its text, its steps replayed from that start, and the map of the
    * start and of the term after each step, carried from the start's map.
    */
  private def carried(
      program: String,
      stopped: scala.concurrent.Future[Unit]
  ): (
      Configured[NoFacts.type],
      Trace[NoFacts.type],
      Vector[ReplayedStep[NoFacts.type]],
      Vector[SourceMap]
  ) =
    val (input, trace) = traced(program, stopped)
    val start = TraceStart.readLocated(
      TraceStart.written(input, Some(program)),
      java.net.URI("trace:start")
    )
    val text = TraceText.written(trace)
    val located =
      TraceText.readLocated(text, RewriteTraceLawTest.readingLimit(text))
    val steps = located.trace.replayed(start.start).flatten
    (
      start.start,
      located.trace,
      steps,
      TraceSourceMaps.carried(start.map, steps)
    )

  /** The program read as a closed term and the trace of the strategy's round on
    * it, as the strategy's proof gives it, not written or read.
    */
  private def traced(
      program: String,
      stopped: scala.concurrent.Future[Unit]
  ): (Configured[NoFacts.type], Trace[NoFacts.type]) =
    val input = closed(program)
    val outcome = strategy
      .ran(Vector(input), true, StopSignal.completedWith(stopped))
      .getOrElse(fail("the strategy gave no answer"))
    val Vector(output) = outcome.outputs: @unchecked
    val proof = outcome.proof.getOrElse(fail("the strategy gave no proof"))
    (
      input,
      RewriteTrace.trace(
        OpentheoryArticle.derivation(index, input, output, proof)
      )
    )

  /** Each place of the term with its map, from the root, outermost first. */
  private def places(
      term: Configured[NoFacts.type],
      map: SourceMap
  ): Vector[(Vector[PositionSegment], Configured[NoFacts.type], SourceMap)] =
    if term.opaque then Vector((Vector.empty, term, map))
    else
      val layer = Positions.layerOf(term)
      (Vector.empty[PositionSegment], term, map) +: layer.children
        .zip(Positions.roles(layer))
        .zipWithIndex
        .flatMap { case ((child, role), place) =>
          places(child, map.children.lift(place).getOrElse(SourceMap.unlocated))
            .map((position, subterm, submap) =>
              (role +: position, subterm, submap)
            )
        }

  stoppableProperty("every carried map fits its term") { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val (start, _, steps, maps) = carried(program, stopped)
        val terms = start +: steps.map(_.after)
        val problems = terms.zip(maps).zipWithIndex.flatMap {
          case ((term, map), step) =>
            places(term, map).flatMap((position, subterm, submap) =>
              val count =
                if subterm.opaque then 0 else subterm.layer.children.size
              val thunk = subterm.layer match
                case com.yang_bo.gezi.ir.Thunk(_, _, _) => true
                case _                      => false
              Option.when(
                !(submap.children.isEmpty || submap.children.size == count) || (submap.code.nonEmpty && !thunk)
              )(
                s"step $step at $position: ${submap.children.size} maps under $count subterms, code ${submap.code.nonEmpty}"
              )
            )
        }
        Result
          .assert(problems.isEmpty)
          .log(problems.mkString("\n"))
          .log(s"${steps.size} steps")
      )
  }

  /** A place's own layer, the subterms below it erased: what a location
    * locates, since the places below have locations of their own (`SourceMap`).
    * A step under a place changes its subterms and keeps its layer, a thunk's
    * code and holes included.
    */
  /** A term's own layer with its children left out: the kind of the layer, and
    * a thunk's code, holes and number of fillings.
    */
  private type OwnLayer = Either[Configured[
    NoFacts.type
  ], (String, Option[(com.yang_bo.gezi.ir.Code, Vector[com.yang_bo.gezi.ir.Hole], Int)])]

  private def own(term: Configured[NoFacts.type]): OwnLayer =
    if term.opaque then Left(term)
    else
      Right(term.layer match
        case com.yang_bo.gezi.ir.Apply(_, _)                  => ("apply", None)
        case com.yang_bo.gezi.ir.Parallel(_, _)               => ("parallel", None)
        case com.yang_bo.gezi.ir.Choice(_, _)                 => ("choice", None)
        case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
          ("thunk", Some((code, holes, fillings.size)))
        case other =>
          throw IllegalStateException(
            s"a term of no facts holds the layer $other"
          ))

  stoppableProperty(
    "a located place has the layer the start has at that location"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val (start, _, steps, maps) = carried(program, stopped)
        val written: Map[Location, Set[OwnLayer]] =
          places(start, maps.head)
            .flatMap((_, subterm, submap) =>
              submap.locations.map(_ -> own(subterm))
            )
            .groupMap(_._1)(_._2)
            .view
            .mapValues(_.toSet)
            .toMap
        val terms = start +: steps.map(_.after)
        val located = terms
          .zip(maps)
          .map((term, map) => places(term, map).count(_._3.locations.nonEmpty))
        val problems =
          terms.zip(maps).zipWithIndex.flatMap { case ((term, map), step) =>
            places(term, map).flatMap((position, subterm, submap) =>
              submap.locations.toVector.flatMap(location =>
                Option.unless(
                  written.getOrElse(location, Set.empty).contains(own(subterm))
                )(
                  s"step $step at $position: $location shows the layer of $subterm"
                )
              )
            )
          }
        Result
          .assert(problems.isEmpty)
          .log(problems.mkString("\n"))
          .log(s"located places per step: $located")
      )
  }

  stoppableProperty(
    "a step keeps the maps off its position and copies the maps its provenance moves"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val (_, _, steps, maps) = carried(program, stopped)
        val problems = steps.zip(maps.zip(maps.tail)).zipWithIndex.flatMap {
          case ((step, (before, after)), place) =>
            val position = step.command.at
            val offPosition = position.indices.flatMap(depth =>
              val prefix = position.take(depth)
              Positions
                .roles(
                  Positions.layerOf(Positions.subterm(step.before, prefix))
                )
                .filterNot(_ == position(depth))
                .flatMap(role =>
                  Option.unless(
                    TraceSourceMaps.at(
                      before,
                      step.before,
                      prefix :+ role
                    ) == TraceSourceMaps.at(after, step.after, prefix :+ role)
                  )(s"step $place: the map at ${prefix :+ role} changed")
                )
            )
            val moved = step.provenance.flatMap(found =>
              found.before.headOption.toVector.flatMap(from =>
                found.after.flatMap(to =>
                  Option.unless(
                    TraceSourceMaps.at(
                      before,
                      step.before,
                      position ++ from
                    ) == TraceSourceMaps.at(after, step.after, position ++ to)
                  )(
                    s"step $place: ${found.variable} moved from $from to $to without its map"
                  )
                )
              )
            )
            offPosition ++ moved
        }
        val movedCount = steps.map(_.provenance.map(_.after.size).sum).sum
        Result
          .assert(problems.isEmpty)
          .log(problems.mkString("\n"))
          .log(s"${steps.size} steps, $movedCount subtrees moved")
      )
  }

  /** Purpose: catch a writer and a reader of lemmas written from their files
    * (`TraceText.writtenWith`, `readLocated`) that disagree: a lemma whose
    * text, its names bound by the β redex, reads as other sides, or a location
    * written otherwise than it is read; and a side's map
    * (`LocatedTrace.lemmaMaps`) that the printer cannot print it with
    * (`ReadableText.printed`), prints as another term, or names the side's own
    * binders otherwise than the lemma's text does, or, for the trace written
    * with no lemma's text, otherwise than the side's closed text does, such as
    * by the names of an equal term elsewhere in the lemma's item.
    */
  stoppableProperty(
    "a trace written with its lemmas' texts reads back as the trace, with their locations and names"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val (_, trace) = traced(program, stopped)
        val written = TraceText.writtenWith(trace, lemmaTexts)
        val located = TraceText
          .readLocated(written, RewriteTraceLawTest.readingLimit(written))
        val expected = trace.lemmas.map(lemma =>
          lemmaTexts
            .get((lemma.left, lemma.right))
            .map(text =>
              com.yang_bo.gezi.rewritetrace.LemmaLocation(
                text.uri,
                com.yang_bo.gezi.locations.Span(text.left.start, text.right.end)
              )
            )
        )
        val sides = trace.lemmas.zip(located.lemmaMaps).flatMap {
          case (lemma, (leftMap, rightMap)) =>
            val text = lemmaTexts.get((lemma.left, lemma.right))
            Vector(
              (lemma.left, leftMap, text.map(_.leftText)),
              (lemma.right, rightMap, text.map(_.rightText))
            )
        }
        // The same trace written with no lemma's text: each side is written as its closed text
        // (`Lambdalattice.closedText`), in an item whose tag `λh0. λh1. h0` is the instruction of a side `λa. λb. a`,
        // so each side's own names are those of its closed text.
        val nameless = TraceText.written(trace)
        val namelessSides = trace.lemmas
          .zip(
            TraceText
              .readLocated(nameless, RewriteTraceLawTest.readingLimit(nameless))
              .lemmaMaps
          )
          .flatMap { case (lemma, (leftMap, rightMap)) =>
            Vector((lemma.left, leftMap), (lemma.right, rightMap)).map(
              (side, map) =>
                (side, map, Some(com.yang_bo.gezi.frontend.Lambdalattice.closedText(side)))
            )
          }
        val misprinted =
          (sides ++ namelessSides).flatMap((side, map, sideText) =>
            val printed = com.yang_bo.gezi.frontend.ReadableText.printed(side, map)
            val again = readBack(printed)
            val ownNames = map.binders.flatten.collect {
              case com.yang_bo.gezi.locations.BinderOrigin.Written(name, _) => name
            }
            val unwritten = sideText.toVector
              .flatMap(text => ownNames.filterNot(text.contains))
            Option.unless((again eq side) && unwritten.isEmpty)(
              s"${printed.text} reads as $again, names not in the side's text: $unwritten"
            )
          )
        Result
          .all(
            List(
              Result.diff(located.trace, trace)(_ == _),
              Result.diff(located.lemmaLocations, expected)(_ == _),
              Result
                .assert(trace.lemmas.isEmpty || expected.exists(_.isDefined))
                .log("no lemma of the trace has a text"),
              Result.assert(misprinted.isEmpty).log(misprinted.mkString("\n"))
            )
          )
          .log(written)
      )
  }

  /** The instruction a printed text reads back to, its bindings contracted
    * (`ReadableText.contracted`).
    */
  private def readBack(
      printed: com.yang_bo.gezi.frontend.ReadableText.Printed[NoFacts.type]
  ): Configured[NoFacts.type] =
    val read: Configured[NoFacts.type] =
      com.yang_bo.gezi.frontend.Defunctionalization.thunkInstruction[com.yang_bo.gezi.ir.NoFacts.type](
        com.yang_bo.gezi.frontend.Lambdalattice.term(printed.text)
      )(using com.yang_bo.gezi.ir.NoFacts)
    (1 to printed.bindings).foldLeft(read)((term, _) =>
      com.yang_bo.gezi.frontend.ReadableText
        .contracted(term, com.yang_bo.gezi.locations.SourceMap.unlocated)
        .getOrElse(
          throw AssertionError(
            s"a printed binding is no (λt. t V) λm. BODY: $term"
          )
        )
        ._1
    )

  /** The subterm at a path of `Layer.children` indices, the path the player
    * keys its nodes by.
    */
  private def atPath(
      term: Configured[NoFacts.type],
      path: Vector[Int]
  ): Option[Configured[NoFacts.type]] =
    path.foldLeft(Option(term))((found, index) =>
      found.flatMap(subterm =>
        if subterm.opaque then None else subterm.layer.children.lift(index)
      )
    )

  /** Purpose: catch a move (`TraceSourceMaps.moves`, what the player's
    * transition flies) whose paths do not take a subtree of the term before the
    * step to the same subtree of the term after it: a path computed in the
    * wrong term, or a position turned into another node's path.
    */
  stoppableProperty(
    "a step's moves take each moved subtree from its node before the step to its node after it"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val (_, _, steps, _) = carried(program, stopped)
        val problems = steps.zipWithIndex.flatMap((step, place) =>
          TraceSourceMaps
            .moves(step)
            .flatMap((from, to) =>
              (atPath(step.before, from), atPath(step.after, to)) match
                case (Some(moved), Some(arrived)) if moved eq arrived => None
                case found => Some(s"step $place: $from to $to finds $found")
            )
        )
        val count = steps.map(TraceSourceMaps.moves(_).size).sum
        Result
          .assert(problems.isEmpty)
          .log(problems.mkString("\n"))
          .log(s"$count moves in ${steps.size} steps")
      )
  }

  /** Purpose: catch a step that builds a binder the carried map gives no
    * origin: the printer names every binder from its origins and has no
    * fallback name, so it throws at such a binder (`ReadableText.printed`).
    */
  stoppableProperty(
    "every binder of every step's term has an origin in its carried map"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val (start, _, steps, maps) = carried(program, stopped)
        val terms = start +: steps.map(_.after)
        val printed = terms
          .zip(maps)
          .map((term, map) => com.yang_bo.gezi.frontend.ReadableText.printed(term, map))
        Result.success.log(s"${printed.size} terms printed")
      )
  }

  /** The text of each step of the trace of a round, read with the start's map
    * (`TraceStart.readLocated` of the start written from the program's source):
    * the start, then each step's label and its term, printed with the names the
    * carried map gives its binders (`ReadableText.printed`); a lemma's label
    * shows its sides printed with the names of the trace written with the
    * lemmas' texts (`LocatedTrace.lemmaMaps`).
    */
  private def namedSteps(
      program: String,
      input: Configured[NoFacts.type],
      output: Configured[NoFacts.type],
      proof: com.yang_bo.gezi.proofs.StrategyProof[NoFacts.type],
      index: StandardLibraryIndex[NoFacts.type]
  ): String =
    val trace = RewriteTrace.trace(
      OpentheoryArticle.derivation(index, input, output, proof)
    )
    val start = TraceStart.readLocated(
      TraceStart.written(input, Some(program)),
      java.net.URI("trace:start")
    )
    val text = TraceText.writtenWith(trace, lemmaTexts)
    val located =
      TraceText.readLocated(text, RewriteTraceLawTest.readingLimit(text))
    val steps = located.trace.replayed(start.start).flatten
    val maps = TraceSourceMaps.carried(start.map, steps)
    val lemmasShown =
      located.trace.lemmas.zip(located.lemmaMaps).zipWithIndex.map {
        case ((lemma, (leftMap, rightMap)), place) =>
          s"lemma ${place + 1}: ${com.yang_bo.gezi.frontend.ReadableText.printed(lemma.left, leftMap).text} = " +
            com.yang_bo.gezi.frontend.ReadableText.printed(lemma.right, rightMap).text
      }
    val labels = "start" +: steps.map(step =>
      TraceSourceMaps.labelWith(step.command, lemmasShown)
    )
    val terms = start.start +: steps.map(_.after)
    labels
      .zip(terms.zip(maps))
      .map { case (label, (term, map)) =>
        s"$label\n  ${com.yang_bo.gezi.frontend.ReadableText.printed(term, map).text}"
      }
      .mkString("\n")

  /** Purpose: show, as a diff, the names each step's term is printed with: the
    * source's names carried through the first-order rounds' steps.
    */
  stoppableTest("the names of each step of first-order rounds' traces") {
    stopped =>
      assertSeededSnapshot(
        programs,
        20261119L,
        4,
        "trace-source-maps/first-order-names.txt"
      )(identity, identity[String])(program =>
        val input = closed(program)
        val outcome = strategy
          .ran(Vector(input), true, StopSignal.completedWith(stopped))
          .getOrElse(fail("the strategy gave no answer"))
        val Vector(output) = outcome.outputs: @unchecked
        namedSteps(
          program,
          input,
          output,
          outcome.proof.getOrElse(fail("the strategy gave no proof")),
          index
        )
      )
  }

  /** Purpose: show, as a diff, the names each step's term is printed with on
    * higher-order rounds (`RewriteTraceLawTest.higherOrderPrograms`), whose β
    * conversions and reverse β conversions build thunks no text wrote, their
    * binders named by the kind of step (`BinderOrigin.Made`).
    */
  stoppableTest("the names of each step of higher-order rounds' traces") {
    stopped =>
      assertSeededSnapshot(
        RewriteTraceLawTest.higherOrderPrograms,
        20261119L,
        4,
        "trace-source-maps/higher-order-names.txt"
      )(
        identity,
        identity[String]
      )(program =>
        val (input, output, proof) =
          RewriteTraceLawTest.higherOrderRan(program, stopped)
        namedSteps(
          program,
          input,
          output,
          proof,
          RewriteTraceLawTest.higherOrderIndex
        )
      )
  }
