package gezi.traceplayer

import gezi.ir.{Configured, NoFacts}
import gezi.frontend.LambdaError
import gezi.frontend.LambdalatticeMalformed
import gezi.frontend.ReadableText
import gezi.knowledgereading.KnowledgeReadingError
import gezi.locations.SourceMap
import gezi.locations.Span
import gezi.rewritetrace.ReplayedStep
import gezi.rewritetrace.TraceSourceMaps
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText

/** The configuration of the terms here: no facts. */
private given traceReadingNoFacts: NoFacts.type = NoFacts

/** The steps a page plays, read from its start's text and its trace's text
  * and replayed: the pure part of reading a page, run by the tests on Node.js.
  *
  * The trace holds only the commands (no IR and no start),
  * so every step's
  * term is computed here by the replay from the start (`Trace.replayed`), the
  * same replay the writer checks the trace against.
  *
  * The start is read with its places in its text (`TraceStart.readLocated`),
  * so that the player names the start's binders as the text does and shows
  * where each node comes from: the source's own names when the start was
  * written from its source (`TraceStart.written`), and its map is carried through the steps
  * (`TraceSourceMaps`), so that a subterm a step moves keeps its names and
  * places, and the node a step puts there is marked. A step by a lemma is
  * labelled with the lemma's two sides printed (`ReadableText`), named from the trace's text (`LocatedTrace.lemmaMaps`), its
  * location not shown. The library terms the lemmas' texts name, and those
  * the start's bindings name, are bound by those names at the start of
  * each side of a label and of every step's text
  * (`ReadableText.KnownNames.Bound`; `LocatedTrace.names`,
  * `LocatedStart.names`),
  * so that each is a
  * closed term.
  */
object TraceReading:

  /** The trace's steps replayed from the start, the start first and then
    * the step of each command of each round in order (`Played`); or the reader's
    * error, for either text. The reader's
    * errors, `LambdalatticeMalformed` (syntax), `LambdaError` (a term that is
    * not closed) and `KnowledgeReadingError` (a text of another shape, or one
    * that reads past its budget), are caught here and nowhere else: the page
    * shows them, with their places and reasons, in place of the picture, and
    * never half a picture. A trace that reads but does not replay is a
    * defect of its writer and throws.
    */
  def played(startText: String, traceText: String): Either[Unreadable, Played] =
    try
      val start = TraceStart.readLocated(startText, startUri)
      val located = TraceText.readLocated(traceText, readingLimit(traceText))
      val rounds = located.trace.replayed(start.start)
      val steps = rounds.flatten
      val lemmasShown = located.trace.lemmas.zip(located.lemmaMaps).zipWithIndex.map { case ((lemma, (leftMap, rightMap)), index) =>
        val known = ReadableText.KnownNames.Bound(located.names)
        s"lemma ${index + 1}: ${ReadableText.printed(lemma.left, leftMap, known).text} = ${ReadableText.printed(lemma.right, rightMap, known).text}"
      }
      Right(
        Played(
          start.start,
          steps,
          None +: rounds.zipWithIndex.flatMap((round, index) =>
            round.map(step => Some(s"Round ${index + 1}: ${TraceSourceMaps.labelWith(step.command, lemmasShown)}"))
          ),
          StartSource(codePoints(startText), Span(0, codePoints(startText).size), start.map),
          TraceRounds(rounds.map(_.size)),
          start.names ++ located.names
        )
      )
    catch
      case malformed: LambdalatticeMalformed => Left(Unreadable(malformed.getMessage))
      case error: LambdaError                => Left(Unreadable(error.getMessage))
      case shape: KnowledgeReadingError      => Left(Unreadable(shape.getMessage))

  /** The evaluator steps reading a text may take: the trace text's own
    * limit (`TraceText.readingLimit`, one step per character and 32 more per
    * character of a string literal, with its measurements).
    */
  def readingLimit(text: String): Long = TraceText.readingLimit(text)

  /** The URI the start's places are located under: the page's own start. */
  val startUri: java.net.URI = java.net.URI("trace:start")

  /** The code points of the text, in which the reader counts its spans. */
  def codePoints(text: String): Vector[Int] =
    @scala.annotation.tailrec
    def from(index: Int, found: Vector[Int]): Vector[Int] =
      if index >= text.length then found
      else
        val codePoint = text.codePointAt(index)
        from(index + Character.charCount(codePoint), found :+ codePoint)
    from(0, Vector.empty)

/** The steps of a page, step k showing term k: the start, then the term
  * after each replayed step; what a person reads of the command that made
  * each step's term (`TraceSourceMaps.label`), none for the start; the
  * source of the start, whose map the steps carry; and the number of steps
  * of each round, by which the hash counts (`TraceRounds`); and the library
  * terms the trace's lemmas and the start's bindings name, by which a step's
  * text names them (`LocatedTrace.names`, `LocatedStart.names`). A step's term, its source
  * map (carried from the start's, `TraceSourceMaps.carriedLazily`), the path
  * of the node its command put there (`TraceSourceMaps.path`) and the
  * subtrees that command moved (`TraceSourceMaps.moves`, from a path in the
  * term before to a path in this term) are made when the step is shown: a
  * trace of many steps over a wide term, such as the 117,310 commands of
  * `contest-entries-solo`'s repeated_library_hotspots calls_1000 direct point (seed 20261116)
  * over a top-level thunk of 2,468 fillings, would cost the steps times the
  * width to make every term whole (the FIXME this replaced, 2026-11-18).
  */
final case class Played(
    start: Configured[NoFacts.type],
    steps: Vector[ReplayedStep[NoFacts.type]],
    labels: Vector[Option[String]],
    source: StartSource,
    rounds: TraceRounds,
    names: Map[Configured[NoFacts.type], String]
):
  require(labels.size == steps.size + 1, s"${labels.size} labels for ${steps.size + 1} terms")
  require(rounds.sizes.sum == steps.size, s"rounds of ${rounds.sizes.sum} steps for ${steps.size} steps")

  /** The number of terms: the start and one after each step. */
  def size: Int = steps.size + 1

  /** The term step k shows. */
  def term(step: Int): Configured[NoFacts.type] = if step == 0 then start else steps(step - 1).after

  /** The source map of the term step k shows. */
  def map(step: Int): SourceMap = maps(step)

  /** The path of the node the command that made step k's term put there,
    * none for the start.
    */
  def rewritten(step: Int): Option[Vector[Int]] =
    Option.when(step > 0)(TraceSourceMaps.path(steps(step - 1).after, steps(step - 1).command.at))

  /** The subtrees the command that made step k's term moved, none for the
    * start.
    */
  def moves(step: Int): Vector[(Vector[Int], Vector[Int])] =
    if step == 0 then Vector.empty else TraceSourceMaps.moves(steps(step - 1))

  private lazy val maps: LazyList[SourceMap] = TraceSourceMaps.carriedLazily(source.map, steps)

/** The page's text that the reader rejects, with its error. */
final case class Unreadable(error: String)
