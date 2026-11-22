package gezi.migration

import gezi.egraph.EGraph
import gezi.ematching.Match
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ematching.CompiledProgram
import gezi.ematching.Program
import gezi.ematching.closures.ClosureCompilation
import gezi.ematching.indexing.Indexing
import gezi.frontend.Defunctionalization
import gezi.frontend.FreeNames
import gezi.frontend.Lambdalattice
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.locations.Location
import gezi.locations.Span
import gezi.orientation.LemmaSides
import gezi.orientation.OrientationCompilation
import gezi.orientation.Orientations
import gezi.provenance.Provenance
import gezi.saturation.Saturation
import gezi.saturation.StopSignal
import scala.util.matching.Regex
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** A place the migration rewrote: the span of the matched text in the text
  * given, and the span of its replacement in the text migrated.
  */
final case class Site(original: Span, replaced: Span)

/** A migrated text and the places rewritten, in the order of the text. */
final case class Migrated(text: String, sites: Vector[Site])

/** The migration of a lambdalattice text by a lemma L = R, read from left
  * to right: each outermost occurrence of an instance of L in the text
  * replaced by the instance of R.
  *
  *   1. The text is read with its source map and added to an e-graph.
  *   2. One round of matching of L's orientation from left to right on the
  *      nodes the text located, by the matching program's public entry
  *      (`CompiledProgram.matches`) under the keys `SeedKey` lists; nothing
  *      is saturated.
  *   3. A match at a node with a span of the text is a site, each span of the
  *      node one site; a site inside another is left for a later round.
  *   4. R is written by the reader's printer (`Lambdalattice.text`), each
  *      metavariable as the text of its binding inside the site, which is
  *      closed, copied from the text and put in parentheses; R's binders are
  *      the printer's, and since R and the copied texts are closed, none
  *      captures a name. Of the parentheses the migration put in, around the
  *      replacement and around each copied text, those the text does not
  *      need are removed (`SpellingMigration.parenthesesRemoved`); the copied
  *      texts are kept as written.
  *   5. The migrated text is read and added to the e-graph of the original,
  *      saturated by the same orientation within the budget: the two must be
  *      one class, which the instances of L = R join. Text outside the sites
  *      is copied unchanged.
  *
  * The lemma is the caller's and is sound by Definition 14; the check of 5
  * catches a migration that did not write the instances it matched. A site
  * whose metavariable has no span inside it, which only a binding the text
  * does not spell has, is not rewritten. Only closed texts are read
  * (`FreeNames.Rejected`).
  */
object TermMigration:

  /** The text migrated by one round of the lemma read from left to right.
    * Throws the reader's errors when the text does not read,
    * `IllegalArgumentException` when the lemma has no orientation from
    * left to right, and `IllegalStateException` when the migrated text and
    * the original are not one class within the budget's instances.
    */
  def migrated(text: String, uri: java.net.URI, lemma: LemmaSides, store: Store, budget: Int): Migrated =
    val located = Lambdalattice.located(text, FreeNames.Rejected)
    val (instruction, map) = Defunctionalization.locatedThunkInstruction(located.term, located.spans, uri)
    val compiledOrientations = OrientationCompilation.compiled(Vector(lemma), store)
    val forward = compiledOrientations.orientations
      .filter(_.direction == Direction.Forward)
      .zipWithIndex
      .map((orientation, index) => orientation.copy(index = index))
    require(forward.nonEmpty, s"the lemma ${lemma.lemma} has no orientation from left to right")
    val program = Indexing.program(
      forward,
      Indexing.codesMet(forward, compiledOrientations.patternInstructions :+ instruction)
    )
    val compiled = ClosureCompilation.compiled(program)
    val initial =
      Saturation.initialGraph(store, Orientations.headArityBounds(forward), compiledOrientations.patternInstructions, explained = false)
    val (withInput, _) = Saturation.inputsAdded(initial, Vector(instruction))
    val graph = Saturation.agendaWorked(program, compiled, Set.empty, withInput)
    val provenance = Provenance.of(graph, Vector(Provenance.Input(instruction, map)), Map.empty)
    val codePoints = SpellingMigration.codePointsOf(text)
    // A duplicate's layer over the roots is its twin's, so matching it would
    // only repeat its twin's sites.
    val found = (0 until graph.nodeCount).toVector.filter(graph.live).flatMap(node =>
      val spans = sourceSpans(provenance.node(node), uri)
      if spans.isEmpty then Vector.empty
      else matchesAt(compiled, graph, node).flatMap(matched => spans.map(span => (span, matched)))
    )
    val sites = outermost(found.flatMap((span, matched) =>
      replacement(lemma.right, matched, span, provenance, uri, codePoints).map(span -> _)
    ))
    val (edited, regions, inserted) = sitesReplaced(codePoints, sites)
    val (migratedText, replaced) =
      SpellingMigration.parenthesesRemoved(SpellingMigration.textOf(edited), inserted, regions)
    checked(text, migratedText, program, compiled, initial, instruction, budget)
    Migrated(migratedText, sites.map(_._1).zip(replaced).map(Site(_, _)))

  /** The matches at the node under every key `SeedKey` files it under: an
    * application under `Apply` and its heads, another layer under its
    * shape, a class holding a closure state under `Closure`, and an instruction's
    * node under the instruction; each under both kinds of seeds (`SeedKind`),
    * which are the orientations' kinds, a new node being matched by both,
    * the instruction's key under `Add` only, where the indexer files it.
    */
  private def matchesAt(compiled: CompiledProgram, graph: EGraph, node: Int): Vector[Match] =
    val shapeKeys = graph.layer(node) match
      case Apply(_, _)           => SeedKey.Apply +: graph.nodeHeads(node).map(SeedKey.Headed(_))
      case Parallel(_, _)        => Vector(SeedKey.Parallel)
      case Choice(_, _)          => Vector(SeedKey.Choice)
      case Thunk(code, holes, _) => Vector(SeedKey.Thunk(code, holes))
      case NoinlineLeaf(_)               => Vector.empty
    val closure = if graph.hasClosure(graph.root(node)) then Vector(SeedKey.Closure) else Vector.empty
    val instructionKeys = graph.nodeInstruction(node).toVector.map(SeedKey.InstructionNode(_))
    val keyed = Vector(SeedKind.Merge, SeedKind.Add).flatMap(kind => (shapeKeys ++ closure).map(kind -> _)) ++
      instructionKeys.map(SeedKind.Add -> _)
    keyed.flatMap((kind, key) => compiled.matches(kind, key, graph, node).found)

  private def sourceSpans(locations: Set[Location], uri: java.net.URI): Vector[Span] =
    locations.toVector.collect { case Location.Source(source, span) if source == uri => span }.sortBy(_.start)

  /** A replacement's code points and the pairs of parentheses the
    * migration put in it, the spans relative to its start.
    */
  private final case class Replacement(codePoints: Vector[Int], parentheses: Vector[Span])

  /** The text of R at the site, in parentheses: each metavariable the text
    * of its binding inside the site, copied as it is, in parentheses; none
    * when a metavariable R mentions has no such span.
    */
  private def replacement(
      right: Pattern,
      found: Match,
      site: Span,
      provenance: Provenance,
      uri: java.net.URI,
      codePoints: Vector[Int]
  ): Option[Replacement] =
    val slices = found.bindings.map(
      _.flatMap(node => sourceSpans(provenance.node(node), uri).find(site.contains))
        .map(span => codePoints.slice(span.start, span.end))
    )
    val mentioned = metavariables(right)
    Option.when(mentioned.forall(index => slices.lift(index).flatten.isDefined)) {
      val placeholders = Vector.tabulate(found.bindings.size)(index => Instruction.opaque(placeholderName(index)))
      val printed = Lambdalattice.text(
        Defunctionalization.instructionTerm(instantiated(right, placeholders)),
        placeholders.zipWithIndex.map((placeholder, index) => placeholder -> placeholderName(index)).toMap
      )
      val open = Vector('('.toInt)
      val (spliced, pairs, copiedTo) =
        placeholderPattern.findAllMatchIn(printed).foldLeft((open, Vector.empty[Span], 0)) {
          case ((made, pairs, from), written) =>
            val slice = slices(written.group(1).toInt).getOrElse(
              throw IllegalStateException(s"no text for the metavariable ${written.group(1)}")
            )
            val before = made ++ SpellingMigration.codePointsOf(printed.substring(from, written.start))
            val after = before ++ open ++ slice :+ ')'.toInt
            (after, pairs :+ Span(before.size, after.size), written.end)
        }
      val whole = spliced ++ SpellingMigration.codePointsOf(printed.substring(copiedTo)) :+ ')'.toInt
      Replacement(whole, Span(0, whole.size) +: pairs)
    }

  /** The name a metavariable is printed as: no such name is a prefix of
    * another, and the printer names binders `x_L`.
    */
  private def placeholderName(index: Int): String = s"metavariable_${index}_"

  private val placeholderPattern: Regex = """metavariable_(\d+)_""".r

  private def metavariables(pattern: Pattern): Set[Int] = pattern match
    case Pattern.Metavariable(index) => Set(index)
    case other                       => other.children.flatMap(metavariables).toSet

  /** The instruction of the pattern, each metavariable the instruction
    * given for it. Throws `IllegalArgumentException` for a closure, which no
    * lemma side holds (`LemmaSides`).
    */
  private[migration] def instantiated(pattern: Pattern, values: Vector[Instruction]): Instruction = pattern match
    case Pattern.Metavariable(index)          => values(index)
    case Pattern.InstructionReference(instruction) => instruction
    case Pattern.Apply(function, argument) =>
      Instruction(Apply(instantiated(function, values), instantiated(argument, values)))
    case Pattern.Choice(left, right) =>
      Instruction(Choice(instantiated(left, values), instantiated(right, values)))
    case Pattern.Parallel(left, right) =>
      Instruction(Parallel(instantiated(left, values), instantiated(right, values)))
    case Pattern.Thunk(code, holes, fillings) =>
      Instruction(Thunk(code, holes, fillings.map(instantiated(_, values))))
    case Pattern.Closure(index) => throw IllegalArgumentException(s"a lemma side holds the closure $index")

  /** The sites no other site contains, one for each span, in the order of
    * the text.
    */
  private def outermost(sites: Vector[(Span, Replacement)]): Vector[(Span, Replacement)] =
    val spans = sites.map(_._1).distinct
    sites
      .filter((span, _) => !spans.exists(other => other != span && other.contains(span)))
      .groupBy(_._1)
      .values
      .flatMap(_.headOption)
      .toVector
      .sortBy(_._1.start)

  /** The code points with each site's span replaced, the spans of the
    * replacements in the text made, and the pairs of parentheses the
    * replacements put there.
    */
  private def sitesReplaced(
      codePoints: Vector[Int],
      sites: Vector[(Span, Replacement)]
  ): (Vector[Int], Vector[Span], Vector[Span]) =
    val (edited, regions, pairs, _) =
      sites.foldLeft((Vector.empty[Int], Vector.empty[Span], Vector.empty[Span], 0)) {
        case ((made, regions, pairs, copiedTo), (span, written)) =>
          val before = made ++ codePoints.slice(copiedTo, span.start)
          (
            before ++ written.codePoints,
            regions :+ Span(before.size, before.size + written.codePoints.size),
            pairs ++ written.parentheses.map(pair => Span(before.size + pair.start, before.size + pair.end)),
            span.end
          )
      }
    (edited ++ codePoints.drop(sites.lastOption.fold(0)(_._1.end)), regions, pairs)

  /** Throws `IllegalStateException` when the migrated text's term and the
    * original are not one class of the graph of both saturated by the
    * orientation within the budget's instances.
    */
  private def checked(
      text: String,
      migratedText: String,
      program: Program,
      compiled: CompiledProgram,
      initial: EGraph,
      instruction: Instruction,
      budget: Int
  ): Unit =
    val migratedInstruction = Defunctionalization.thunkInstruction(Lambdalattice.term(migratedText))
    val run = Saturation.runFrom(
      program,
      compiled,
      Set.empty,
      initial,
      Vector(instruction, migratedInstruction),
      budget,
      StopSignal.NeverStopped
    )
    val Vector(original, migrated) = run.inputNodes: @unchecked
    if run.graph.root(original) != run.graph.root(migrated) then
      throw IllegalStateException(
        s"the migration of `$text` to `$migratedText` is not one class with it within ${run.end}"
      )
