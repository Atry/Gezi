package com.yang_bo.gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.FreeNames
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.rewritetrace.Trace
import com.yang_bo.gezi.rewritetrace.TraceStart
import com.yang_bo.gezi.rewritetrace.TraceText

private given sourceNamesLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of a trace's start written from its source (`TraceStart.written`)
  * and drawn with the source's names (`StartSource`, `CodeDisplay`), on
  * generated programs whose source names every binder by a generated name:
  *
  *   1. the text written from the source reads back as the start;
  *   2. every binder of the start's thunks and of their codes, read or not, is
  *      drawn with the name the source writes at it, at one of the occurrences
  *      the IR holds as one place (`misnamed`), none with the player's own and
  *      none with another binder's;
  *   3. the start drawn with those names, read as a lambdalattice text, is the
  *      start, so that a name drawn for one binder and spelled in the source by
  *      another would read back as another term.
  *
  * Purpose: catch a start written otherwise than its source, a binder whose
  * source name the player loses, and a name the player gives the wrong binder.
  */
class SourceNamesLawTest extends GeneratedProperties:

  /** A generated program and its source, the binder at depth d named by the
    * word drawn for d followed by d, so that a binder's name says the depth it
    * stands at (`misnamed`). The source is written here, every construct in
    * parentheses, rather than by `LambdalatticeText`, which reuses a name where
    * no capture follows.
    */
  private val sources: Gen[(Configured[NoFacts.type], String)] =
    for
      term <- HoasGenerators.closedTerm
      words <- Gen
        .string(Gen.lower, Range.linear(1, 4))
        .list(Range.singleton(64))
    yield
      val source = written(
        LambdalatticeText.closedInstructionsWrittenOut(
          term.deBruijnTerm(Map.empty)
        ),
        words,
        0
      )
      (
        Defunctionalization.thunkInstruction(Lambdalattice.term(source))(using
          com.yang_bo.gezi.ir.NoFacts
        ),
        source
      )

  /** The text of a de Bruijn term under `depth` binders, the binder at depth d
    * named `words(d)` followed by d. Recursive on the term's depth: a generated
    * term is small.
    */
  private def written(
      term: DeBruijnTerm,
      words: List[String],
      depth: Int
  ): String =
    def name(at: Int): String = s"${words(at)}$at"
    term match
      case DeBruijnTerm.Lambda(body) =>
        s"(λ${name(depth)}. ${written(body, words, depth + 1)})"
      case DeBruijnTerm.Variable(index)           => name(depth - 1 - index)
      case DeBruijnTerm.Apply(function, argument) =>
        s"(${written(function, words, depth)} ${written(argument, words, depth)})"
      case DeBruijnTerm.Choice(left, right) =>
        s"(${written(right, words, depth)} + ${written(left, words, depth)})"
      case DeBruijnTerm.Parallel(left, right) =>
        s"(${written(left, words, depth)} ∥ ${written(right, words, depth)})"
      case other =>
        throw IllegalStateException(s"a generated closed term holds $other")

  property("a start written from its source reads back as the start") {
    for (start, source) <- sources.forAllWithLog(_._2)
    yield
      val text = TraceStart.written(start, Some(source))
      Result.diff(
        TraceStart.readLocated(text, TraceReading.startUri).start,
        start
      )(_ eq _)
  }

  property(
    "every binder of the start is drawn with its source's name, and the drawing reads back as the start"
  ) {
    for (start, source) <- sources.forAllWithLog(_._2)
    yield
      val startText = TraceStart.written(start, Some(source))
      TraceReading.played(
        startText,
        TraceText.written(Trace(Vector.empty, Vector.empty, Vector.empty))
      ) match
        case Left(unreadable) => Result.failure.log(unreadable.error)
        case Right(played)    =>
          val read = Lambdalattice.located(source, FreeNames.Rejected)
          val (_, sourceMap) = Defunctionalization.locatedThunkInstruction(
            read.term,
            read.spans,
            sourceUri
          )(using com.yang_bo.gezi.ir.NoFacts)
          val (drawn, misnamed) =
            drawing(
              start,
              played.map(0),
              played.source,
              openings(start, sourceMap, TraceReading.codePoints(source)),
              0,
              Set(0)
            )
          val again = Defunctionalization.thunkInstruction(
            Lambdalattice.term(drawn)
          )(using com.yang_bo.gezi.ir.NoFacts)
          Result
            .all(
              List(
                Result
                  .diff(misnamed, Vector.empty[String])(_ == _)
                  .log("binders drawn with another name than the source's"),
                Result.diff(again, start)(_ eq _).log(s"the drawing: $drawn")
              )
            )
  }

  /** The URI the generated source is read under for its own map. */
  private val sourceUri: java.net.URI = java.net.URI("test:source")

  /** For each instruction of the start, the number of the source's abstractions
    * open at each of its occurrences that the source's own map locates: the
    * source reads as the start, so its map has the start's places, located in
    * the source rather than in the start's text, which the printer writes
    * (`TraceStart.written`). An instruction is interned, so its occurrences are
    * one, and the printer names it after one of them. Recursive on the start's
    * depth: a generated term is small.
    */
  private def openings(
      instruction: Configured[NoFacts.type],
      map: SourceMap,
      codePoints: Vector[Int]
  ): Map[Configured[NoFacts.type], Set[Int]] =
    val here = map.locations.collect {
      case com.yang_bo.gezi.locations.Location.Source(_, span) =>
        openAt(codePoints, span.start)
    }
    val parts = instruction.layer match
      case com.yang_bo.gezi.ir.Apply(function, argument) => Vector(function, argument)
      case com.yang_bo.gezi.ir.Choice(left, right)       => Vector(left, right)
      case com.yang_bo.gezi.ir.Parallel(left, right)     => Vector(left, right)
      case com.yang_bo.gezi.ir.Thunk(_, _, fillings)     => fillings
      case other                             =>
        throw IllegalStateException(s"a generated start holds $other")
    parts.zipWithIndex.foldLeft(Map(instruction -> here)) {
      case (found, (part, index)) =>
        openings(
          part,
          map.children.lift(index).getOrElse(SourceMap.unlocated),
          codePoints
        ).foldLeft(found) { case (current, (inner, depths)) =>
          current.updated(inner, current.getOrElse(inner, Set.empty) ++ depths)
        }
    }

  /** The number of the source's abstractions open at the offset, counted from
    * the source's first code point: the source writes every abstraction as
    * `(λname. body)` (`written`), and a place's span begins at the λ of its
    * first abstraction, after that abstraction's parenthesis.
    */
  private def openAt(codePoints: Vector[Int], offset: Int): Int =
    codePoints
      .take(offset)
      .indices
      .foldLeft(List.empty[Boolean]) { (open, at) =>
        val point = codePoints(at)
        if point == '('.toInt then
          (codePoints
            .lift(at + 1)
            .contains('λ'.toInt) && at + 1 < offset) :: open
        else if point == ')'.toInt then open.drop(1)
        else open
      }
      .count(identity)

  /** Whether a binder drawn at the depth has a name the source writes at it:
    * the source names the binder at depth d with a word followed by d
    * (`sources`), and a place stands at the depth it is drawn at shifted by one
    * of `shifts`. A place is shifted when the IR holds several occurrences of
    * it as one: α-equivalent closed subterms are one interned filling (`λa1.
    * a1` and `λa2. a2` under
    * `λa0. ((λa1. ((a0 a0) ((λa2. a2) a0))) + (λa1. a1))`, HEDGEHOG_SEED
    * 1665308405), drawn once with the names of one of its occurrences.
    */
  private def misnamed(
      name: String,
      depth: Int,
      shifts: Set[Int]
  ): Option[String] =
    val digits = name.reverse.takeWhile(_.isDigit).reverse
    Option.unless(
      name.exists(_.isLetter) && shifts.exists(shift =>
        digits == (depth + shift).toString
      )
    )(
      s"$name at depth $depth, shifts $shifts"
    )

  /** The shifts of an instruction drawn at the depth: for each located
    * occurrence of it in the source (`openings`), the number of the source's
    * abstractions open there, less the depth; `inherited` for an instruction
    * the source's map locates nowhere.
    */
  private def shifts(
      instruction: Configured[NoFacts.type],
      openings: Map[Configured[NoFacts.type], Set[Int]],
      depth: Int,
      inherited: Set[Int]
  ): Set[Int] =
    val depths = openings.getOrElse(instruction, Set.empty)
    if depths.isEmpty then inherited else depths.map(_ - depth)

  /** The start as the player draws it, written as a lambdalattice text, its
    * binders counted from `depth`, and the binders drawn with another name than
    * the source writes at them.
    */
  private def drawing(
      instruction: Configured[NoFacts.type],
      map: SourceMap,
      source: StartSource,
      openings: Map[Configured[NoFacts.type], Set[Int]],
      depth: Int,
      inherited: Set[Int]
  ): (String, Vector[String]) =
    def under(index: Int): SourceMap =
      map.children.lift(index).getOrElse(SourceMap.unlocated)
    val here = shifts(instruction, openings, depth, inherited)
    if instruction.opaque then
      throw IllegalStateException(
        s"a generated start holds the opaque $instruction"
      )
    instruction.layer match
      case com.yang_bo.gezi.ir.Apply(function, argument) =>
        val (functionText, functionMisnamed) =
          drawing(function, under(0), source, openings, depth, here)
        val (argumentText, argumentMisnamed) =
          drawing(argument, under(1), source, openings, depth, here)
        (s"($functionText $argumentText)", functionMisnamed ++ argumentMisnamed)
      case com.yang_bo.gezi.ir.Choice(left, right) =>
        val (leftText, leftMisnamed) =
          drawing(left, under(0), source, openings, depth, here)
        val (rightText, rightMisnamed) =
          drawing(right, under(1), source, openings, depth, here)
        (s"($rightText + $leftText)", rightMisnamed ++ leftMisnamed)
      case com.yang_bo.gezi.ir.Parallel(left, right) =>
        val (leftText, leftMisnamed) =
          drawing(left, under(0), source, openings, depth, here)
        val (rightText, rightMisnamed) =
          drawing(right, under(1), source, openings, depth, here)
        (s"($leftText ∥ $rightText)", leftMisnamed ++ rightMisnamed)
      case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
        val names = CodeDisplay.slotNames(code, map.code, Some(source))
        val written =
          CodeDisplay.writtenBinders(Some(map), holes.size, Some(source))
        val binders = CodeDisplay.binders(holes, 0, names, written)
        val bindersMisnamed = binders.zipWithIndex.flatMap((binder, position) =>
          misnamed(binder, depth + position, here)
        )
        val (body, bodyMisnamed) = displayText(
          CodeDisplay.of(code, holes, written, map.code, Some(source)),
          (index, at) =>
            drawing(fillings(index), under(index), source, openings, at, here),
          depth + holes.size,
          here
        )
        (
          s"(${binders.map(binder => s"λ$binder. ").mkString}$body)",
          bindersMisnamed ++ bodyMisnamed
        )
      case other =>
        throw IllegalStateException(s"a generated start holds $other")

  /** The text of a code's display at the depth, each filling drawn by
    * `fillings` at the depth it stands at, and the binders of its lambdas drawn
    * with another name than the source's.
    */
  private def displayText(
      display: CodeDisplay,
      fillings: (Int, Int) => (String, Vector[String]),
      depth: Int,
      shifts: Set[Int]
  ): (String, Vector[String]) =
    def pair(
        left: CodeDisplay,
        right: CodeDisplay,
        operator: String
    ): (String, Vector[String]) =
      val (leftText, leftMisnamed) = displayText(left, fillings, depth, shifts)
      val (rightText, rightMisnamed) =
        displayText(right, fillings, depth, shifts)
      (s"($leftText$operator$rightText)", leftMisnamed ++ rightMisnamed)
    display match
      case CodeDisplay.Variable(name)            => (name, Vector.empty)
      case CodeDisplay.Filling(index)            => fillings(index, depth)
      case CodeDisplay.Apply(function, argument) =>
        pair(function, argument, " ")
      case CodeDisplay.Choice(left, right)   => pair(right, left, " + ")
      case CodeDisplay.Parallel(left, right) => pair(left, right, " ∥ ")
      case CodeDisplay.Lambda(binders, body) =>
        val (bodyText, bodyMisnamed) =
          displayText(body, fillings, depth + binders.size, shifts)
        val bindersMisnamed = binders.zipWithIndex.flatMap((binder, position) =>
          misnamed(binder, depth + position, shifts)
        )
        (
          s"(${binders.map(binder => s"λ$binder. ").mkString}$bodyText)",
          bindersMisnamed ++ bodyMisnamed
        )
