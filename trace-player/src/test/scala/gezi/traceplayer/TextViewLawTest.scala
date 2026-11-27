package gezi.traceplayer

import hedgehog.Result
import gezi.frontend.ReadableText
import gezi.generatedinputs.GeneratedProperties
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText

/** The law of the text view's highlight on generated traces read and replayed
  * as a page plays them (`TraceReading.played`): every step's term printed with
  * its carried map, the node the step put there (`Played.rewritten`) is
  * highlighted by a mark the printed text holds, at the place of that node or
  * of a node above it, and the printed structure of every step pairs its
  * openings and closings (`TextView.trees`).
  *
  * Purpose: catch a step whose rewritten node the text view highlights nowhere,
  * or highlights at a node beside or below it, and pieces the view cannot nest.
  */
class TextViewLawTest extends GeneratedProperties:

  property(
    "each step's rewritten node is highlighted at its place or above it"
  ) {
    for (start, trace) <- TermSequences.trace.forAllWithLog((start, trace) =>
        s"${TraceStart.written(start, None)}\n${TraceText.written(trace)}"
      )
    yield TraceReading.played(
      TraceStart.written(start, None),
      TraceText.written(trace)
    ) match
      case Left(unreadable) =>
        Result.failure.log(s"the texts do not read: ${unreadable.error}")
      case Right(played) =>
        Result.all(
          (0 until played.size).toList.map(step =>
            val printed =
              ReadableText.printed(played.term(step), played.map(step))
            val marked = printed.pieces.collect {
              case ReadableText.Piece.At(place, _) => place.key
            }.toSet
            val nested = TextView.trees(printed.pieces).nonEmpty
            played.rewritten(step) match
              case None =>
                Result.assert(nested).log(s"step $step: no structure")
              case Some(path) =>
                val above = path.inits.map(printed.place(_).key).toSet
                TextView.highlighted(printed, path) match
                  case Some(key) =>
                    Result
                      .assert(
                        nested && marked.contains(key) && above.contains(key)
                      )
                      .log(s"step $step: $key for the path $path")
                  case None =>
                    Result.failure.log(
                      s"step $step: nothing highlighted for the path $path in ${printed.text}"
                    )
          )
        )
  }
