package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.rewritetrace.TraceStart

/** The law of a start's text on generated starts that share their parts
  * (`TraceStart`): a generated closed term under a tower of diamonds
  * `λf. f d d`, each level writing the level below twice, so that the printer
  * binds the levels at the start's root, each binding's value using the
  * bindings before it. The text, written nameless and written from the start's
  * source, reads back as the start.
  *
  * Purpose: catch a reader that contracts the printer's bindings in the wrong
  * order or into the wrong places when a later binding's value uses an earlier
  * one, and a count of bindings that differs from the printer's.
  */
class TraceStartLawTest extends GeneratedProperties:

  /** A generated closed term under a tower of diamonds of a generated height,
    * drawn before any abstraction is built (the tower's bodies draw nothing).
    */
  private val towers: Gen[Term] =
    for
      leaf <- HoasGenerators.closedTerm
      height <- Gen.int(Range.linear(0, 5))
    yield (1 to height).foldLeft(leaf)((below, _) =>
      Term.Abstraction(function => function(below)(below))
    )

  property(
    "a start with shared parts, written nameless and from its source, reads back as the start"
  ) {
    for tower <- towers.forAllWithLog(LambdalatticeText.text)
    yield
      val start = Defunctionalization.thunkInstruction(
        tower.deBruijnTerm(Map.empty)
      )(using gezi.ir.NoFacts)
      val source = LambdalatticeText.text(tower)
      Result.all(
        List(
          Result
            .diff(
              TraceStart
                .readLocated(
                  TraceStart.written(start, None),
                  TraceReading.startUri
                )
                .start,
              start
            )(_ eq _)
            .log("written nameless"),
          Result
            .diff(
              TraceStart
                .readLocated(
                  TraceStart.written(start, Some(source)),
                  TraceReading.startUri
                )
                .start,
              start
            )(_ eq _)
            .log("written from its source")
        )
      )
  }
