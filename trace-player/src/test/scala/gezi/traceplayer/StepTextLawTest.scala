package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.ReadableText
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.locations.SourceMap
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText

private given stepTextLawTestNoFacts: NoFacts.type = NoFacts

/** The law of a step's text on generated traces read and replayed as a page
  * plays them, from a start written with a generated subset of its subterms
  * named as library terms (`TraceStart.written` with `known`), every other name
  * holding `$` as the library's synthetic names do (`$library$known_3`), each
  * step printed as the views print it (`BoxFolding.step`) with a generated
  * subset of its shared instructions inlined: the text, read by the front end
  * with free names rejected and its bindings at the root contracted
  * (`ReadableText.contracted`, as many as the printer wrote), is the step's
  * term; and the library names the player reads from the start are exactly the
  * given names the start's text binds.
  *
  * Purpose: catch a step's text that writes a library term by a name it binds
  * nowhere, a text that reads back as another term than the step's, a name the
  * printer escapes again although it is a name already (`$` written as
  * `$u0024`), and a start whose library names the player does not read back,
  * which would leave the first law with no library name to check.
  */
class StepTextLawTest extends GeneratedProperties:

  /** Every subterm of the term that is no opaque instruction, each once, in
    * preorder.
    */
  private def subterms(
      instruction: Configured[NoFacts.type]
  ): Vector[Configured[NoFacts.type]] =
    if instruction.opaque then Vector.empty
    else (instruction +: instruction.layer.children.flatMap(subterms)).distinct

  /** The text read back and its first `bindings` bindings at the root
    * contracted, each `(λt. t V) λm. BODY` to BODY with V in place of m.
    */
  private def readBack(
      text: String,
      bindings: Int
  ): Option[Configured[NoFacts.type]] =
    (1 to bindings)
      .foldLeft(
        Option[(Configured[NoFacts.type], SourceMap)](
          (
            Defunctionalization.thunkInstruction(Lambdalattice.term(text))(using
              gezi.ir.NoFacts
            ),
            SourceMap.unlocated
          )
        )
      )((read, _) =>
        read.flatMap((instruction, map) =>
          ReadableText.contracted(instruction, map)
        )
      )
      .map(_._1)

  property(
    "every step's text, library terms bound by their names, reads back as the step's term"
  ) {
    for
      (start, trace) <- Gen
        .choice1(TermSequences.trace, TermSequences.sharingTrace)
        .forAllWithLog((start, trace) =>
          s"${TraceStart.written(start, None)}\n${TraceText.written(trace)}"
        )
      selection <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
    yield
      val known = subterms(start).zipWithIndex.collect {
        case (subterm, index) if ((selection >> (index % 31)) & 1L) == 1L =>
          subterm -> (if index % 2 == 0 then s"known_$index"
                      else s"$$library$$known_$index")
      }.toMap
      TraceReading.played(
        TraceStart.written(start, None, known),
        TraceText.written(trace)
      ) match
        case Left(unreadable) =>
          Result.failure.log(s"the texts do not read: ${unreadable.error}")
        case Right(played) =>
          val startBound = ReadableText
            .printedNameless(start, ReadableText.KnownNames.Bound(known))
            .sharedValues
            .collect {
              case value if known.get(value.instruction).contains(value.name) =>
                value.instruction -> value.name
            }
            .toMap
          Result
            .all(
              Result
                .diff(played.names, startBound)(_ == _)
                .log("the library names read from the start") ::
                (0 until played.size).toList.map(step =>
                  val term = played.term(step)
                  val (plain, _) = BoxFolding
                    .step(term, played.map(step), played.names, Set.empty)
                  val keys = plain.sharedValues.zipWithIndex
                    .collect {
                      case (value, index)
                          if ((selection >> (31 + index % 31)) & 1L) == 1L =>
                        SharedKey.of(value.name)
                    }
                    .flatten
                    .toSet
                  val (printed, _) =
                    BoxFolding.step(term, played.map(step), played.names, keys)
                  Result
                    .diff(readBack(printed.text, printed.bindings), Some(term))(
                      (read, expected) => read.zip(expected).exists(_ eq _)
                    )
                    .log(
                      s"step $step, ${printed.bindings} bindings: ${printed.text}"
                    )
                )
            )
            .log(s"the library names: ${played.names.values.toVector.sorted}")
  }
