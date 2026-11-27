package com.yang_bo.gezi.frontend

import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.locations.BinderOrigin
import com.yang_bo.gezi.locations.Location
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.locations.Span

/** The law of the located contraction of the printer's bindings
  * (`Defunctionalization.locatedBindingsContracted`) on the instructions of
  * `SharingInstructions`, printed by `ReadableText.printedNameless` and read
  * with their spans: the body's instruction is the printed instruction and the
  * one the unlocated contraction gives (`bindingsContracted`); every location
  * of a binding's map lies in the text of that binding's value, and the map's
  * root holds the value's span; and every location of the body's map lies in
  * the text of the body. Its purpose is to catch a located contraction whose
  * instruction differs from the program's or from the exchange format's, and a
  * map that puts a place in another part of the text than the one it was read
  * from, such as a value's places at the occurrences of its name, or the spans
  * of a binding shifted onto the next.
  */
class LocatedBindingsContractionLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private val uri: java.net.URI =
    java.net.URI("file:///located-bindings.lambdalattice")

  /** Every span a map's locations and binder origins hold, or the locations of
    * another kind.
    */
  private def spans(map: SourceMap): Vector[Either[Location, Span]] =
    val own = map.locations.toVector ++ map.binders.flatten.flatMap {
      case BinderOrigin.Written(_, location)                => Vector(location)
      case BinderOrigin.LiteralBit(_, _, location)          => Vector(location)
      case BinderOrigin.Enclosing(_) | BinderOrigin.Made(_) => Vector.empty
    }
    own.map {
      case Location.Source(`uri`, span) => Right(span)
      case other                        => Left(other)
    } ++ map.code.toVector.flatMap(spans) ++ map.children.flatMap(spans)

  /** The problems of a map that should locate only within `within`. */
  private def outside(
      name: String,
      map: SourceMap,
      within: Span
  ): Vector[String] =
    spans(map).collect {
      case Left(location) => s"$name holds $location, no span of the text"
      case Right(span) if !within.contains(span) =>
        s"$name holds $span, outside $within"
    }

  property(
    "the body is the printed instruction, and each map locates within its part of the text",
    _.copy(testLimit = 30)
  ) {
    SharingInstructions.instructions
      .forAllWithLog(instruction =>
        ReadableText.printedNameless(instruction).text
      )
      .map(instruction =>
        val printed = ReadableText.printedNameless(instruction)
        val read = Lambdalattice.located(printed.text, FreeNames.Rejected)
        val located =
          Defunctionalization.locatedBindingsContracted[NoFacts.type](
            read.term,
            read.spans,
            uri,
            printed.bindings
          )
        located match
          case Left(reason)      => Result.failure.log(reason)
          case Right(contracted) =>
            val (bodySpans, bindingProblems) =
              contracted.bindings.zipWithIndex.foldLeft(
                (read.spans, Vector.empty[String])
              ) { case ((spansHere, problems), (binding, index)) =>
                val valueSpan = spansHere.child(0).child(0).child(1).span
                val rootProblems =
                  if binding.map.locations
                      .contains(Location.Source(uri, valueSpan))
                  then Vector.empty
                  else
                    Vector(
                      s"binding $index's root holds ${binding.map.locations}, not $valueSpan"
                    )
                (
                  spansHere.child(1).child(0),
                  problems ++ rootProblems ++ outside(
                    s"binding $index",
                    binding.map,
                    valueSpan
                  )
                )
              }
            val problems =
              (if Configured.same(contracted.body, instruction) then
                 Vector.empty
               else Vector("the body is not the printed instruction")) ++
                (if Defunctionalization
                     .bindingsContracted[NoFacts.type](
                       read.term,
                       printed.bindings,
                       enclosingBinders = 0
                     )
                     .exists(Configured.same(_, instruction))
                 then Vector.empty
                 else
                   Vector(
                     "the unlocated contraction gives another instruction"
                   )) ++
                (if contracted.bindings.size == printed.bindings then
                   Vector.empty
                 else
                   Vector(
                     s"${contracted.bindings.size} bindings for the printer's ${printed.bindings}"
                   )) ++
                bindingProblems ++ outside(
                  "the body",
                  contracted.map,
                  bodySpans.span
                )
            Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }
