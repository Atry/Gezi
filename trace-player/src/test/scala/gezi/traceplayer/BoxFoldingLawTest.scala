package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.ReadableText
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText

/** The laws of the boxes view's folding (`BoxFolding`)
  * on generated traces
  * read and replayed as a page plays them, each step folded with a
  * generated subset of its shared instructions inlined: the boxes, each
  * reference replaced by its binding's boxes, are the step's term's tree;
  * no place is drawn twice; the place of every path of the term is a place
  * drawn; no inlined shared instruction is bound; and every box the folding
  * offers to bind again is an inlined one.
  *
  * Purpose: catch a folding that draws a term other than the step's (a
  * reference to the wrong binding, a subterm lost under a reference), two
  * boxes under one key (the view would update the wrong one), a path whose
  * box the highlight and the flights cannot find, and an inlined
  * instruction still bound.
  */
class BoxFoldingLawTest extends GeneratedProperties:

  /** Whether the box, its references replaced by the boxes of their
    * bindings, is the instruction's tree.
    */
  private def drawsTree(box: BoxFolding.Box, instruction: Instruction, bound: Map[String, BoxFolding.Box]): Boolean =
    box.shown match
      case BoxFolding.Shown.Layer(drawn, _, _) =>
        val children = if instruction.opaque then Vector.empty else instruction.layer.children
        drawn == instruction && box.under.size == children.size &&
        box.under.zip(children).forall((under, child) => drawsTree(under, child, bound))
      case BoxFolding.Shown.Reference(name, _) => bound.get(name).exists(drawsTree(_, instruction, bound))

  /** Every path of the term, by the indices of `Layer.children`. */
  private def paths(instruction: Instruction): Vector[Vector[Int]] =
    val children = if instruction.opaque then Vector.empty else instruction.layer.children
    Vector(Vector.empty) ++ children.zipWithIndex.flatMap((child, index) => paths(child).map(index +: _))

  /** Every box of the tree. */
  private def boxes(box: BoxFolding.Box): Vector[BoxFolding.Box] = box +: box.under.flatMap(boxes)

  property("the folded boxes draw each step's term once at each place, inlined instructions unbound") {
    for
      (start, trace) <- Gen.choice1(TermSequences.trace, TermSequences.sharingTrace)
        .forAllWithLog((start, trace) => s"${TraceStart.written(start, None)}\n${TraceText.written(trace)}")
        .cover(30, "the start binds a shared instruction", (start, _) => ReadableText.printedNameless(start).sharedValues.nonEmpty)
      selection <- Gen.int(Range.linear(0, Int.MaxValue)).forAll
    yield TraceReading.played(TraceStart.written(start, None), TraceText.written(trace)) match
      case Left(unreadable) => Result.failure.log(s"the texts do not read: ${unreadable.error}")
      case Right(played) =>
        Result.all(
          (0 until played.size).toList.map(step =>
            val term = played.term(step)
            val (plain, _) = BoxFolding.step(term, played.map(step), played.names, Set.empty)
            val keys = plain.sharedValues.zipWithIndex.collect {
              case (value, index) if ((selection >> (index % 31)) & 1) == 1 => SharedKey.of(value.name)
            }.flatten.toSet
            val (printed, folding) = BoxFolding.step(term, played.map(step), played.names, keys)
            val (bindings, body) = folding.drawn
            val bound = bindings.toMap
            // A reference draws no place of its own: it stands for its binding's.
            val drawnPlaces = (bindings.map(_._2) :+ body).flatMap(boxes).flatMap(box =>
              box.shown match
                case BoxFolding.Shown.Reference(_, _) => Vector.empty
                case _                                => Vector(box.place)
            )
            val inlinedKeys = folding.inlined.values.toSet
            Result
              .all(
                List(
                  Result.assert(drawsTree(body, term, bound)).log("the body is not the term's tree"),
                  Result.assert(drawnPlaces.distinct.size == drawnPlaces.size).log(s"a place drawn twice: $drawnPlaces"),
                  Result.assert(paths(term).forall(path => drawnPlaces.contains(folding.place(path)))).log("a path's place not drawn"),
                  Result.assert(printed.sharedValues.forall(value => SharedKey.of(value.name).forall(!keys.contains(_))))
                    .log(s"an inlined instruction bound: $keys in ${printed.text}"),
                  Result.assert(folding.extractions.values.forall(inlinedKeys.contains)).log("a button for no inlined instruction")
                )
              )
              .log(s"step $step")
          )
        )
  }
