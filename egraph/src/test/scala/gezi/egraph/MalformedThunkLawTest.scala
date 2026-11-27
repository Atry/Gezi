package gezi.egraph

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.generatedinputs.StandInStorages
import gezi.ir.Store
import gezi.ir.{Apply, Slot, Thunk}

/** The law that the e-graph rejects a thunk that is not well-formed, one whose
  * fillings are not exactly its code's slots that no hole binds
  * (`Code.fillingCount`, the input contract of `EGraph.layerMade`), on
  * generated thunks of three codes, 1 or 2 holes and 0 to 2 fillings that do
  * not fit.
  *
  * Purpose: catch a graph that takes such a thunk in, where its respelling
  * would read a slot no filling fills, or where two thunks would be one node
  * only because one carries a filling no slot reads.
  */
class MalformedThunkLawTest extends GeneratedProperties:

  private val leaves: Vector[StandInStorages.Term] =
    Vector(0, 1).map(position => StandInStorages.opaque(s"leaf $position"))

  property(
    "the graph rejects a thunk whose fillings are not its code's slots no hole binds"
  ) {
    val hole = Gen.element1[Hole](Hole.Bound(0), Hole.Bound(1), Hole.Ignored)
    for
      code <- Gen
        .element1(
          Code(Slot(0)),
          Code(Slot(1)),
          Code(Apply(Code(Slot(0)), Code(Slot(1))))
        )
        .forAll
      holes <- hole.list(Range.linear(1, 2)).map(_.toVector).forAll
      fillingCount <- Gen
        .int(Range.linear(0, 2))
        .filter(count => !Code.fillingCount(code, holes).contains(count))
        .forAll
    yield
      val (graph, leafNodes) = leaves.foldLeft(
        (
          EGraph.empty(
            Store(
              noinline = leaves.toSet,
              gezi.ir.TermConstruction(StandInStorages)
            ),
            Map.empty,
            explained = false
          ),
          Vector.empty[Int]
        )
      ) { case ((current, nodes), leaf) =>
        val (next, node) = current.instructionAdded(leaf)
        (next, nodes :+ node)
      }
      val thunk = Thunk(
        code,
        holes,
        Vector.tabulate(fillingCount)(position =>
          leafNodes(position % leafNodes.size)
        )
      )
      val rejected = scala.util.Try(graph.layerAdded(thunk)).failed.toOption
      Result
        .assert(rejected.exists(_.isInstanceOf[IllegalArgumentException]))
        .log(s"$thunk: ${rejected.fold("taken in")(_.toString)}")
  }
