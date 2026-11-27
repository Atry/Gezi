package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Store
import gezi.ir.{Apply, Slot, Thunk}
import gezi.saturation.BodyOpening
import gezi.saturation.OpeningCriterion

/** The law that the body opening reads a let-bound value of a closure's code:
  * the closure `λx. (λf. f x … x) h`, its let unreduced in the code with h at a
  * filling, as the front end spells a closure whose let binds a closed value,
  * is opened exactly when h is a head some lemma's left side applies, for a
  * generated number of arguments and a generated head arity.
  *
  * Purpose: catch an opening criterion that reads only the head of the code's
  * own applications and so misses a head bound by a let, the defect that cost
  * `contest-entries-wren`'s calls_10000_hot/direct point its one opening
  * (`BodyOpening.calls`' Scaladoc has the measurement).
  */
class LetBoundHeadOpeningLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private val head = NoFacts.opaque("let-bound head")

  /** `λx. (λf. f x … x) h`, f applied to x `arguments` times, in the front
    * end's spelling: x the hole at slot 0, h the filling at slot 1, and the
    * inner thunk's hole f at its slot 0 with x passed on at its slot 1.
    */
  private def closure(arguments: Int): Configured[NoFacts.type] =
    val applied = (1 to arguments).foldLeft(Code(Slot(0)))((function, _) =>
      Code(Apply(function, Code(Slot(1))))
    )
    val inner = Code(
      Thunk(applied, Vector(Hole.Bound(0)), Vector(Code(Slot(0))))
    )
    NoFacts.thunkOrInstance(
      Code(Apply(inner, Code(Slot(1)))),
      Vector(Hole.Bound(0)),
      Vector(head)
    )

  property(
    "a closure whose let binds a head is opened, and one whose let binds no head is not"
  ) {
    for
      arguments <- Gen.int(Range.linear(1, 3)).forAll
      arity <- Gen.int(Range.linear(1, 3)).forAll
      isHead <- Gen.boolean.forAll
    yield
      val (graph, _) = EGraph
        .empty(
          Store(
            noinline = Set(head),
            gezi.ir.TermConstruction(gezi.ir.NoFacts)
          ),
          Map.empty,
          explained = false
        )
        .instructionAdded(closure(arguments))
      val heads = if isHead then Map(head -> arity)
      else Map.empty[Configured[NoFacts.type], Int]
      val scope =
        BodyOpening.classesUnder(graph, graph.liveNodes.map(_.root), Set.empty)
      val (_, openings) = BodyOpening.opened(
        graph,
        Vector.empty,
        8,
        scope,
        heads,
        Set.empty,
        OpeningCriterion.CallsAHead[gezi.ir.NoFacts.type]()
      )
      Result
        .diff(openings.size, if isHead then 1 else 0)(_ == _)
        .log(s"$arguments arguments, arity $arity, head: $isHead")
  }
