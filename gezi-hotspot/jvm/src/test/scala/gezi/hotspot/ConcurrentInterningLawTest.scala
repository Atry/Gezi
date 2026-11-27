package gezi.hotspot

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.saturation.StopSignal

/** The law of concurrent registration: tasks run in parallel by the fork and
  * join primitive (`Forks.joinedAll`), each interning its own generated list
  * of terms, the lists overlapping, give one object for each term, whichever
  * task interned it first, and each object's layer is the layer it was
  * interned with. Its purpose is to catch an interner that, under contention,
  * hands two threads two objects for one layer (a race between the look-up and
  * the insertion), or files an object under another layer, so that a handle
  * would no longer identify a term.
  *
  * The terms are written as descriptions, built into instructions inside the
  * tasks: opaque leaves of a few names, and applications, parallels and
  * choices of terms built before. A small set of leaves makes the lists
  * share many terms, so that several tasks intern the same layer at once.
  */
class ConcurrentInterningLawTest extends GeneratedProperties:

  private enum Description:
    case Leaf(name: String)
    case Applied(function: Description, argument: Description)
    case Parallel(left: Description, right: Description)
    case Choice(left: Description, right: Description)

  private def built(description: Description): Configured[NoFacts.type] = description match
    case Description.Leaf(name)                   => NoFacts.opaque(s"concurrent_interning_$name")
    case Description.Applied(function, argument)  => NoFacts.application(built(function), built(argument))
    case Description.Parallel(left, right)        => NoFacts.parallel(built(left), built(right))
    case Description.Choice(left, right)          => NoFacts.choice(built(left), built(right))

  private def descriptions(depth: Int): Gen[Description] =
    val leaf = Gen.elementUnsafe(List("a", "b", "c")).map(Description.Leaf(_))
    if depth == 0 then leaf
    else
      Gen.frequency1(
        1 -> leaf,
        1 -> descriptions(depth - 1).flatMap(left => descriptions(depth - 1).map(right => Description.Applied(left, right))),
        1 -> descriptions(depth - 1).flatMap(left => descriptions(depth - 1).map(right => Description.Parallel(left, right))),
        1 -> descriptions(depth - 1).flatMap(left => descriptions(depth - 1).map(right => Description.Choice(left, right)))
      )

  private val budget = Budget(1000, countedUnits = false, NeverStop)

  property("tasks interning overlapping terms in parallel get one object for each term, filed under its layer") {
    for
      shared <- descriptions(3).list(Range.linear(1, 8)).forAll
      perTask <- descriptions(3).list(Range.linear(0, 4)).list(Range.linear(2, 8)).forAll
    yield
      // Every task interns the shared terms and its own, so the same layers are interned by several tasks at once.
      val lists = perTask.toVector.map(own => (shared ++ own).toVector)
      val tasks = lists.map(list => ForkedTask[Vector[Configured[NoFacts.type]]](budget, (_, _) => TaskOutcome(list.map(built), Spent(0, Map.empty))))
      val joined = Forks.joinedAll(tasks).outcomes.map(_.result)
      val byDescription = lists.zip(joined).flatMap((list, instructions) => list.zip(instructions))
      val split = byDescription.groupBy(_._1).toVector.collect {
        case (description, found) if found.map(_._2).distinctBy(term => System.identityHashCode(term.representation)).size > 1 => description
      }
      val misfiled = byDescription.collect {
        case (description, instruction) if !Configured.same(built(description), instruction)(using NoFacts) => description
      }
      Result.all(
        List(
          Result.diff(split, Vector.empty)(_ == _).log("terms interned as more than one object"),
          Result.diff(misfiled, Vector.empty)(_ == _).log("objects that are not the term interned again")
        )
      )
  }

  /** A signal that never asks to stop. */
  private object NeverStop extends StopSignal:
    def stopRequested: Boolean = false
