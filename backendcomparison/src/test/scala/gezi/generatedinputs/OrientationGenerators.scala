package gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import gezi.orientation.Orientation
import gezi.ir.Direction
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.ir.{Apply, Choice, Parallel}

/** Generators of orientations over a generated store (`StoreGenerators`), whose terms are of the stand-in
  * configuration, no Gezi data.
  */
object OrientationGenerators:

  private type C = StandInStorages.type
  private type Term = StandInStorages.Term

  /** Two to five orientations whose matched sides abstract one stored
    * application, parallel or choice:
    * the same abstraction of its first child and a different abstraction of
    * its other children each, so that their seeds begin with equal steps and
    * the graph has nodes they match; their added side an instruction, and the
    * metavariables essential in every other orientation, so that both plain
    * and witness steps occur.
    */
  def orientationsOver(generated: GeneratedStore): Gen[Vector[Orientation[C]]] =
    val instructions = generated.instructions
    val positions = instructions.zipWithIndex.toMap
    val store = generated.store
    val compounds = instructions.map(store.expanded).filter(layer => abstractable(layer) && layer.children.size >= 2)
    for
      layer <-
        if compounds.isEmpty then
          Gen.constant(store.expanded(StandInStorages.parallel(instructions.head, instructions.head)))
        else Gen.element(compounds.head, compounds.tail.toList)
      common <- abstraction(store, positions, layer.children.head, 3)
      count <- Gen.int(Range.linear(2, 5))
      others <- each(layer.children.tail.map(abstraction(store, positions, _, 3)))
        .list(Range.singleton(count))
      added <- Gen.element(instructions.head, instructions.tail.toList)
    yield others.zipWithIndex.toVector.map { (rest, index) =>
      val matched = patternOver(layer, common +: rest)
      Orientation(
        index = index,
        lemma = LemmaIdentifier(index),
        direction = Direction.Forward,
        arity = metavariableCount,
        matched = matched,
        added = Pattern.InstructionReference(added),
        functions = Vector.empty,
        essential =
          if index % 2 == 0 then Vector.range(0, metavariableCount) else Vector.empty,
        shared = Vector.empty
      )
    }

  val metavariableCount = 3

  /** A pattern at most `depth` layers deep that the term of the instruction is
    * an instance of, unless one metavariable stands for two instructions of
    * different terms: the instruction itself, the metavariable the instruction's
    * position in the store gives (so that an instruction met twice is the same metavariable, and
    * later copies are determined), or the instruction's application, parallel or
    * choice over patterns of its children.
    */
  private def abstraction(store: Store[C], positions: Map[Term, Int], instruction: Term, depth: Int): Gen[Pattern[C]] =
    val leaf = Gen.frequency1(
      2 -> Gen.constant(Pattern.Metavariable(positions(instruction) % metavariableCount)),
      1 -> Gen.constant(Pattern.InstructionReference(instruction))
    )
    store.expanded(instruction) match
      case layer if abstractable(layer) && depth > 0 =>
        val below = each(layer.children.map(abstraction(store, positions, _, depth - 1)))
        Gen.frequency1(1 -> leaf, 3 -> below.map(patternOver(layer, _)))
      case _ => leaf

  /** A layer a pattern may abstract: an application, a parallel or a choice. */
  private def abstractable(layer: Layer[Term]): Boolean = layer match
    case Apply(_, _) | Parallel(_, _) | Choice(_, _) => true
    case _                                                             => false

  /** The pattern of the layer's shape over patterns of its children, in
    * child order.
    */
  private def patternOver(layer: Layer[Term], children: Vector[Pattern[C]]): Pattern[C] = layer match
    case Apply(_, _)     => Pattern.Apply(children(0), children(1))
    case Parallel(_, _)  => Pattern.Parallel(children(0), children(1))
    case _                     => Pattern.Choice(children(0), children(1))

  /** One value of each generator, in order. */
  private def each(generators: Vector[Gen[Pattern[C]]]): Gen[Vector[Pattern[C]]] =
    generators.foldLeft(Gen.constant(Vector.empty[Pattern[C]]))((gathered, generator) =>
      for
        earlier <- gathered
        next <- generator
      yield earlier :+ next
    )
