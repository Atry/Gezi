package com.yang_bo.gezi.saturation

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Apply
import com.yang_bo.gezi.ir.Choice
import com.yang_bo.gezi.generatedinputs.StandInStorage
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.ir.Interned
import com.yang_bo.gezi.ir.IrLayer
import com.yang_bo.gezi.ir.NativeStorage
import com.yang_bo.gezi.ir.Parallel
import com.yang_bo.gezi.ir.Store

/** A native storage of the tests, kept as a leaf, whose view throws when it is
  * read. Equal to itself only.
  */
private final class PoisonedLeafStorage(criterionTerm: StandInStorages.Term)
    extends StandInStorage:
  def standInCriterion: StandInStorages.Term = criterionTerm
  val closed: Boolean = true
  val suspensionFree: Boolean = true
  val handedOverWhole: Boolean = false
  protected val termChildren: IArray[AnyRef] = IArray(
    criterionTerm.representation
  )
  protected val constructorIndex: Int = 0
  val leafInEGraph: Boolean = true
  val constantSize: Boolean = true

  /** False: a stand-in of the tests forms no group. */
  def precedes(other: com.yang_bo.gezi.ir.NativeStorage): Boolean = false

  /** A stand-in is one object: equal to itself only, in the pool as outside it.
    */
  def contentHash: Int = System.identityHashCode(this)
  def sameContent(other: NativeStorage): Boolean = this eq other

/** The law of a closure's body written back over storage leaves: a generated
  * body (applications, parallels and choices over noinline names, an
  * eigenvariable and poisoned storages, whose views throw) is abstracted over
  * the eigenvariable as a body is written back (`HigherOrderMatching.
  * abstractedInstruction`, which reads the body through `instructionView` and
  * `holds`), and added to a graph with the eigenvariable at its leaf
  * (`termAdded`). Derived before the run from the walks that stop at a leaf
  * (`heldAsLeaf`): neither reads a storage's view, and every storage of the
  * body is, as the very object, a subterm of the abstraction and a leaf of the
  * graph. Its purpose is to catch a write-back that reads a storage leaf's
  * view, the path of a closure whose filling holds a storage.
  */
class StorageLeafAbstractionLawTest extends GeneratedProperties:

  private type Term = StandInStorages.Term

  private val criterion = StandInStorages.opaque("criterion")
  private val names =
    Vector(StandInStorages.opaque("first"), StandInStorages.opaque("second"))
  private val eigenvariable = StandInStorages.opaque("eigenvariable")

  private def body(atoms: Vector[Term], depth: Int): Gen[Term] =
    if depth == 0 then Gen.element(atoms.head, atoms.tail.toList)
    else
      Gen.frequency1(
        2 -> Gen.element(atoms.head, atoms.tail.toList),
        3 -> (for
          function <- body(atoms, depth - 1); argument <- body(atoms, depth - 1)
        yield StandInStorages.application(function, argument)),
        1 -> (for
          left <- body(atoms, depth - 1); right <- body(atoms, depth - 1)
        yield StandInStorages.parallel(left, right)),
        1 -> (for
          left <- body(atoms, depth - 1); right <- body(atoms, depth - 1)
        yield StandInStorages.choice(left, right))
      )

  /** Every subterm, each once, a storage's view not read. */
  private def subterms(root: Term): Set[Term] =
    @scala.annotation.tailrec
    def walked(pending: List[Term], seen: Set[Term]): Set[Term] = pending match
      case Nil                        => seen
      case term :: rest if seen(term) => walked(rest, seen)
      case term :: rest if NativeStorage.stored(term.representation) =>
        walked(rest, seen + term)
      case term :: rest =>
        val children: List[Term] =
          if term.opaque then Nil else term.layer.children.toList
        walked(children ::: rest, seen + term)
    walked(List(root), Set.empty)

  property(
    "a body over storage leaves is abstracted and added with no storage's view read"
  ) {
    for
      storageCount <- Gen.int(Range.linear(1, 3)).forAll
      storages = (0 until storageCount).toVector.map(_ =>
        com.yang_bo.gezi.generatedinputs.StandInStorages.stored(
          PoisonedLeafStorage(criterion)
        )
      )
      generated <- body(names ++ storages :+ eigenvariable, 4).forAll
    yield
      val written = StandInStorages.application(
        StandInStorages.application(eigenvariable, generated),
        storages.head
      )
      val abstracted = HigherOrderMatching.abstractedInstruction(
        written,
        Vector(eigenvariable),
        com.yang_bo.gezi.ir.TermConstruction(StandInStorages)
      )
      val store = Store(
        (names :+ eigenvariable :+ criterion).toSet,
        com.yang_bo.gezi.ir.TermConstruction(StandInStorages)
      )
      val (empty, eigenvariableNode) = EGraph
        .empty(store, Map.empty, explained = false)
        .instructionAdded(eigenvariable)
      val (graph, _) = HigherOrderMatching.termAdded(
        empty,
        ClosedTerm.InstructionTerm(written),
        Map(eigenvariable -> eigenvariableNode)
      )
      val bodyStorages = subterms(written).filter(term =>
        NativeStorage.stored(term.representation)
      )
      val inAbstraction = subterms(abstracted)
      Result
        .assert(bodyStorages.forall(inAbstraction.contains))
        .log(s"a storage lost from the abstraction")
        .and(
          Result
            .assert(
              bodyStorages
                .forall(storage => graph.instructionNode(storage).isDefined)
            )
            .log("a storage with no leaf node")
        )
  }
