package gezi.backendcomparison

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.ematching.closures.ClosureCompilation
import gezi.ematching.indexing.Indexing
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StandInStorage
import gezi.generatedinputs.StandInStorages
import gezi.ir.Apply
import gezi.ir.BuiltInRule
import gezi.ir.Direction
import gezi.ir.Interned
import gezi.ir.IrLayer
import gezi.ir.LemmaIdentifier
import gezi.ir.NativeStorage
import gezi.ir.Parallel
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.orientation.Orientation
import gezi.orientation.Orientations
import gezi.saturation.Saturation
import gezi.saturation.StopSignal

/** A native storage of the tests, kept as a leaf, whose view throws when it is
  * read, of constant size unless said otherwise. Equal to itself only.
  */
private final class PoisonedLeafStorage(
    criterionTerm: StandInStorages.Term,
    val constantSize: Boolean = true
) extends StandInStorage:
  def standInCriterion: StandInStorages.Term = criterionTerm
  val closed: Boolean = true
  val suspensionFree: Boolean = true
  val handedOverWhole: Boolean = false
  protected val termChildren: IArray[AnyRef] = IArray(
    criterionTerm.representation
  )
  protected val constructorIndex: Int = 0
  val leafInEGraph: Boolean = true

  /** False: a stand-in of the tests forms no group. */
  def precedes(other: gezi.ir.NativeStorage): Boolean = false

  /** A stand-in is one object: equal to itself only, in the pool as outside it.
    */
  def contentHash: Int = System.identityHashCode(this)
  def sameContent(other: NativeStorage): Boolean = this eq other

/** The law that a lemma matching `?x ∥ ?T` matches a storage the e-graph keeps
  * as a leaf, through its pattern view, without its view: generated storages
  * (poisoned: their views throw), each with a criterion among generated
  * noinline names and given to a generated noinline function, are saturated
  * under the one orientation `?x ∥ ?T → mark ?x` (mark a noinline name).
  * Derived before the run from the pattern view (the leaf's class holds
  * `Parallel(leaf, T)`, which the orientation's matched side matches with ?x
  * the leaf's own class): the run reaches its fixed point without reading a
  * view, and every storage's class holds `mark` applied to it. Its purpose is
  * to catch a pattern view that `?x ∥ ?T` cannot match, which would leave every
  * typed call, filter idempotence and reverse lemma blind to a storage, and a
  * matching that reads a storage leaf's view.
  */
class PatternViewMatchingLawTest extends GeneratedProperties:

  private type C = StandInStorages.type

  private given StandInStorages.type = StandInStorages

  private val mark = StandInStorages.opaque("mark")

  private val orientation: Orientation[C] = Orientation(
    index = 0,
    lemma = LemmaIdentifier(0),
    direction = Direction.Forward,
    arity = 2,
    matched =
      Pattern.Parallel(Pattern.Metavariable[C](0), Pattern.Metavariable[C](1)),
    added = Pattern
      .Apply(Pattern.InstructionReference(mark), Pattern.Metavariable[C](0)),
    functions = Vector.empty,
    essential = Vector(0, 1),
    shared = Vector.empty
  )

  stoppableProperty(
    "a storage leaf's pattern view lets ?x ∥ ?T match the storage"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      storageCount <- Gen.int(Range.linear(1, 4)).forAll
      criterionCount <- Gen.int(Range.linear(1, 3)).forAll
      picks <- Gen
        .int(Range.linear(0, Int.MaxValue))
        .list(Range.singleton(2 * storageCount))
        .forAll
    yield
      val criteria = (0 until criterionCount).toVector.map(position =>
        StandInStorages.opaque(s"criterion $position")
      )
      val functions = (0 until 2).toVector.map(position =>
        StandInStorages.opaque(s"function $position")
      )
      val storages = (0 until storageCount).toVector.map(position =>
        StandInStorages.stored(
          PoisonedLeafStorage(criteria(picks(2 * position) % criterionCount))
        )
      )
      val inputs = storages.zipWithIndex.map((storage, position) =>
        StandInStorages.application(
          functions(picks(2 * position + 1) % 2),
          storage
        )
      )
      val store = Store(
        (criteria ++ functions :+ mark).toSet,
        gezi.ir.TermConstruction(StandInStorages)
      )
      val program = Indexing.program(
        Vector(orientation),
        Indexing.codesMet(Vector(orientation), inputs)
      )
      val run = Saturation.run(
        program,
        ClosureCompilation.compiled(program),
        BuiltInRule.beforeOptIn,
        store,
        Orientations.headArityBounds(Vector(orientation)),
        Vector.empty,
        inputs,
        budget = 1000,
        explained = false,
        stop
      )
      val graph = run.graph
      val markNode = graph.instructionNode(mark)
      val marked = storages.map(storage =>
        val leaf = graph
          .instructionNode(storage)
          .getOrElse(throw IllegalStateException(s"no node of $storage"))
        markNode
          .flatMap(node => graph.layerNode(Apply(node, graph.root(leaf))))
          .exists(found => graph.root(found) == graph.root(leaf))
      )
      Result
        .assert(run.end.isInstanceOf[gezi.saturation.End.FixedPoint])
        .log(s"${run.end}")
        .and(Result.assert(marked.forall(identity)).log(s"marked: $marked"))
  }
