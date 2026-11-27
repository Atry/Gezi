package com.yang_bo.gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.Justification
import com.yang_bo.gezi.extraction.CountedExtraction
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Apply
import com.yang_bo.gezi.ir.Choice
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.generatedinputs.StandInStorage
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.ir.Interned
import com.yang_bo.gezi.ir.IrLayer
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.NativeStorage
import com.yang_bo.gezi.ir.Parallel
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.CombinatorProperty
import com.yang_bo.gezi.standardlibrary.Property
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex

/** A native storage of the tests kept as a leaf of constant size, holding its
  * criterion alone as a constant storage does, whose view throws when it is
  * read: neither extraction may read a leaf's view. Equal to itself only.
  */
final class ExtractedStorage(
    value: StandInStorages.Term,
    criterionTerm: StandInStorages.Term
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
  val constantSize: Boolean = true

  /** False: a stand-in of the tests forms no group. */
  def precedes(other: NativeStorage): Boolean = false

  /** A stand-in is one object: equal to itself only, in the pool as outside it.
    */
  def contentHash: Int = System.identityHashCode(this)
  def sameContent(other: NativeStorage): Boolean = this eq other

/** The law that the native route's extraction, `specialization_attraction` then
  * `compression`, spells a class that holds a storage side S and a written
  * member q by S, read by an application `g K`. S is built by construction of
  * each kind, every iteration, beside a typed member p of each shape (`f (a ∥
  * A) ∥ B`, `C (a ∥ A) ∥ T`, `x ∥ T`), so that the reading rule S reaches the
  * class through is the one that decides: a storage leaf ℓ itself; a tagged
  * storage `t ℓ`, t a name of property `tag_next`; and a choice of storages
  * `ℓ1 + ℓ2`. A contract filled by a storage, `c ℓ` with `c = λy. h y ∥ R`, is
  * set beside the same contract filled by an unfiltered name, `c y`. Every name
  * is a production name of the extractor. Derived before the run from
  * `SpecializationAttraction`, `Compression` and `ContentOrder`: p reads count
  * 0, a filter's root and at least one unfiltered left; ℓ reads (0, Filter, 0);
  * `t ℓ`, the tag given its last argument, reads as ℓ; `ℓ1 + ℓ2`, a choice
  * every member of which reads as a filter, reads (0, Filter, 0); so S and p
  * are one reading of K and S wins. `c ℓ`, a filter filling the hole, takes
  * back the empty hole's unfiltered argument, (0, Filter, 1), against `c y`'s
  * (1, Filter, 1): `c ℓ` wins. Where a rule reads S otherwise than as a filter,
  * so it was before the storage leaf rule (0f32fb14b), where ℓ read as a plain
  * name of root Other: S and p are two readings and `g`, one unfiltered
  * application more over S, gives p the class; and `c ℓ` ties `c y` in this
  * module and in size, and `ContentOrder`, a name before a storage leaf, gives
  * `c y` the class. Both extractions are checked, the round's
  * (`CountedExtraction`) for every case and the write-back's
  * (`LocalExtraction`) where its choice is derivable, for S = ℓ alone: it
  * finalizes classes greedily in the order of their costs, and a parent cheaper
  * than a child (`t`, of a marker's root, reads dearer than `t ℓ`) can be
  * finalized before the child's production is offered. Its purpose is to catch
  * a reading of a storage, or of a tag, a choice or a contract over storages,
  * under which a storage loses to another member of its class.
  */
class StorageLeafExtractionLawTest extends GeneratedProperties:

  private given StandInStorages.type = StandInStorages

  private val modules: Vector[NormalityModule[StandInStorages.type]] = Vector(
    SpecializationAttraction.at[StandInStorages.type],
    Compression.at[StandInStorages.type]
  )

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  property(
    "a class of a storage side and a written typed member is spelled by the storage side at an application of it"
  ) {
    for round <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
    yield
      def name(role: String): StandInStorages.Term =
        StandInStorages.opaque(s"storage leaf extraction $role $round")
      val (g, f, a, filterA, filterB, constructor, criterion, x) =
        (
          name("g"),
          name("f"),
          name("a"),
          name("A"),
          name("B"),
          name("C"),
          name("T"),
          name("x")
        )
      // The tag is a key of the facts, so it is pure.
      val tagKey = Pure
        .of(com.yang_bo.gezi.ir.NoFacts.opaque(s"storage leaf extraction t $round"))
        .getOrElse(
          throw IllegalStateException("an opaque term holds no parallel")
        )
      val tag = Configured.fromPure(StandInStorages)(tagKey)
      val (h, range, unfiltered) = (name("h"), name("R"), name("y"))
      val names = Set(
        g,
        f,
        a,
        filterA,
        filterB,
        constructor,
        criterion,
        x,
        h,
        range,
        tag,
        unfiltered
      )
      // t a tag of one argument still missing (`tag_next`), read as its argument once given it.
      val index = StandardLibraryIndex(
        StandInStorages,
        Vector.empty,
        Vector.empty,
        Vector.empty,
        Vector(CombinatorProperty(tagKey, Property.TagNext))
      )
      // c = λy. h y ∥ R in the front end's spelling, slots numbered by first
      // occurrence in preorder: h slot 0, y slot 1 (the hole), R slot 2.
      val contract = NoFacts.thunkOrInstance(
        Code.Parallel(Code.Apply(Code.Slot(0), Code.Slot(1)), Code.Slot(2)),
        Vector(Hole.Bound(1)),
        Vector(h, range)
      )
      def parallel(
          left: StandInStorages.Term,
          right: StandInStorages.Term
      ): StandInStorages.Term = StandInStorages.parallel(left, right)
      def applied(
          function: StandInStorages.Term,
          argument: StandInStorages.Term
      ): StandInStorages.Term = StandInStorages.application(function, argument)
      val members = Vector(
        "f (a ∥ A) ∥ B" -> parallel(applied(f, parallel(a, filterA)), filterB),
        "C (a ∥ A) ∥ T" -> parallel(
          applied(constructor, parallel(a, filterA)),
          criterion
        ),
        "x ∥ T" -> parallel(x, criterion)
      )
      def storageOf(label: String): StandInStorages.Term =
        StandInStorages.stored(
          ExtractedStorage(name(s"value of $label"), criterion)
        )
      def choice(
          left: StandInStorages.Term,
          right: StandInStorages.Term
      ): StandInStorages.Term = StandInStorages.choice(left, right)
      // Each case: its label, the member written in the class, the storage
      // side united with it, and whether the write-back's choice is derivable.
      val cases = members.flatMap { (shape, member) =>
        val storage = storageOf(shape)
        Vector(
          (s"ℓ beside $shape", member, storage, true),
          (s"t ℓ beside $shape", member, applied(tag, storage), false),
          (
            s"ℓ1 + ℓ2 beside $shape",
            member,
            choice(storage, storageOf(s"second beside $shape")),
            false
          )
        )
      } :+ (
        "c ℓ beside c y",
        applied(contract, unfiltered),
        applied(contract, storageOf("contract")),
        false
      )
      Result.all(cases.toList.map {
        (label, member, storageSide, writeBackDerivable) =>
          val parent = applied(g, member)
          val (withParent, parentNode) = EGraph
            .empty(
              Store(
                noinline = names,
                com.yang_bo.gezi.ir.TermConstruction(StandInStorages)
              ),
              Map.empty,
              explained = false
            )
            .instructionAdded(parent)
          val (withStorage, storageNode) =
            withParent.instructionAdded(storageSide)
          val graph = withStorage.unionWorked(
            withStorage.instructionNode(member).get,
            storageNode,
            lemma,
            None
          )
          val stop = StopSignal.completedWith(scala.concurrent.Future.never)
          val model = ModuleCostModel(modules, TermReading(index), stop)
          val extracted = CountedExtraction
            .fixed(graph, names, model, stop)
            .getOrElse(
              throw IllegalStateException("the extraction was stopped")
            )
          val spelled = FixpointEgraph.outputsSpelled(
            extracted,
            Vector(graph.root(parentNode)),
            Vector(parent),
            graph.store.construction
          )
          val writeBack =
            LocalExtraction(modules, _ => names, SpellingRetention.NotKept)
          val (written, _) = writeBack.spelled(
            writeBack.prepared(index, graph),
            graph,
            parentNode,
            SpellingCache.empty,
            Set.empty
          )
          val expected = applied(g, storageSide)
          Result
            .diff(
              (spelled, if writeBackDerivable then written else expected),
              (Vector(expected), expected)
            )(_ == _)
            .log(label)
      })
  }
