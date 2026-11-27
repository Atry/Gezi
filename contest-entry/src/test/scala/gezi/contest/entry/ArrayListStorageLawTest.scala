package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import java.nio.file.Paths
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.ExpansionSource
import gezi.ir.Closed
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.StorageAccess
import gezi.ir.Value
import gezi.jit.ArrayListStorage
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.JitValue
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.StorageEncoding
import gezi.jit.StorageEncodingOperations
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions
import gezi.weakhead.ScottADTChoices

/** The laws of the array lists' storage (`ArrayListStorage`,
  * `Representation.ArrayListOf`), over a library compiled from
  * `tests/library_fixtures/array_list.lambdalattice`, which holds the array
  * lists' module (`corpora/compiler/array_list`), N the canonical naturals'
  * criterion `binary_set true` and A the array lists' `array_list N`. Derived
  * from the storage's definition and from section 24 of
  * `docs/design/gezi-set-equations-proofs.md`:
  *
  *   - the library's backend checks accept the module, the encoding makes array
  *     lists of the canonical naturals, and the unique spelling's premise
  *     `⊢ A = cons N A + nil` is shown for them (the premise's representations
  *     hold them, none a non-member);
  *   - a storage's view is `nil ∥ A`, or `cons s t ∥ A` with s the storage of
  *     its first element and t the storage of the suffix after it, which is one
  *     object with the storage of the same elements from one on;
  *   - the converting construction makes `cons s t ∥ A`, t an array list's
  *     storage, into the one storage of the elements, the very object the
  *     elements' storage is: one term, one object;
  *   - elements consed one by one onto a suffix (`StorageEncoding.arrayConsed`,
  *     the converting construction's cons) have the content hash codes of the
  *     same elements held at once, each computed in one step from the suffix's,
  *     so that a chain of 10⁵ conses hashes on no JVM stack;
  *   - an array list's storage reads back to the normal forms the same elements
  *     give as a list `cons (e1 ∥ N) (… nil) ∥ list_type N`, the two criteria
  *     equal by the β rule (lemma 24.1).
  *
  * Their purpose is to catch a view that is not the unique spelling, a written
  * spelling that makes a second object, a hash code that differs between two
  * holders of the same elements, and a readback that differs from the list's.
  */
class ArrayListStorageLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/array_list.lambdalattice"),
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/array_list_terms.lambdalattice",
          Vector("binary_set", "true", "nil", "cons", "list_type", "array_list")
        ),
        Expansions.none
      )
      ._1

  /** The library compiled before the first test, about 2.5 s, past a test's 3 s
    * deadline.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms, _ => facts)

  /** The backend's encoding, the configuration every storage of these laws is a
    * term of.
    */
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: StorageAccess = StorageAccess.granted()

  private def operations: StorageEncodingOperations[encoding.type] =
    encoding.operations

  /** A library member as a term of the encoding: the same object as the member
    * read with no facts.
    */
  private def term(name: String): Configured[encoding.type] =
    Configured.fromPure(encoding)(
      Pure.required(
        terms.getOrElse(
          name,
          throw IllegalArgumentException(s"no member $name")
        )
      )
    )

  private def value(name: String): JitValue[encoding.type] =
    Value.of(term(name))

  private val representation: Representation[Nothing] =
    Representation.ArrayListOf(BinaryNaturalNatives.canonical)

  private def natural(element: BigInteger): JitValue[encoding.type] =
    operations.storageOf(
      BinaryNaturalNatives.canonical,
      BinaryNatural(BigInt(element))
    )

  private def arrayStorage(
      values: Vector[BigInteger]
  ): JitValue[encoding.type] =
    operations.storageOf(
      representation,
      operations.arrayList(representation, values)
    )

  /** A closed value of the encoding as its term: a storage and a term of the
    * library hold no neutral value.
    */
  private def closedTerm(
      found: JitValue[encoding.type]
  ): Configured[encoding.type] =
    Closed
      .configured(found)
      .getOrElse(
        throw IllegalStateException(
          s"a storage or a library term is closed: $found"
        )
      )

  private val values: Gen[Vector[BigInteger]] =
    Gen
      .int(Range.linear(0, 40))
      .list(Range.linear(0, 6))
      .map(_.toVector.map(value => BigInteger.valueOf(value.toLong)))

  test(
    "the module is accepted, and the encoding makes the array lists of the canonical naturals"
  ) {
    assertEquals(
      operations.arrayListRepresentations,
      Vector(
        Representation.ArrayListOf(BinaryNaturalNatives.canonical),
        Representation.ArrayListOf(BinaryNaturalNatives.positive)
      )
    )
  }

  property(
    "a storage's view is the unique spelling, its tail the suffix's storage"
  ) {
    for elements <- values.forAll
    yield
      val stored = arrayStorage(elements) match
        case JitValue.Stored(storage: ArrayListStorage) => storage
        case other                                      =>
          throw IllegalStateException(
            s"an array list's storage is an ArrayListStorage, not $other"
          )
      val view = encoding.viewOf(stored)
      val expected: Configured[encoding.type] =
        if elements.isEmpty then term("nil")
        else
          closedTerm(
            JitValue.Apply(
              JitValue.Apply(value("cons"), natural(elements.head)),
              arrayStorage(elements.tail)
            )
          )
      // The view's left side as the JIT's value it is; its tail, the suffix's
      // storage, is the one object of the elements after the first, however
      // they are held.
      val tailIsSuffix = Value.of(view.value) match
        case JitValue.Apply(_, tail) if elements.nonEmpty =>
          Value.same(
            tail,
            operations.storageOf(
              representation,
              NativeValue.ArrayListed(
                stored.listed.elements,
                stored.listed.start + 1
              )
            )
          ) &&
          Value.same(tail, arrayStorage(elements.tail))
        case _ => elements.isEmpty
      Result.assert(
        Configured.same(view.value, expected) &&
          Configured.same(
            view.criterion,
            closedTerm(operations.criterionOf(representation))
          ) &&
          tailIsSuffix
      )
  }

  property(
    "the converting construction makes `cons s t ∥ A` the elements' one storage"
  ) {
    for
      first <- Gen.int(Range.linear(0, 40)).forAll
      rest <- values.forAll
    yield
      val head = BigInteger.valueOf(first.toLong)
      val written = Value.Parallel(
        JitValue.Apply(
          JitValue.Apply(value("cons"), natural(head)),
          arrayStorage(rest)
        ),
        operations.criterionOf(representation)
      )
      Result.assert(Value.same(written, arrayStorage(head +: rest)))
  }

  test(
    "a chain of 10⁵ conses has the hash codes of its elements held at once"
  ) {
    val elements =
      Vector.tabulate(100000)(index => BigInteger.valueOf((index % 41).toLong))
    val consed = elements.foldRight(
      operations.arrayList(representation, Vector.empty)
    )(operations.arrayConsed(representation, _, _))
    val held = operations.arrayList(representation, elements)
    assertEquals(
      (consed.elements.contentHashes(0), consed.hashCode),
      (held.elements.contentHashes(0), held.hashCode)
    )
  }

  stoppableProperty(
    "an array list reads back to the normal forms of the same elements as a list"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for elements <- values.forAll
    yield
      val naturals = encoding.application(term("binary_set"), term("true"))
      val asList = encoding.parallel(
        elements.foldRight(term("nil"))((element, rest) =>
          encoding.application(
            encoding.application(
              term("cons"),
              encoding.parallel(closedTerm(natural(element)), naturals)
            ),
            rest
          )
        ),
        encoding.application(term("list_type"), naturals)
      )
      Result.assert(
        sameReadings(
          normalForms(closedTerm(arrayStorage(elements)), stop),
          normalForms(asList, stop)
        )
      )
  }

  /** Two readings alike: both stopped, or both finished with the same Scott ADT
    * values and flags.
    */
  private def sameReadings(
      left: Option[ScottADTChoices.Read[encoding.type]],
      right: Option[ScottADTChoices.Read[encoding.type]]
  ): Boolean = (left, right) match
    case (None, None)                => true
    case (Some(first), Some(second)) =>
      ScottADTChoices.same(first.choices, second.choices) &&
      first.nothingDropped == second.nothingDropped && first.noChoiceSplit == second.noChoiceSplit
    case _ => false

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = false,
    instanceTableTrial = gezi.jit.TableCost.trial,
    instanceRetention = InstanceRetentionOption.Generations(
      gezi.jit.JitConfiguration.defaultInstanceTableGeneration
    ),
    budget = gezi.jit.JitConfiguration.defaultBudget,
    checkpoints = CheckpointOption.Profitable,
    nativeBlocks = NativeBlocksOption.None,
    lookahead = LookaheadOption.Lazily,
    instanceReuse = InstanceReuseOption.WithinVersion
  )

  private val readingOptions =
    ReadingOptions(
      ApplicationOption.ByLayer,
      TableSharingOption.Local,
      TableRetentionOption.NoneKept,
      ContinuationOption.Substituted,
      ParallelOption.BothSides
    )

  private def normalForms(
      program: Configured[encoding.type],
      stop: StopSignal
  ): Option[ScottADTChoices.Read[encoding.type]] =
    val jit = Defaults.jit(encoding, jitOptions, GroupBlocksOption.None, access)
    val executor = Defaults.executor(jit, readingOptions)
    Judgments
      .read(
        executor,
        ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
        program,
        1000000L,
        stop,
        jit.readingConfiguration
      )
      .read
