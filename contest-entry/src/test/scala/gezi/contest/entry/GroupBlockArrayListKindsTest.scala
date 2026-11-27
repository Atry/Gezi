package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import java.nio.file.Paths
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Closed
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.StorageAccess
import gezi.ir.Value
import gezi.jit.ArrayItem
import gezi.jit.ArrayListStorage
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.JitValue
import gezi.jit.JvmIntNatives
import gezi.jit.Representation
import gezi.jit.StorageEncoding
import gezi.jit.StorageEncodingOperations
import gezi.narrowblocks.groups.GroupBackend
import gezi.narrowblocks.groups.GroupBlockMechanism
import gezi.narrowblocks.groups.GroupCompilation
import gezi.narrowblocks.groups.GroupGrammar
import gezi.narrowblocks.groups.GroupRun
import gezi.narrowblocks.groups.GroupValue
import gezi.narrowblocks.groups.JvmArrayGroupBackend
import gezi.narrowblocks.groups.ScalarGroupBackend
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions

/** The laws of array lists of the three element kinds an encoding makes
  * them of, the canonical naturals (N), the positive ones (P) and the 32-bit
  * words held as a JVM `int` (J), in storages and in group blocks, over the
  * library of `tests/library_fixtures/jvm_int_array_list.lambdalattice`;
  * `A E` is `array_list E`. Derived before the run from the encoding's
  * definitions and the block's invariant that every list of a column no
  * filter reads is of the column's static representation:
  *
  *  - the encoding makes array lists of N, P and J, in that order, and the
  *    unique spelling's premise has no nonmember;
  *  - a storage of a list of words is one object whatever vector holds its
  *    elements; its view is nil, or `cons s t ∥ A J` with s the word's
  *    storage and t the suffix's storage;
  *  - relabelling (`StorageEncoding.relabelled`, proofs section 26) gives,
  *    for a list of positive naturals under `A N`, for a list of naturals
  *    with no zero under `A P`, and for the empty list of any kind under any
  *    array list's criterion, the one storage of the target of the same
  *    elements; nothing for a list holding zero under `A P`, nor for a
  *    nonempty list of naturals under `A J`. In a block only the first
  *    occurs; the filtered term has no answer itself (proofs section 26,
  *    lemma 26.3), but a context consuming it can, so the block does not
  *    drop the row: it stops, giving no value, and the reading reads the
  *    application; a list of another element family is never filtered or
  *    entered in a block;
  *  - a block `λx. x ∥ A E` gives exactly that: the relabelled storage, or
  *    no value (it stops) when relabelling gives nothing, on both backends;
  *  - L1 to L3 on words: the sum by `int32_add` with an accumulator, wrapped
  *    modulo 2³²; the reverse, by cons onto an accumulator from
  *    `nil ∥ A J`, the storage of the reversed vector; the length counted
  *    by `int32_add 1`;
  *  - a cons onto a list of another representation, `cons 1 (x ∥ A N) ∥ A
  *    P`, is no block (the rest must be of the cons's representation); with
  *    `x ∥ A P` it is, and gives the storage of the consed vector under `A
  *    P` when 1 is positive;
  *  - a list of words reversed in a block leaves it as the storage of the
  *    reversed vector, and no list of the reversal is scanned for its hash
  *    codes: each cons computes its own from its rest's in one step, so the
  *    reversal is linear; conses onto a list given whole do so too, and a
  *    cons onto a relabelled list is the storage of the same vector;
  *  - an array list's filter on a natural is no block;
  *  - programs mixing the filters (a recursion that copies its argument,
  *    called under `A P` and reading it under `A N`; a list filtered by `A P`
  *    then by `A N`) give the storage of `A N` of the same elements when the
  *    list holds no zero, no answer when it holds one, and nil under `A N`
  *    for the empty list of words.
  *
  * Their purpose is to catch a list of one element kind read or stored as
  * another, a relabelling that keeps a list a filter rejects or drops one it
  * admits, a block whose exit is not the unique spelling, and a cons across
  * representations compiled into a block.
  */
class GroupBlockArrayListKindsTest extends GeneratedProperties:

  private def fewInputs(config: hedgehog.core.PropertyConfig): hedgehog.core.PropertyConfig =
    config.copy(testLimit = hedgehog.core.SuccessCount(10))

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(buildRoot, buildRoot.resolve("tests/library_fixtures/jvm_int_array_list.lambdalattice"), Vector(BackendChecks))

  private lazy val facts = BackendFacts.of(library)

  /** The backend's encoding, the configuration every program and storage of these laws is a term of. */
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: StorageAccess = StorageAccess.granted()

  private def operations: StorageEncodingOperations[encoding.type] = encoding.operations

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/jvm_int_array_list_terms.lambdalattice",
          Vector("binary_set", "true", "false", "boolean_type", "nil", "cons", "list_type", "array_list", "jvm_int_type", "int32_add")
        ),
        Expansions.none
      )
      ._1

  private lazy val compilation = GroupCompilation(facts)

  /** The library compiled, its terms read and its unique spelling's premise
    * shown before the first test, not charged to it.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms, _ => compilation)

  /** A library member as a term of the encoding: the same object as the member read with no facts. */
  private def term(name: String): Configured[encoding.type] =
    Configured.fromPure(encoding)(Pure.required(terms.getOrElse(name, throw IllegalArgumentException(s"no member $name"))))

  /** A closed value of the encoding as its term: a storage holds no neutral value. */
  private def closedTerm(found: JitValue[encoding.type]): Configured[encoding.type] =
    Closed.configured(found).getOrElse(throw IllegalStateException(s"a storage is closed: $found"))

  private lazy val fixpoint: Configured[encoding.type] = Configured.fromPure(encoding)(GroupGrammar.fixpointByValue)

  private lazy val naturals: Configured[encoding.type] = encoding.application(term("binary_set"), term("true"))
  private lazy val positives: Configured[encoding.type] = encoding.application(term("binary_set"), term("false"))
  private lazy val words: Configured[encoding.type] = term("jvm_int_type")
  private def listsOf(element: Configured[encoding.type]): Configured[encoding.type] = encoding.application(term("array_list"), element)

  private val naturalLists: Representation[Nothing] = Representation.ArrayListOf(BinaryNaturalNatives.canonical)
  private val positiveLists: Representation[Nothing] = Representation.ArrayListOf(BinaryNaturalNatives.positive)
  private val wordLists: Representation[Nothing] = Representation.ArrayListOf(JvmIntNatives.jvmInt)

  private def listStorage(representation: Representation[Nothing], values: Vector[ArrayItem]): JitValue[encoding.type] =
    operations.storageOf(representation, operations.arrayList(representation, values))

  private def word(bits: Int): Configured[encoding.type] = closedTerm(operations.storageOf(JvmIntNatives.jvmInt, JvmIntNatives.value(bits)))

  private def natural(value: Long): Configured[encoding.type] =
    closedTerm(operations.storageOf(BinaryNaturalNatives.canonical, BinaryNatural(BigInt(value))))

  private def naturalItems(values: Vector[Int]): Vector[ArrayItem] = values.map(value => BigInteger.valueOf(value.toLong): ArrayItem)

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code = arguments.foldLeft(function)(Code.Apply(_, _))

  private def filtered(value: Code, criterion: Code): Code = Code.Parallel(value, criterion)

  /** A block of one parameter, x at slot 0, the captures from slot 1. */
  private def block(code: Code, captures: Configured[encoding.type]*): Configured[encoding.type] =
    encoding.thunkOrInstance(code, Vector(Hole.Bound(0)), captures.toVector)

  private val backends: Vector[GroupBackend] = Vector(ScalarGroupBackend, JvmArrayGroupBackend)

  /** The block's value on the argument, on each backend, through the JIT's
    * mechanism, its exit included: none when the thunk is no block.
    */
  private def results(stop: StopSignal, thunk: Configured[encoding.type], argument: JitValue[encoding.type]): Vector[Option[JitValue[encoding.type]]] =
    backends.map(backend =>
      val mechanism = GroupBlockMechanism(compilation, facts, backend)
      mechanism.compiled(thunk, operations).flatMap(artifact => artifact.run(Vector(argument), 100000000L, stop)).flatMap(_.value)
    )

  /** Whether each value found is the very object expected, and none is
    * found where none is expected.
    */
  private def sameObjects(found: Vector[Option[JitValue[encoding.type]]], expected: Vector[Option[JitValue[encoding.type]]]): Boolean =
    found.size == expected.size && found.lazyZip(expected).forall((one, other) => one.isDefined == other.isDefined && one.zip(other).forall((first, second) => Value.same(first, second)))

  private def sameObjectsOnEachBackend(found: Vector[Vector[Option[JitValue[encoding.type]]]], expected: Vector[Vector[Option[JitValue[encoding.type]]]]): Boolean =
    found.size == expected.size && found.lazyZip(expected).forall(sameObjects)

  private val ints: Gen[Vector[Int]] =
    Gen
      .frequency1(3 -> Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)), 1 -> Gen.element1(0, 1, -1, Int.MinValue, Int.MaxValue))
      .list(Range.linear(0, 6))
      .map(_.toVector)

  private val small: Gen[Vector[Int]] = Gen.int(Range.linear(0, 40)).list(Range.linear(0, 6)).map(_.toVector)

  test("the encoding makes array lists of N, P and J") {
    assertEquals(operations.arrayListRepresentations, Vector(naturalLists, positiveLists, wordLists))
  }

  property("a list of words has one storage, its view the unique spelling, its hash code the written term's") {
    for values <- ints.forAll
    yield
      val items = values.map(bits => bits: ArrayItem)
      val stored = listStorage(wordLists, items)
      // Another vector of the same elements, a second holder.
      val again = listStorage(wordLists, values.reverse.reverse.map(bits => bits: ArrayItem))
      val view = stored match
        case JitValue.Stored(storage: ArrayListStorage) => encoding.viewOf(storage)
        case other                                      => throw IllegalStateException(s"an array list's storage, not $other")
      val expectedLeft: Configured[encoding.type] =
        if values.isEmpty then term("nil")
        else closedTerm(JitValue.Apply(JitValue.Apply(Value.of(term("cons")), Value.of(word(values.head))), listStorage(wordLists, items.tail)))
      Result.assert(
        Value.same(stored, again) && Configured.same(view.value, expectedLeft) &&
          Configured.same(view.criterion, closedTerm(operations.criterionOf(wordLists)))
      )
  }

  property("relabelling gives the target's one storage of the same elements, or nothing where the target rejects one") {
    for
      values <- small.forAll
      positive = values.map(value => value + 1)
      withZero <- Gen.int(Range.linear(0, values.size)).map(at => values.patch(at, Vector(0), 0)).forAll
    yield
      def relabelled(source: Representation[Nothing], items: Vector[ArrayItem], target: Representation[Nothing]): Option[JitValue[encoding.type]] =
        operations.relabelled(operations.arrayList(source, items), target).map(operations.storageOf(target, _))
      val found = Vector(
        relabelled(positiveLists, naturalItems(positive), naturalLists),
        relabelled(naturalLists, naturalItems(positive), positiveLists),
        relabelled(naturalLists, naturalItems(withZero), positiveLists),
        relabelled(naturalLists, Vector.empty, wordLists),
        relabelled(wordLists, Vector.empty, positiveLists),
        relabelled(naturalLists, naturalItems(withZero), wordLists)
      )
      val expected = Vector(
        Some(listStorage(naturalLists, naturalItems(positive))),
        Some(listStorage(positiveLists, naturalItems(positive))),
        None,
        Some(listStorage(wordLists, Vector.empty)),
        Some(listStorage(positiveLists, Vector.empty)),
        None
      )
      Result.assert(sameObjects(found, expected))
  }

  stoppableProperty("a block filtering its list by another array list's criterion gives the relabelled storage, or no answer", fewInputs) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      values <- small.forAll
      positive = values.map(value => value + 1)
      withZero <- Gen.int(Range.linear(0, values.size)).map(at => values.patch(at, Vector(0), 0)).forAll
    yield
      // λx. x ∥ A E: x 0, A E 1.
      def under(element: Configured[encoding.type]): Configured[encoding.type] = block(filtered(slot(0), slot(1)), listsOf(element))
      val found = Vector(
        results(stop, under(naturals), listStorage(positiveLists, naturalItems(positive))),
        results(stop, under(positives), listStorage(naturalLists, naturalItems(positive))),
        results(stop, under(positives), listStorage(naturalLists, naturalItems(withZero))),
        results(stop, under(naturals), listStorage(wordLists, Vector.empty)),
        results(stop, under(words), listStorage(naturalLists, naturalItems(withZero)))
      )
      // A list of another element family does not enter the block (its
      // kind does not agree with the parameter's filter): the reading reads
      // the term.
      val expected = Vector(
        Some(listStorage(naturalLists, naturalItems(positive))),
        Some(listStorage(positiveLists, naturalItems(positive))),
        None,
        None,
        None
      )
      Result.diff(found, expected.map(value => Vector(value, value)))(sameObjectsOnEachBackend)
  }

  /** S: self 0, l 1, acc 2, J 3, A J 4, add 5, one 6; its cons case reads
    * h 0, t 1, self 2, acc 3, J 4, A J 5, add 6, one 7, and calls self on t
    * and `int32_add h acc` (`summing`) or `int32_add one acc`.
    */
  private def folding(summing: Boolean): Configured[encoding.type] =
    val added = if summing then filtered(slot(0), slot(4)) else slot(7)
    val call = filtered(applied(slot(2), filtered(slot(1), slot(5)), applied(slot(6), added, filtered(slot(3), slot(4)))), slot(4))
    encoding.thunkOrInstance(
      applied(filtered(slot(1), slot(4)), filtered(slot(2), slot(3)), Code.Thunk(call, Vector(Hole.Bound(0), Hole.Bound(1)), Vector(0, 2, 3, 4, 5, 6).map(slot))),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(words, listsOf(words), term("int32_add"), word(1))
    )

  /** `λx. fixpoint S (x ∥ A J) zero ∥ J`: x 0, fixpoint 1, S 2, A J 3, J 4, zero 5. */
  private def folded(summing: Boolean): Configured[encoding.type] =
    block(
      filtered(applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3)), slot(5)), slot(4)),
      fixpoint,
      folding(summing),
      listsOf(words),
      words,
      word(0)
    )

  /** R: self 0, l 1, acc 2, A J 3, J 4, cons 5; its cons case reads h 0, t 1,
    * self 2, acc 3, A J 4, J 5, cons 6.
    */
  private lazy val reversing: Configured[encoding.type] =
    val consed = filtered(applied(slot(6), filtered(slot(0), slot(5)), filtered(slot(3), slot(4))), slot(4))
    encoding.thunkOrInstance(
      applied(
        filtered(slot(1), slot(3)),
        filtered(slot(2), slot(3)),
        Code.Thunk(filtered(applied(slot(2), filtered(slot(1), slot(4)), consed), slot(4)), Vector(Hole.Bound(0), Hole.Bound(1)), Vector(0, 2, 3, 4, 5).map(slot))
      ),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(listsOf(words), words, term("cons"))
    )

  /** `λx. fixpoint R (x ∥ A J) (nil ∥ A J) ∥ A J`: x 0, fixpoint 1, R 2, A J 3, nil 4. */
  private lazy val reverse: Configured[encoding.type] =
    block(
      filtered(applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3)), filtered(slot(4), slot(3))), slot(3)),
      fixpoint,
      reversing,
      listsOf(words),
      term("nil")
    )

  stoppableProperty("L1 to L3 on words: the sum modulo 2³², the reverse and the length, on both backends", fewInputs) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- ints.forAll
    yield
      val list = listStorage(wordLists, values.map(bits => bits: ArrayItem))
      val found = Vector(results(stop, folded(summing = true), list), results(stop, reverse, list), results(stop, folded(summing = false), list))
      val expected = Vector(
        Value.of(word(values.foldLeft(0)(_ + _))): JitValue[encoding.type],
        listStorage(wordLists, values.reverse.map(bits => bits: ArrayItem)),
        Value.of(word(values.size)): JitValue[encoding.type]
      )
      Result.diff(found, expected.map(value => Vector(Some(value), Some(value))))(sameObjectsOnEachBackend)
  }

  stoppableProperty("a cons onto a list of another representation is no block; onto one of its own it is", fewInputs) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- small.forAll
    yield
      // λx. cons one (x ∥ A R) ∥ A P: x 0, cons 1, one 2, A R 3, A P 4.
      def consedOnto(rest: Configured[encoding.type]): Configured[encoding.type] =
        block(filtered(applied(slot(1), slot(2), filtered(slot(0), slot(3))), slot(4)), term("cons"), natural(1), listsOf(rest), listsOf(positives))
      val positive = naturalItems(values.map(_ + 1))
      val list = listStorage(positiveLists, positive)
      val expected = listStorage(positiveLists, naturalItems(Vector(1)) ++ positive)
      Result.diff(
        (compilation.compiled(consedOnto(naturals), operations).isDefined, results(stop, consedOnto(positives), list).map(_.exists(Value.same(_, expected)))),
        (false, Vector(true, true))
      )(_ == _)
  }

  test("an array list's filter on a value of another kind is no block, directly or through a recursion's parameter") {
    // λx. (x ∥ C) ∥ A N: x 0, C 1, A N 2. A truth value is no list, though
    // true is nil's term, so `true ∥ A N` is nil: a block would lose it or,
    // relabelling no list, throw; the general reading reads it.
    def filteredTwice(criterion: Configured[encoding.type]): Configured[encoding.type] = block(filtered(filtered(slot(0), slot(1)), slot(2)), criterion, listsOf(naturals))
    // λx. fixpoint T (x ∥ C) ∥ A N, T reading its parameter under A N only:
    // the parameter's kind comes from its occurrences, a list, which the
    // call's argument, of C, is not.
    def copiedUnder(criterion: Configured[encoding.type]): Configured[encoding.type] =
      block(
        filtered(applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3))), slot(4)),
        fixpoint,
        copying,
        criterion,
        listsOf(naturals)
      )
    // λx. (x ∥ A N) ∥ boolean_type: x 0, A N 1, boolean_type 2. Conversely a
    // list under the booleans' criterion: nil is true, so a block dropping the
    // row would lose it.
    val listUnderTruths = block(filtered(filtered(slot(0), slot(1)), slot(2)), listsOf(naturals), term("boolean_type"))
    // U: self 0, l 1, A N 2, N 3, nil 4; its cons case reads h 0, t 1, self 2,
    // A N 3, N 4 and calls self on `h ∥ N`. l's kind comes from its
    // occurrences, a list, which the self call's argument, a natural, is not.
    val callingOnHead = encoding.thunkOrInstance(
      applied(
        filtered(slot(1), slot(2)),
        filtered(slot(4), slot(2)),
        Code.Thunk(filtered(applied(slot(2), filtered(slot(0), slot(4))), slot(3)), Vector(Hole.Bound(0), Hole.Bound(1)), Vector(0, 2, 3).map(slot))
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(listsOf(naturals), naturals, term("nil"))
    )
    // λx. fixpoint U (x ∥ A N) ∥ A N: x 0, fixpoint 1, U 2, A N 3.
    val selfCalledOnHead =
      block(filtered(applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3))), slot(3)), fixpoint, callingOnHead, listsOf(naturals))
    // The same U calling itself on `t ∥ A N`, the twin that compiles: only the
    // self call's argument differs.
    val callingOnTail = encoding.thunkOrInstance(
      applied(
        filtered(slot(1), slot(2)),
        filtered(slot(4), slot(2)),
        Code.Thunk(filtered(applied(slot(2), filtered(slot(1), slot(3))), slot(3)), Vector(Hole.Bound(0), Hole.Bound(1)), Vector(0, 2, 3).map(slot))
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(listsOf(naturals), naturals, term("nil"))
    )
    val selfCalledOnTail =
      block(filtered(applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3))), slot(3)), fixpoint, callingOnTail, listsOf(naturals))
    // λx. (x ∥ A J) ∥ A N: words relabelled as naturals, of another family.
    val wordsUnderNaturals = block(filtered(filtered(slot(0), slot(1)), slot(2)), listsOf(words), listsOf(naturals))
    val programs = Vector(
      filteredTwice(term("boolean_type")),
      filteredTwice(naturals),
      copiedUnder(term("boolean_type")),
      copiedUnder(naturals),
      listUnderTruths,
      selfCalledOnHead,
      wordsUnderNaturals,
      selfCalledOnTail
    )
    assertEquals(programs.map(compilation.compiled(_, operations).isDefined), programs.map(_ => false).init :+ true)
  }

  stoppableTest("a block whose parameter is read as a list is not entered with a value of another kind") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    // λx. x ∥ A N: x 0, A N 1, entered with the truth true, which is nil's
    // term: the block is not entered, and the reading reads the term. The
    // mechanism is run directly, as the JIT runs it after its entry decode.
    val truth = operations.storageOf(Representation.Truth, gezi.jit.NativeValue.Truth(true))
    assertEquals(results(stop, block(filtered(slot(0), slot(1)), listsOf(naturals)), truth).map(_.isDefined), Vector(false, false))
  }

  /** The elements of the block's list results on the list, on each backend,
    * as the block holds them before its exit interns them: an interned
    * storage holds whichever holder of the same elements was made first.
    */
  private def heldResults(stop: StopSignal, thunk: Configured[encoding.type], list: JitValue[encoding.type]): Vector[Option[Vector[gezi.jit.ArrayElements]]] =
    val block = compilation.compiled(thunk, operations).getOrElse(throw IllegalStateException(s"the block compiles: $thunk"))
    val listed = list match
      case JitValue.Stored(storage: ArrayListStorage) => storage.listed
      case other                                      => throw IllegalStateException(s"an array list's storage, not $other")
    backends.map(backend =>
      GroupRun.run(block, Vector(Vector(GroupValue.List(listed))), backend, 100000000L, stop).results.map(_.collect {
        case GroupValue.List(found) => found.elements
      })
    )

  stoppableProperty("a list of words reversed in a block leaves as the reversed vector's storage, its hash codes given at each cons") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- ints.forAll
    yield
      // Each cons computes its content hash codes from its rest's in one step
      // (`arrayConsed`), so no list of the reversal is scanned: the result's
      // are given, never computed by a pass; the empty accumulator's own pass
      // is over no element. A reversal of one element or none is the
      // accumulator or a cons onto it alike.
      val list = listStorage(wordLists, values.map(bits => bits: ArrayItem))
      val expected = listStorage(wordLists, values.reverse.map(bits => bits: ArrayItem))
      Result.diff(
        (results(stop, reverse, list).map(_.exists(Value.same(_, expected))), heldResults(stop, reverse, list).map(_.map(_.map(found => found.hashesGiven || found.values.isEmpty)))),
        (Vector(true, true), Vector(Some(Vector(true)), Some(Vector(true))))
      )(_ == _)
  }

  property("conses onto a list given whole compute their hash codes in one step") {
    for
      values <- ints.forAll
      items <- Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)).list(Range.linear(1, 4)).map(_.toVector).forAll
    yield
      // The given list's content hash codes are computed in one pass when the
      // first cons asks them, and each cons extends its rest's in one step,
      // so every consed list is given its own and none is scanned again.
      val whole = operations.arrayList(wordLists, values.map(bits => bits: ArrayItem))
      val consed = items.scanRight(whole)((bits, rest) => operations.arrayConsed(wordLists, bits, rest)).init
      Result.diff(
        consed.map(_.elements.hashesGiven),
        consed.map(_ => true)
      )(_ == _)
  }

  property("a cons onto a relabelled list is the storage of the same vector, its hash codes given") {
    for values <- small.forAll
    yield
      // Relabelled elements share the content's hash codes, so a cons onto
      // them computes its own in one step.
      val positive = naturalItems(values.map(_ + 1))
      val relabelled = operations.relabelled(operations.arrayList(positiveLists, positive), naturalLists).getOrElse(throw IllegalStateException("a list of positives is one of naturals"))
      val consed = operations.arrayConsed(naturalLists, BigInteger.ZERO, relabelled)
      Result.diff(
        (consed.elements.hashesGiven, Value.same(operations.storageOf(naturalLists, consed), listStorage(naturalLists, naturalItems(Vector(0)) ++ positive))),
        (true, true)
      )(_ == _)
  }

  /** T: self 0, l 1, A N 2, N 3, cons 4, nil 5; its cons case reads h 0,
    * t 1, self 2, A N 3, N 4, cons 5, and copies the list under `A N`.
    */
  private lazy val copying: Configured[encoding.type] =
    val copied = filtered(applied(slot(5), filtered(slot(0), slot(4)), filtered(applied(slot(2), filtered(slot(1), slot(3))), slot(3))), slot(3))
    encoding.thunkOrInstance(
      applied(filtered(slot(1), slot(2)), filtered(slot(5), slot(2)), Code.Thunk(copied, Vector(Hole.Bound(0), Hole.Bound(1)), Vector(0, 2, 3, 4, 5).map(slot))),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(listsOf(naturals), naturals, term("cons"), term("nil"))
    )

  /** `λx. fixpoint T (x ∥ A P) ∥ A N`: x 0, fixpoint 1, T 2, A P 3, A N 4. */
  private lazy val copiedUnderPositives: Configured[encoding.type] =
    block(
      filtered(applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3))), slot(4)),
      fixpoint,
      copying,
      listsOf(positives),
      listsOf(naturals)
    )

  /** `λx. (x ∥ A P) ∥ A N`: x 0, A P 1, A N 2. */
  private lazy val twiceFiltered: Configured[encoding.type] = block(filtered(filtered(slot(0), slot(1)), slot(2)), listsOf(positives), listsOf(naturals))

  stoppableProperty("programs mixing the filters give the values the relabelling equations derive, on both backends", fewInputs) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      values <- small.forAll
      zeroAt <- Gen.int(Range.linear(0, values.size)).forAll
    yield
      val (positive, withZero) = (naturalItems(values.map(_ + 1)), naturalItems(values.patch(zeroAt, Vector(0), 0)))
      val cases = Vector(
        // T copies its argument under A N, called under A P: a list of positives is kept and relabelled twice.
        (copiedUnderPositives, listStorage(positiveLists, positive), listStorage(naturalLists, positive)),
        (copiedUnderPositives, listStorage(naturalLists, positive), listStorage(naturalLists, positive)),
        (twiceFiltered, listStorage(naturalLists, positive), listStorage(naturalLists, positive))
      )
      // A zero fails the filter A P, which stops the block; the empty list of
      // words is of another element family, which enters no block: no value.
      val noValue = Vector(
        results(stop, copiedUnderPositives, listStorage(naturalLists, withZero)),
        results(stop, twiceFiltered, listStorage(naturalLists, withZero)),
        results(stop, copiedUnderPositives, listStorage(wordLists, Vector.empty)),
        results(stop, twiceFiltered, listStorage(wordLists, Vector.empty))
      )
      Result.diff(
        (cases.map((program, argument, expected) => results(stop, program, argument).map(_.exists(Value.same(_, expected)))), noValue),
        (cases.map(_ => Vector(true, true)), noValue.map(_ => Vector(None, None)))
      )(_ == _)
  }

  /** The JIT's machine, whose heads are the JIT's own (a storage left a
    * storage).
    */
  private lazy val rulesJit =
    Defaults.jit(
      encoding,
      JitOptions(
        DispatchOption.Fallback,
        BackendOption.Closure,
        GranularityOption.PredicatePerCode,
        instanceTable = false,
        instanceTableTrial = gezi.jit.TableCost.trial,
        instanceRetention = InstanceRetentionOption.Generations(gezi.jit.JitConfiguration.defaultInstanceTableGeneration),
        budget = gezi.jit.JitConfiguration.defaultBudget,
        checkpoints = CheckpointOption.Profitable,
        nativeBlocks = NativeBlocksOption.None,
        lookahead = LookaheadOption.Lazily,
        instanceReuse = InstanceReuseOption.WithinVersion
      ),
      GroupBlocksOption.Enabled(),
      access
    )

  private lazy val rules = gezi.jit.JitRules(rulesJit.configuration)

  /** The heads the JIT reads of a term, none when the reading did not end. */
  private def jitHeads(written: Configured[encoding.type]): Option[Vector[AnyRef]] =
    rules.heads(Value.of(written)).collected.result(gezi.weakhead.ReadingState.knowingTop(1000L, rulesJit.readingConfiguration)) match
      case gezi.weakhead.Computed.Done(found, _) => Some(found.map(head => head: AnyRef))
      case _                                     => None

  /** The law that the JIT and a block spell a relabelled array list alike:
    * a list of positive naturals written under `A N` is, at the JIT's decode
    * point, the one head that relabelling gives, the storage of `A N` of the
    * same elements, the object the block `λx. x ∥ A N` gives too (the case
    * above). Derived before the run from the decode point's use of
    * `StorageEncoding.relabelled`, the block's relabelling. Its purpose is to
    * catch the JIT reading such a list as cells of `list_type N`, another
    * spelling of the same term than the block's.
    */
  property("the JIT reads a list of positives under A N as the relabelled storage, the block's spelling", fewInputs) {
    for values <- small.forAll
    yield
      val positive = naturalItems(values.map(_ + 1))
      val written = encoding.parallel(closedTerm(listStorage(positiveLists, positive)), listsOf(naturals))
      val expected: AnyRef = listStorage(naturalLists, positive) match
        case JitValue.Stored(storage) => storage
        case other                    => throw IllegalStateException(s"an array list is a storage, not $other")
      Result.diff(jitHeads(written).map(_.map(_ eq expected)), Some(Vector(true)))(_ == _)
  }
