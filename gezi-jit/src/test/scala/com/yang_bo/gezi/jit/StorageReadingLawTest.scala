package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.hotspot.Retention
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.EvaluatorTesting
import com.yang_bo.gezi.weakhead.ListRepresentation
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NormalForms
import com.yang_bo.gezi.weakhead.ParallelReading
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.weakhead.TableSharing
import com.yang_bo.gezi.ir.Value

/** The laws of the reader's storage option (`com.yang_bo.gezi.weakhead.StorageReading`,
  * implemented by `StorageReadingOfFacts`) on generated lists of naturals in
  * the unique spelling, built through the conversion, read by the tabled weak
  * head. Its purpose is to catch an option that changes what a reading reads
  * (the elimination C ȳ of a storage and the conversion of a parallel are
  * equations: the unique spelling's pattern theorem and the conversion's
  * definition), that gives an open term a storage, that reads #2202's raw-tail
  * cell by its spelling, or whose completed tables a reading without the option
  * reads.
  */
class StorageReadingLawTest extends GeneratedProperties:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => encoding,
      _ => zero,
      _ => successor,
      _ => natType,
      _ => nil,
      _ => cons,
      _ => listType,
      _ => headCase,
      _ => even,
      _ => double,
      _ => identity
    )

  private lazy val facts = BackendFacts.of(NativesTesting.nativesOn)
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private lazy val option: StorageReadingOfFacts[encoding.type] =
    StorageReadingOfFacts[encoding.type](encoding)

  /** The configuration of the facts, under which the readings read their
    * storages.
    */
  private lazy val configuration = JitTesting.plainConfiguration(encoding)

  private lazy val zero: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("zero"))
  private lazy val successor: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("successor"))
  private lazy val natType: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("nat_type"))
  private lazy val nil: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("nil"))
  private lazy val cons: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("cons"))
  private lazy val listType: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("list_type"))
  private lazy val even: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("even"))
  private lazy val double: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("double"))
  private lazy val identity: Value[encoding.type] =
    JitTesting.termValue[encoding.type](Term.λ(x => x))

  /** The cases a list is read by, taking its head: zero for the empty list. */
  private lazy val headCase: Value[encoding.type] =
    JitTesting.termValue[encoding.type](Term.λ(head => Term.λ(_ => head)))

  private val limit: Long = 200000

  private def natural(value: Int): JitValue[encoding.type] =
    (1 to value).foldLeft(JitTesting.parallelOfValues(encoding)(zero, natType))(
      (inner, _) =>
        JitTesting
          .parallelOfValues(encoding)(JitValue.Apply(successor, inner), natType)
    )

  private def naturals: JitValue[encoding.type] =
    JitValue.Apply(listType, natType)

  private def listOf(items: Vector[Int]): JitValue[encoding.type] =
    items.foldRight(JitTesting.parallelOfValues(encoding)(nil, naturals))(
      (item, rest) =>
        JitTesting.parallelOfValues(encoding)(
          JitValue.Apply(
            JitValue.Apply(
              cons,
              JitTesting.parallelOfValues(encoding)(natural(item), natType)
            ),
            rest
          ),
          naturals
        )
    )

  /** The list applied to the cases zero and take-the-head. */
  private def headOf(list: JitValue[encoding.type]): Value[encoding.type] =
    Value.Apply(Value.Apply(list, zero), headCase)

  private def read(
      value: Value[encoding.type],
      state: ReadingState[encoding.type]
  ): Bounded[Vector[Configured[encoding.type]]] = readCounted(value, state)._1

  /** The normal forms, the steps spent and the natives called. */
  private def readCounted(
      value: Value[encoding.type],
      state: ReadingState[encoding.type]
  ): (Bounded[Vector[Configured[encoding.type]]], Long, Long) =
    NormalForms.normalForms(Mode.TablingWeakHead, value).result(state) match
      case Computed.Done(normalForms, after) =>
        (
          Bounded.Finished(
            normalForms.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering)
          ),
          after.budget.spent,
          after.nativeCalls
        )
      case Computed.Stopped(after) =>
        (EvaluatorTesting.stopped(after), after.budget.spent, after.nativeCalls)

  private def plainNatural(value: Int): JitValue[encoding.type] =
    (1 to value).foldLeft(zero)((inner, _) => JitValue.Apply(successor, inner))

  private val lists: Gen[Vector[Int]] =
    Gen.int(Range.linear(0, 6)).list(Range.linear(0, 6)).map(_.toVector)

  /** The list written plainly, `cons (successor^k zero) …` ending in nil, with
    * no filter and no storage.
    */
  private def plainListOf(items: Vector[Int]): JitValue[encoding.type] =
    items.foldRight(nil)((item, rest) =>
      JitValue.Apply(
        JitValue.Apply(
          cons,
          (1 to item).foldLeft(zero)((inner, _) =>
            JitValue.Apply(successor, inner)
          )
        ),
        rest
      )
    )

  // The reference is the same list written plainly, no storage in it.
  property(
    "with the option, a list of storages reads the normal forms of the list written plainly"
  ) {
    for items <- lists.forAll
    yield
      val withOption = read(
        headOf(listOf(items)),
        ReadingState.fresh(limit, configuration).copy(storages = Some(option))
      )
      val plain = read(
        headOf(plainListOf(items)),
        ReadingState.fresh(limit, configuration)
      )
      Result.all(
        List(
          Result
            .assert(plain.isInstanceOf[Bounded.Finished[?]])
            .log(s"the plain list's reading did not finish: $plain"),
          Result
            .assert(JitTesting.sameOutcomes(withOption, plain))
            .log(s"$withOption against $plain")
        )
      )
  }

  property(
    "the option converts no open term: a field holding a neutral value keeps the parallel"
  ) {
    for value <- Gen.int(Range.linear(0, 6)).forAll
    yield
      val opened = JitValue.Neutral[encoding.type](
        com.yang_bo.gezi.weakhead.BoundVariable(value),
        Vector.empty
      )
      val cell = JitValue.Apply(
        JitValue
          .Apply(cons, JitTesting.parallelOfValues(encoding)(opened, natType)),
        JitTesting.parallelOfValues(encoding)(nil, naturals)
      )
      val built = JitTesting.parallelOfValues(encoding)(cell, naturals)
      val openCriterion = JitValue.Apply(listType, opened)
      val emptyUnderOpen =
        JitTesting.parallelOfValues(encoding)(nil, openCriterion)
      Result.all(
        List(
          Result
            .assert(!com.yang_bo.gezi.ir.NativeStorage.stored(built.representation))
            .log(s"an open cell got a storage: $built"),
          Result
            .assert(
              !com.yang_bo.gezi.ir.NativeStorage.stored(emptyUnderOpen.representation)
            )
            .log(s"nil under an open criterion got a storage: $emptyUnderOpen")
        )
      )
  }

  /** A reading without the option on a cache a reading with it filled spends
    * exactly the steps of a reading without it on a fresh cache, and reads the
    * same: the reading is deterministic, and the option's reading completes the
    * table of the very key the plain one starts from, so a plain reading that
    * read the option's tables would hit that table and spend other steps than a
    * fresh one. The program is even of a natural's storage, which the option
    * reads by one call of the native and the plain reading through the
    * storage's views, so that the two readings' own steps differ, asserted so
    * that such a hit could not go unseen.
    */
  property(
    "a reading without the option reads the same whether or not a reading with it shared the cache first"
  ) {
    for value <- Gen.int(Range.linear(2, 30)).forAll
    yield
      val program = Value.Apply(even, natural(value))
      // One expansion source for both readings on the shared cache, so that
      // only the option tells their namespaces apart.
      val source = ExpansionSource.fresh()
      def shared(cache: com.yang_bo.gezi.hotspot.Cache) =
        TableSharing.Shared(cache, Retention.Strong, source)
      val (alone, aloneSteps, _) = readCounted(
        program,
        ReadingState
          .fresh(limit, configuration)
          .copy(sharing = shared(BaselineCaches.provider()))
      )
      val cache = BaselineCaches.provider()
      val (withOption, optionSteps, _) = readCounted(
        program,
        ReadingState
          .fresh(limit, configuration)
          .copy(sharing = shared(cache), storages = Some(option))
      )
      val (after, afterSteps, _) = readCounted(
        program,
        ReadingState.fresh(limit, configuration).copy(sharing = shared(cache))
      )
      Result.all(
        List(
          Result
            .assert(optionSteps != aloneSteps)
            .log(
              s"the readings with and without the option spent alike: $aloneSteps"
            ),
          Result
            .assert(
              JitTesting.sameOutcomes(after, alone) && afterSteps == aloneSteps
            )
            .log(
              s"$after in $afterSteps steps against $alone in $aloneSteps steps"
            ),
          Result
            .assert(JitTesting.sameOutcomes(withOption, alone))
            .log("the option changes no normal form")
        )
      )
  }

  // Derived before the run: even applied to a natural's storage is an exact
  // application of a native whose argument is a storage of its place, so it is
  // called once, its result a boolean's storage read as true or false whatever
  // the natural's size; the steps are those of that boolean's reading.
  property(
    "even of a natural's storage calls its native once, the steps the same for 10 and 1000"
  ) {
    for parity <- Gen.boolean.forAll
    yield
      val small = if parity then 10 else 11
      val large = if parity then 1000 else 1001
      val (smallForms, smallSteps, smallCalls) = readCounted(
        Value.Apply(even, natural(small)),
        ReadingState.fresh(limit, configuration).copy(storages = Some(option))
      )
      val (largeForms, largeSteps, largeCalls) = readCounted(
        Value.Apply(even, natural(large)),
        ReadingState.fresh(limit, configuration).copy(storages = Some(option))
      )
      Result.all(
        List(
          Result
            .diff((smallCalls, largeCalls), (1L, 1L))(_ == _)
            .log("native calls"),
          Result.diff(smallSteps, largeSteps)(_ == _).log("steps"),
          Result
            .assert(JitTesting.sameOutcomes(largeForms, smallForms))
            .log("the two parities read alike"),
          Result
            .assert(smallForms.isInstanceOf[Bounded.Finished[?]])
            .log(s"$smallForms")
        )
      )
  }

  // Derived before the run: the inner application is an exact application of
  // double on a storage, so the outer one has a value by the structural path:
  // two calls; the normal forms are those of the program written plainly.
  property(
    "double of double of a natural's storage calls its native twice and reads the plain program's normal forms"
  ) {
    for value <- Gen.int(Range.linear(0, 5)).forAll
    yield
      val (forms, _, calls) =
        readCounted(
          Value.Apply(double, Value.Apply(double, natural(value))),
          ReadingState.fresh(limit, configuration).copy(storages = Some(option))
        )
      val plain = read(
        Value.Apply(double, Value.Apply(double, plainNatural(value))),
        ReadingState.fresh(limit, configuration)
      )
      Result.all(
        List(
          Result.diff(calls, 2L)(_ == _).log("native calls"),
          Result
            .assert(JitTesting.sameOutcomes(forms, plain))
            .log("normal forms")
        )
      )
  }

  // Derived before the run: identity applied to the storage is no storage and
  // no native application, so the outer double has no value by the
  // structural path and is read as its term; the normal forms are the plain
  // program's.
  property(
    "double of a term a function that is no native computes calls no native"
  ) {
    for value <- Gen.int(Range.linear(0, 5)).forAll
    yield
      val (forms, _, calls) =
        readCounted(
          Value.Apply(double, Value.Apply(identity, natural(value))),
          ReadingState.fresh(limit, configuration).copy(storages = Some(option))
        )
      val plain = read(
        Value.Apply(double, Value.Apply(identity, plainNatural(value))),
        ReadingState.fresh(limit, configuration)
      )
      Result.all(
        List(
          Result.diff(calls, 0L)(_ == _).log("native calls"),
          Result
            .assert(JitTesting.sameOutcomes(forms, plain))
            .log("normal forms")
        )
      )
  }

  private def readIn(
      mode: Mode,
      value: Value[encoding.type],
      state: ReadingState[encoding.type]
  ): Bounded[Vector[Configured[encoding.type]]] =
    NormalForms.normalForms(mode, value).result(state) match
      case Computed.Done(normalForms, _) =>
        Bounded.Finished(normalForms.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering))
      case Computed.Stopped(after) => EvaluatorTesting.stopped(after)

  // The option holds in both modes: the untabled weak head reads a list of
  // storages as the plain list too.
  property(
    "under the untabled weak head, with the option, a list of storages reads the plain list's normal forms"
  ) {
    for items <- lists.forAll
    yield
      val withOption = readIn(
        Mode.WeakHead,
        headOf(listOf(items)),
        ReadingState.fresh(limit, configuration).copy(storages = Some(option))
      )
      val plain = readIn(
        Mode.WeakHead,
        headOf(plainListOf(items)),
        ReadingState.fresh(limit, configuration)
      )
      Result
        .assert(JitTesting.sameOutcomes(withOption, plain))
        .log(s"$withOption against $plain")
  }

  // Under HeadsMet with the option, a list of storages reads the plain list's
  // normal forms. Whether the heads met here hold a storage beside its own
  // criterion, the case the option keeps whole, is not shown by this law.
  property(
    "under HeadsMet, with the option, a list of storages reads the plain list's normal forms"
  ) {
    for items <- lists.forAll
    yield
      val state = ReadingState
        .fresh(limit, configuration)
        .copy(storages = Some(option), parallels = ParallelReading.HeadsMet)
      val withOption = read(headOf(listOf(items)), state)
      val plain = read(
        headOf(plainListOf(items)),
        ReadingState.fresh(limit, configuration)
      )
      Result
        .assert(JitTesting.sameOutcomes(withOption, plain))
        .log(s"$withOption against $plain")
  }
