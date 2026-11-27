package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.Closed
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.{Configured, Value}
import com.yang_bo.gezi.jit.JitTesting.{
  interned,
  parallelOfValues,
  storageOf,
  valueOfNative
}
import com.yang_bo.gezi.jit.JitTesting.libraryTerm
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.Values

/** The laws of group storages (`GroupStorage`), the term `(m1 + … + mk) ∥ T` of
  * storages of one representation in their canonical order, on generated
  * naturals, booleans and lists of the natives fixture.
  */
class GroupStorageLawTest extends GeneratedProperties:

  private lazy val library = NativesTesting.nativesOn
  private lazy val facts = BackendFacts.of(library)
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => JitTesting.criterionOf(encoding)(Representation.BigInteger))

  private def natural(
      value: BigInt
  ): RepresentedStorage[JitValue[encoding.type]] = storageOf(encoding)(
    Representation.BigInteger,
    NativeValue.Natural(value)
  ) match
    case storage => storage

  private def truth(
      value: Boolean
  ): RepresentedStorage[JitValue[encoding.type]] =
    storageOf(encoding)(Representation.Truth, NativeValue.Truth(value)) match
      case storage => storage

  private def node(
      storage: RepresentedStorage[JitValue[encoding.type]]
  ): JitValue[encoding.type] = interned(encoding)(storage)

  private def chain(
      members: Vector[RepresentedStorage[JitValue[encoding.type]]]
  ): JitValue[encoding.type] = JitValue.Choice(members.map(node))

  private lazy val criterionTerm: Configured[encoding.type] =
    Closed
      .configured(naturalCriterion)
      .getOrElse(
        throw IllegalStateException("the natural criterion is no term")
      )

  private lazy val naturalCriterion: JitValue[encoding.type] =
    JitTesting.criterionOf(encoding)(Representation.BigInteger)

  /** The law of the canonical order: on generated pairs of naturals and of
    * booleans, a storage precedes another exactly when its value is smaller (an
    * independent oracle: `BigInt` and `Boolean` comparison), never itself, and
    * never both ways; a natural and a boolean are not ordered. Its purpose is
    * to catch an order that disagrees with the values, is not antisymmetric, or
    * orders storages of two kinds.
    */
  property(
    "a storage precedes another exactly when its value is smaller, within one kind"
  ) {
    for
      first <- Gen.long(Range.linear(0L, 1000L)).forAll
      second <- Gen.long(Range.linear(0L, 1000L)).forAll
      firstTruth <- Gen.boolean.forAll
      secondTruth <- Gen.boolean.forAll
    yield
      val (a, b) = (natural(BigInt(first)), natural(BigInt(second)))
      val (p, q) = (truth(firstTruth), truth(secondTruth))
      Result
        .diff(a.precedes(b), first < second)(_ == _)
        .and(Result.assert(!(a.precedes(b) && b.precedes(a))))
        .and(Result.assert(!a.precedes(a)))
        .and(Result.diff(p.precedes(q), !firstTruth && secondTruth)(_ == _))
        .and(Result.assert(!a.precedes(p) && !p.precedes(a)))
  }

  /** Two names whose `String` hash codes are equal: the same number of blocks
    * "Aa" and "BB", which hash alike, in two generated arrangements, so that
    * nothing a `String` hash gives could order them.
    */
  private val collidingNames: Gen[(String, String)] =
    for
      blocks <- Gen.int(Range.linear(1, 6))
      first <- Gen.boolean.list(Range.singleton(blocks))
      second <- Gen.boolean.list(Range.singleton(blocks))
    yield
      def name(arrangement: List[Boolean]): String =
        arrangement.map(if _ then "Aa" else "BB").mkString
      (name(first), name(second))

  /** The law that two distinct general storages are ordered by their content,
    * never by a hash code: list cells over generated noinline names, whose
    * `String` hash codes are equal, come in the order of their names, exactly
    * one before the other, and the two in that order form a group. Derived
    * before the run from the canonical order
    * (`RepresentedStorage.canonicalOrder`, `com.yang_bo.gezi.ir.ContentComparison`): the
    * cells' constructor and criterion are one, so their items, opaque names,
    * decide. Its purpose is to catch an order that reads a hash code, an
    * identity that differs from one run to the next.
    */
  property(
    "two general storages are ordered by their content, and form a group in that order"
  ) {
    for (firstName, secondName) <- collidingNames.forAll
    yield
      if firstName == secondName then Result.success
      else
        val listRepresentation = Representation.ListOf(naturalCriterion)
        val nil = valueOfNative(encoding)(
          listRepresentation,
          NativeValue.Listed(
            com.yang_bo.gezi.weakhead.ListRepresentation.Items(0, Vector.empty)
          )
        )
        def cell(name: String): RepresentedStorage[JitValue[encoding.type]] =
          storageOf(encoding)(
            listRepresentation,
            NativeValue.Listed(
              com.yang_bo.gezi.weakhead.ListRepresentation
                .Cell(Value.of(encoding.opaque(name)), nil)
            )
          )
        val (earlier, later) = if firstName < secondName then
          (cell(firstName), cell(secondName))
        else (cell(secondName), cell(firstName))
        val converted = parallelOfValues(encoding)(
          chain(Vector(earlier, later)),
          JitTesting.criterionOf(encoding)(listRepresentation)
        )
        Result
          .assert(earlier.precedes(later) && !later.precedes(earlier))
          .log(s"$firstName and $secondName")
          .and(
            Result
              .assert((converted: AnyRef).isInstanceOf[GroupStorage[?]])
              .log(s"no group: $converted")
          )
  }

  /** The law of the conversion into a group: generated distinct naturals in
    * ascending order, written `(n1 + … + nk) ∥ nat` and converted
    * (`StorageEncoding.parallel`), give a group whose members are those
    * storages; its view's choice is the very chain written, which the group
    * holds; the same term converted twice is one object; the same members out
    * of order, with a repetition, or a member before a group, give the plain
    * parallel. Derived before the run from the conversion (a choice's storage
    * run, `Choice.storageRun`, decides in one step) and the hash code's fold.
    * Its purpose is to catch a group that forms from a choice that is not the
    * canonical one (one term, two storages), and a group whose hash code is not
    * its view's.
    */
  property(
    "a chain of storages in their canonical order filtered by their criterion converts to their group"
  ) {
    for values <- Gen
        .long(Range.linear(0L, 500L))
        .list(Range.linear(2, 6))
        .forAll
    yield
      val sorted =
        values.distinct.sorted.map(value => natural(BigInt(value))).toVector
      if sorted.size < 2 then Result.success
      else
        val written = chain(sorted)
        val converted = parallelOfValues(encoding)(written, naturalCriterion)
        val again = parallelOfValues(encoding)(chain(sorted), naturalCriterion)
        val grouped = (converted: AnyRef) match
          case group: GroupStorage[?] =>
            Result
              .diff(group.members, sorted)(_ == _)
              .and(
                Result
                  .assert(
                    encoding
                      .viewOf(group)(using com.yang_bo.gezi.ir.StorageAccess.granted())
                      .value
                      .asInstanceOf[AnyRef] eq written.asInstanceOf[AnyRef]
                  )
                  .log("the view's choice is not the chain written")
              )
              .and(
                Result
                  .assert(
                    group.chain.asInstanceOf[AnyRef] eq written
                      .asInstanceOf[AnyRef]
                  )
                  .log("the group holds another chain")
              )
          case other => Result.failure.log(s"no group: $other")
        val reversed =
          parallelOfValues(encoding)(chain(sorted.reverse), naturalCriterion)
        val repeated = parallelOfValues(encoding)(
          chain(sorted.head +: sorted),
          naturalCriterion
        )
        val memberBeforeGroup = parallelOfValues(encoding)(
          JitValue.Choice(Vector(node(sorted.head), converted)),
          naturalCriterion
        )
        grouped
          .and(Result.assert(converted eq again).log("one term, two objects"))
          .and(
            Result
              .assert(JitValue.Parallel.unapply(reversed).isDefined)
              .log(s"out of order: $reversed")
          )
          .and(
            Result
              .assert(JitValue.Parallel.unapply(repeated).isDefined)
              .log(s"repeated: $repeated")
          )
          .and(
            Result
              .assert(JitValue.Parallel.unapply(memberBeforeGroup).isDefined)
              .log(s"a member before a group: $memberBeforeGroup")
          )
  }

  /** The Scott numeral of the value over the library's zero and successor, no
    * filter and no storage in it.
    */
  private def numeral(value: Long): TermOf[Configured[encoding.type]] =
    (1L to value).foldLeft(libraryTerm[encoding.type]("zero"))((term, _) =>
      libraryTerm[encoding.type]("successor")(term)
    )

  /** The JIT under the converting construction
    * (`StorageConstruction.Converted`), its instance table on or off.
    */
  private def convertingJit(instanceTable: Boolean): Jit[encoding.type] =
    val plain = NativesTesting.configurationOf(encoding)
    Jit(
      JitConfiguration[encoding.type](
        encoding,
        plain.budget,
        plain.strategy,
        plain.backend,
        plain.dispatch,
        instanceTable,
        storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )

  /** The normal forms of the closed term under the mode, within the natives'
    * step limit.
    */
  private def normalForms(
      jit: Jit[encoding.type],
      term: TermOf[Configured[encoding.type]]
  ) =
    NativesTesting.normalFormsSpent(
      jit,
      JitTesting.termValue(term),
      NativesTesting.normalFormLimit
    )

  private def referenceNormalForms(term: TermOf[Configured[encoding.type]]) =
    NativesTesting.normalFormsSpent(
      Mode.TablingWeakHead,
      JitTesting.plainConfiguration(encoding),
      JitTesting.termValue(term),
      NativesTesting.normalFormLimit
    )

  /** The choice of the storages' nodes, as a closed term. */
  private def storagesChoice(
      members: Vector[RepresentedStorage[JitValue[encoding.type]]]
  ): TermOf[Configured[encoding.type]] =
    members
      .map(member =>
        Term.closed(
          Closed
            .configured(node(member))
            .getOrElse(
              throw IllegalStateException(s"a storage that is no term: $member")
            )
        )
      )
      .reduceRight(_ + _)

  property("a group reads as the choice of its members") {
    for
      values <- Gen.long(Range.linear(0L, 12L)).list(Range.linear(2, 4)).forAll
      ordered <- Gen.boolean.forAll
    yield
      val distinctValues = values.distinct.toVector
      if distinctValues.size < 2 then Result.success
      else
        val members = (if ordered then distinctValues.sorted
                       else distinctValues).map(value => natural(BigInt(value)))
        val sortedMembers =
          distinctValues.sorted.map(value => natural(BigInt(value)))
        val group =
          parallelOfValues(encoding)(chain(sortedMembers), naturalCriterion)
        val jit = Jit(NativesTesting.configurationOf(encoding))
        val heads = jit
          .representedHeads(group)
          .collected
          .result(
            com.yang_bo.gezi.weakhead.ReadingState
              .fresh(NativesTesting.normalFormLimit, jit.readingConfiguration)
          ) match
          case com.yang_bo.gezi.weakhead.Computed.Done(found, after) =>
            (found, JitTesting.counts(after.jitState).encodings)
          case com.yang_bo.gezi.weakhead.Computed.Stopped(_) => (Vector.empty, -1L)
        val program =
          Term.λ(x => x ∥ Term.closed(criterionTerm))(storagesChoice(members))
        val read = normalForms(convertingJit(instanceTable = false), program)
        val reference =
          referenceNormalForms(distinctValues.map(numeral).reduceRight(_ + _))
        Result
          .diff(heads, (sortedMembers.map(_.value), 0L))(_ == _)
          .and(
            Result
              .assert(reference.outcome.finished)
              .log("the reference did not finish")
          )
          .and(
            Result
              .assert(JitTesting.sameOutcomes(read.outcome, reference.outcome))
              .log(s"${read.outcome} against ${reference.outcome}")
          )
  }

  /** The law of a group held inside a value: under the conversion with the
    * instance table on, `(λx. (λz. λy. y z z) (x ∥ nat)) (n1 + … + nk)` puts
    * the group in the filling of a thunk, in a slot read twice (which the
    * instance table shares when reading it may cost more than its heads), and
    * the normal-form reader reads it back from the head `λy. y z z`. Derived
    * before the run: every answer is an answer of the same program over the
    * plain Scott numerals with no filter, which the tabling weak head reads (an
    * executor may lose answers, never add one), and each `λy. y n n`, both
    * occurrences reading the same member, is among the JIT's answers whether or
    * not the slot is shared. Its purpose is to catch a walk of the JIT's values
    * with no case for a group (a reading cost, a closedness walk, a walk for
    * decoding cases, the readback's encoding), which throws, skips the members
    * or adds an answer.
    */
  property(
    "a group in a filling read twice reads back as the choice of its members"
  ) {
    for values <- Gen.long(Range.linear(0L, 6L)).list(Range.linear(2, 3)).forAll
    yield
      val distinctValues = values.distinct.sorted.toVector
      if distinctValues.size < 2 then Result.success
      else
        val members = distinctValues.map(value => natural(BigInt(value)))
        def body(
            argument: TermOf[Configured[encoding.type]]
        ): TermOf[Configured[encoding.type]] =
          Term.λ(z => Term.λ(y => y(z)(z)))(argument)
        val program = Term
          .λ(x => body(x ∥ Term.closed(criterionTerm)))(storagesChoice(members))
        val read = normalForms(convertingJit(instanceTable = true), program)
        val reference = referenceNormalForms(
          Term.λ(x => body(x))(distinctValues.map(numeral).reduceRight(_ + _))
        )
        val diagonal = distinctValues.map(value =>
          referenceNormalForms(Term.λ(y => y(numeral(value))(numeral(value))))
        )
        (read.outcome, reference.outcome) match
          case (
                com.yang_bo.gezi.weakhead.Bounded.Finished(answers),
                com.yang_bo.gezi.weakhead.Bounded.Finished(expected)
              ) =>
            val diagonalAnswers = diagonal.flatMap(_.outcome match
              case com.yang_bo.gezi.weakhead.Bounded.Finished(found) => found
              case other                                 =>
                throw IllegalStateException(
                  s"a diagonal answer not read: $other"
                ))
            def holds(
                terms: Vector[Configured[encoding.type]],
                term: Configured[encoding.type]
            ): Boolean = terms.exists(Configured.same(_, term))
            Result
              .assert(answers.forall(holds(expected, _)))
              .log(
                s"an answer the reference does not read: ${answers.filterNot(holds(expected, _))}"
              )
              .and(
                Result
                  .assert(diagonalAnswers.forall(holds(answers, _)))
                  .log(
                    s"a diagonal answer missing: ${diagonalAnswers.filterNot(holds(answers, _))}"
                  )
              )
          case other => Result.failure.log(s"not finished: $other")
  }

  /** The law that a group's members are read without their views: a group of
    * generated naturals, converted from their chain and read for its heads by a
    * JIT whose capability reads native data only (`StorageAccess.dataOnly`), so
    * that a view read throws. Derived before the run: the conversion decides
    * from the chain's storage run and the first member's criterion, and the JIT
    * reads a group's members as their own heads (`JitValue.Grouped`), so no
    * view is read and the heads are the members' values in order. Its purpose
    * is to catch a conversion or a reading of a group that materializes a
    * member's view or the choice of the members.
    */
  property("a group's heads are read without its members' views") {
    for values <- Gen
        .long(Range.linear(0L, 1000L))
        .list(Range.linear(2, 6))
        .forAll
    yield
      val distinctValues = values.distinct.sorted.toVector
      if distinctValues.size < 2 then Result.success
      else
        val members = distinctValues.map(value => natural(BigInt(value)))
        val group = Value.Parallel(chain(members), naturalCriterion)
        val dataOnlyJit = Jit(
          JitConfiguration.of(
            encoding,
            instanceTable = false,
            com.yang_bo.gezi.ir.StorageAccess.dataOnly()
          )
        )
        val heads = dataOnlyJit
          .representedHeads(group)
          .collected
          .result(
            com.yang_bo.gezi.weakhead.ReadingState.fresh(
              NativesTesting.normalFormLimit,
              dataOnlyJit.readingConfiguration
            )
          ) match
          case com.yang_bo.gezi.weakhead.Computed.Done(found, _) => found
          case com.yang_bo.gezi.weakhead.Computed.Stopped(_)     => Vector.empty
        Result
          .assert(Value.closed(group).flatMap(StorageOf.group(_)).isDefined)
          .log(s"no group: $group")
          .and(
            Result.diff(
              heads,
              distinctValues.map(value => NativeValue.Natural(BigInt(value)))
            )(_ == _)
          )
  }
