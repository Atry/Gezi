package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Mode

/** The law of a decode point that a context consumes: a numeral x written with
  * the three constructors, canonical or not, under `binary_set p` for either p,
  * applied to three cases that ignore their fields and give one value v,
  * `(x ∥ binary_set p) v (λ_. v) (λ_. v)`, reads the one normal form v under
  * the JIT, whether or not x is in the set.
  *
  * The expectation follows from the β rule and the λ-lattice laws:
  * `binary_set p` is `A + B + p (λz e o. z) top` with `A = λz e o. o S`,
  * `B = λz e o. e S'` (corpora/library/binary/natural.lambdalattice), so
  * applied to the cases it is `v + v + (v or top)`, which is v up to ≃_O (`top`
  * is the top of ⊑_O, `top + M ≃_O M`); x applied to the cases is v, whichever
  * constructor it is; and a parallel applied is the parallel of the
  * applications, `v ∥ v = v`.
  *
  * Its purpose is to catch a decode point that reads a member its criterion
  * excludes (zero under the positive naturals, a non-canonical numeral) as no
  * head, which loses the answer of every context that consumes the parallel
  * without reading the member's fields.
  */
class ConsumedDecodePointLawTest extends GeneratedProperties:

  /** The library of native_types, prolog_backend and binary_prolog_backend, the
    * one field of tests/library_fixtures/binary_natural_backend.lambdalattice,
    * checked by the backend (as `BinaryNaturalDecodingLawTest` compiles it).
    */
  private lazy val library =
    LibraryFiles.compiled(
      "tests/library_fixtures/binary_natural_backend.lambdalattice",
      Vector(BackendChecks)
    )

  /** The encoding of the library's facts, whose singleton type is the
    * configuration of this library's terms.
    */
  private lazy val encoding: StorageEncoding =
    NativesTesting.encodingOf(library)

  private given encoding.type = encoding

  /** The encoding of the natives' library, the configuration of the native and
    * list tests.
    */
  private lazy val nativesEncoding: StorageEncoding =
    NativesTesting.nativesOnEncoding

  private given nativesEncoding.type = nativesEncoding

  /** A closed term of this library's configuration. */
  private type Program = TermOf[Configured[encoding.type]]

  /** A closed term of the natives' library's configuration. */
  private type NativesProgram = TermOf[Configured[nativesEncoding.type]]

  /** The JIT's configuration of the library's facts, one for every input: the
    * facts are a function of the library.
    */
  private lazy val configuration = NativesTesting.configurationOf(encoding)

  /** The library, its configuration and the library terms the numerals are
    * built from, forced before the first test and not charged to it
    * (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => configuration,
      _ => JitTesting.libraryTerms,
      _ => NativesTesting.nativesOn
    )

  private def name(key: String): Program =
    JitTesting.libraryTerm[encoding.type](key)

  /** A numeral of at most the depth, each of the three constructors drawn
    * uniformly at every size.
    */
  private def numeral(depth: Int): Gen[Program] =
    if depth == 0 then Gen.constant(name("binary_zero"))
    else
      Gen.int(Range.constant(0, 2)).flatMap {
        case 0 => Gen.constant(name("binary_zero"))
        case 1 => numeral(depth - 1).map(name("binary_even")(_))
        case _ => numeral(depth - 1).map(name("binary_odd")(_))
      }

  property(
    "a numeral under binary_set, consumed by cases that ignore their fields and give v, reads v"
  ) {
    for
      written <- Gen.int(Range.linear(0, 6)).flatMap(numeral).forAll
      canonical <- Gen.boolean.forAll
      truth <- Gen.boolean.forAll
    yield
      val value = name(if truth then "true" else "false")
      val filtered = written ∥ name("binary_set")(name(if canonical then "true"
      else "false"))
      val consumed = filtered(value)(Term.λ(_ => value))(Term.λ(_ => value))
      val jit = NativesTesting.normalFormsSpent(
        Jit(configuration),
        JitTesting.termValue(consumed),
        NativesTesting.normalFormLimit
      )
      val expected = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        JitTesting.termValue(value),
        NativesTesting.normalFormLimit
      )
      val reference = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        JitTesting.termValue(consumed),
        20000
      )
      Result.all(
        List(
          Result
            .assert(JitTesting.sameOutcomes(jit.outcome, expected.outcome))
            .log(s"the JIT's reading: ${jit.outcome}"),
          Result
            .assert(
              JitTesting.sameOutcomes(reference.outcome, expected.outcome)
            )
            .log(s"tabling(weak_head)'s reading: ${reference.outcome}")
        )
      )
  }

  /** A constructor whose field is itself filtered, under binary_set p and
    * consumed by cases that ignore their fields and give v:
    * `(C (x ∥ binary_set q) ∥ binary_set p) v (λ_. v) (λ_. v)` for C even or
    * odd and x any numeral, which is v by the β rule and the λ-lattice laws as
    * above: C applied to the cases picks one and ignores its field, and
    * binary_set p applied to them is v up to ≃_O. Its purpose is to catch a
    * decode point that reads such a member through the natives
    * (`listOrDataDecodePointHeads`, a type-filtered constructor) and drops it
    * when its field cannot be decoded.
    */
  property(
    "a constructor over a filtered field, under binary_set and consumed by cases that give v, reads v"
  ) {
    for
      written <- Gen.int(Range.linear(0, 4)).flatMap(numeral).forAll
      even <- Gen.boolean.forAll
      inner <- Gen.boolean.forAll
      outer <- Gen.boolean.forAll
      truth <- Gen.boolean.forAll
    yield
      val value = name(if truth then "true" else "false")
      def set(canonical: Boolean): Program =
        name("binary_set")(name(if canonical then "true" else "false"))
      val constructed =
        name(if even then "binary_even" else "binary_odd")(written ∥ set(inner))
      val consumed = (constructed ∥ set(outer))(value)(Term.λ(_ => value))(
        Term.λ(_ => value)
      )
      val jit = NativesTesting.normalFormsSpent(
        Jit(configuration),
        JitTesting.termValue(consumed),
        NativesTesting.normalFormLimit
      )
      val expected = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        JitTesting.termValue(value),
        NativesTesting.normalFormLimit
      )
      Result
        .assert(JitTesting.sameOutcomes(jit.outcome, expected.outcome))
        .log(s"the JIT's reading: ${jit.outcome}")
  }

  /** A field whose one head decodes to two values, used twice by a context:
    * `(binary_odd h ∥ N) w (λ_. w) (λy. D y y)`, N = `binary_set true`, h
    * either the one abstraction `λz e o. z + o binary_zero` or the choice
    * `binary_zero + binary_odd binary_zero` (both zero + one), written alone or
    * filtered `h ∥ N` (≃ h, both its members being in N), v and w true and
    * false in either order, and
    * `D = λp q. (p v (λ_. w) (λ_. w)) ∥ (q w (λ_. w) (λ_. v))`. By the β rule
    * and the λ-lattice laws the value's odd case gives
    * `D h h = (v + w) ∥ (w + v) = v + w`, and N applied to the cases gives
    * `D S S + w + w = v + w` (its odd field set S holds zero and odd numerals),
    * so the program is `(v + w) ∥ (v + w)`, whose normal forms are v and w. Its
    * purpose is to catch a decode point that reads the member as the choice of
    * two storages, `odd 0 + odd 1`, below it in ⊑_O, which reads
    * `D 0 0 ∥ … + D 1 1 ∥ …`, none (`D 0 0 = v ∥ w`).
    */
  test(
    "a field that decodes to two values, used twice by a context, keeps the answers"
  ) {
    for
      abstraction <- Vector(true, false); filtered <- Vector(false, true);
      truth <- Vector(true, false)
    do
      val v = name(if truth then "true" else "false")
      val w = name(if truth then "false" else "true")
      val written =
        if abstraction then
          Term.λ(z =>
            Term.λ(_ => Term.λ(o => Term.choice(z, o(name("binary_zero")))))
          )
        else
          Term.choice(
            name("binary_zero"),
            name("binary_odd")(name("binary_zero"))
          )
      val field =
        if filtered then written ∥ name("binary_set")(name("true")) else written
      val twice = Term.λ(p =>
        Term.λ(q =>
          p(v)(Term.λ(_ => w))(Term.λ(_ => w)) ∥ q(w)(Term.λ(_ => w))(
            Term.λ(_ => v)
          )
        )
      )
      val consumed =
        (name("binary_odd")(field) ∥ name("binary_set")(name("true")))(w)(
          Term.λ(_ => w)
        )(Term.λ(y => twice(y)(y)))
      val jit = NativesTesting.normalFormsSpent(
        Jit(configuration),
        JitTesting.termValue(consumed),
        200000
      )
      val expected = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        JitTesting.termValue(Term.choice(v, w)),
        NativesTesting.normalFormLimit
      )
      assert(
        JitTesting.sameOutcomes(jit.outcome, expected.outcome),
        s"the field ${
            if abstraction then "λz e o. z + o zero" else "zero + one"
          }${if filtered then " ∥ N" else ""}, v $truth"
      )
  }

  /** The natives' library, whose `boolean_not` is a native over the booleans.
    */
  private lazy val nativeEvaluator = Jit(
    NativesTesting.configurationOf(nativesEncoding)
  )

  /** A native's argument with a member the criterion excludes:
    * `boolean_not (a ∥ boolean_type) v v`, a either `x = λa b c d. c`, no
    * boolean, or the choice of x with a boolean m. By the β rule `boolean_not
    * b` is `b false true`, so x's member gives `(x false true v v) ∥ ((false +
    * true) v v)` = `v ∥ v` = v, and m's gives v; the expectation is
    *   v. Its purpose is to catch a native that runs on the members it decodes
    *      and drops the others, where its define reads them.
    */
  property(
    "a native whose argument has a member the criterion excludes, consumed by cases that give v, reads v"
  ) {
    for
      chosen <- Gen.boolean.forAll
      member <- Gen.boolean.forAll
      truth <- Gen.boolean.forAll
    yield
      val value =
        JitTesting.libraryTerm[nativesEncoding.type](if truth then "true"
        else "false")
      val excluded: NativesProgram =
        Term.λ(_ => Term.λ(_ => Term.λ(c => Term.λ(_ => c))))
      val argument = if chosen then
        Term.choice(
          JitTesting.libraryTerm[nativesEncoding.type](if member then "true"
          else "false"),
          excluded
        )
      else excluded
      val consumed = JitTesting.libraryTerm[nativesEncoding.type](
        "boolean_not"
      )(
        argument ∥ JitTesting.libraryTerm[nativesEncoding.type]("boolean_type")
      )(value)(value)
      val jit = NativesTesting.normalFormsSpent(
        nativeEvaluator,
        JitTesting.termValue(consumed),
        20000
      )
      val expected = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(nativesEncoding),
        JitTesting.termValue(value),
        NativesTesting.normalFormLimit
      )
      Result
        .assert(JitTesting.sameOutcomes(jit.outcome, expected.outcome))
        .log(s"the JIT's reading: ${jit.outcome}")
  }

  /** A filtered field whose excluded member sits beside a member the natives
    * read: `(binary_even ((zero + one) ∥ binary_set false) ∥ binary_set true) a
    * (λh. h v (λ_. v) (λ_. w)) (λ_. a)`, one being `binary_odd zero`, a the
    * identity, v and w true and false. By the β rule the value takes its even
    * case, which reads the field: one gives w, and the excluded zero gives
    * `v ∥ (w + v + top)` (binary_set false applied to the field's cases), whose
    * normal form is v; binary_set true applied to the outer cases gives
    * `a + a + (w + v + top)`, so the normal forms are v and w, which
    * tabling(weak_head) reads too. The JIT reads with its instance table, as
    * the reference tables: untabled, the parallel the decode point gives for
    * the member is read past the limit. Its purpose is to catch a native run on
    * the members it decodes that drops the one it cannot, whose answer a
    * consumer can still read.
    */
  test(
    "a filtered field's excluded member beside a member the natives read keeps its answer"
  ) {
    val a = Term.λ(x => x)
    val v = name("true")
    val w = name("false")
    val field = Term.choice(
      name("binary_zero"),
      name("binary_odd")(name("binary_zero"))
    ) ∥ name("binary_set")(name("false"))
    val consumer = Term.λ(h => h(v)(Term.λ(_ => v))(Term.λ(_ => w)))
    val consumed =
      (name("binary_even")(field) ∥ name("binary_set")(name("true")))(a)(
        consumer
      )(Term.λ(_ => a))
    val tabled = JitConfiguration[encoding.type](
      encoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
    )
    def answers(
        outcome: Bounded[Vector[Configured[encoding.type]]]
    ): Option[Set[Configured[encoding.type]]] = outcome match
      case Bounded.Finished(found) => Some(found.toSet)
      case _                       => None
    val jit = NativesTesting.normalFormsSpent(
      Jit(tabled),
      JitTesting.termValue(consumed),
      20000
    )
    val expected = NativesTesting.normalFormsSpent(
      Mode.TablingWeakHead,
      JitTesting.plainConfiguration(encoding),
      JitTesting.termValue(Term.choice(v, w)),
      NativesTesting.normalFormLimit
    )
    assertEquals(answers(jit.outcome), answers(expected.outcome))
  }

  /** The natives' library, whose list type has a decode point. */
  private lazy val listEvaluator = Jit(
    JitConfiguration[nativesEncoding.type](
      nativesEncoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
    )
  )

  /** A list member whose two sides are cells in the unique spelling that differ
    * as JIT values and are β-equal, read for its own normal forms with nothing
    * applied: `(c ∥ c') ∥ L`, L = `list_type nat_type`, c =
    * `cons (n ∥ nat_type) (nil ∥ L) ∥ L` and c' the same with `I n` for n, n a
    * generated natural and I the identity. By the β rule c' is c, ∥ is
    * idempotent, and n is a natural and nil a list, so the member reads the
    * normal form of `cons n nil`. Each side is a cell of the list's shapes,
    * their items kept unread, so the two read apart, and the sides-apart rule
    * alone decides the reading; its purpose is to catch a decode point that
    * refutes a member whose sides read apart, which reads no head for it.
    */
  property(
    "a list member whose sides read apart but are β-equal reads its normal form"
  ) {
    for count <- Gen.int(Range.linear(0, 4)).forAll
    yield
      val natural = (1 to count).foldLeft(
        JitTesting.libraryTerm[nativesEncoding.type]("zero")
      )((inner, _) =>
        JitTesting.libraryTerm[nativesEncoding.type]("successor")(inner)
      )
      val cons = JitTesting.libraryTerm[nativesEncoding.type]("cons")
      val nil = JitTesting.libraryTerm[nativesEncoding.type]("nil")
      val naturals = JitTesting.libraryTerm[nativesEncoding.type]("nat_type")
      val listType =
        JitTesting.libraryTerm[nativesEncoding.type]("list_type")(naturals)
      def cell(item: NativesProgram): NativesProgram =
        cons(item ∥ naturals)(nil ∥ listType) ∥ listType
      val member = (cell(natural) ∥ cell(Term.λ(x => x)(natural))) ∥ listType
      val jit = NativesTesting.normalFormsSpent(
        listEvaluator,
        JitTesting.termValue(member),
        20000
      )
      val expected = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(nativesEncoding),
        JitTesting.termValue(cons(natural)(nil)),
        NativesTesting.normalFormLimit
      )
      Result
        .assert(JitTesting.sameOutcomes(jit.outcome, expected.outcome))
        .log(s"the JIT's reading: ${jit.outcome}")
  }

  /** A list cell under `list_type nat_type` consumed by cases that agree on a
    * field of the cell, for v the identity or `λa b. a`:
    * `(cons v nil ∥ list_type nat_type) v (λa b. a)`, whose cell gives v and
    * whose type gives `nat_type + v` by the β rule, so the term is
    * `(v ∥ nat_type) + v` (the parallel applied is the parallel of the
    * applications, which distributes over the choice); and
    * `(cons v v ∥ list_type nat_type) v (λh t. t)`, whose cell gives its tail v
    * and whose type gives `L + v`, so the term is `(v ∥ L) + v`. Each has the
    * normal form v, and v ∥ nat_type and v ∥ L have none that is not v (v is
    * separable from every other shape), so each reads exactly v's own normal
    * form. A decode point that reads the cell as
    * `cons (v ∥ nat_type) (nil ∥ L)` drops the meeting with the type's nil case
    * and reads none. The JIT reads with its instance table (`listEvaluator`);
    * it was not checked without one.
    */
  property(
    "a list cell under list_type, consumed by cases that agree on one of its fields, reads that field"
  ) {
    for
      identity <- Gen.boolean.forAll
      tail <- Gen.boolean.forAll
    yield
      val value: NativesProgram =
        if identity then Term.λ(x => x) else Term.λ(a => Term.λ(_ => a))
      val listType = JitTesting.libraryTerm[nativesEncoding.type]("list_type")(
        JitTesting.libraryTerm[nativesEncoding.type]("nat_type")
      )
      val cons = JitTesting.libraryTerm[nativesEncoding.type]("cons")
      val consumed =
        if tail then
          (cons(value)(value) ∥ listType)(value)(
            Term.λ(_ => Term.λ(rest => rest))
          )
        else
          (cons(value)(
            JitTesting.libraryTerm[nativesEncoding.type]("nil")
          ) ∥ listType)(value)(Term.λ(a => Term.λ(_ => a)))
      val jit = NativesTesting.normalFormsSpent(
        listEvaluator,
        JitTesting.termValue(consumed),
        20000
      )
      val expected = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(nativesEncoding),
        JitTesting.termValue(value),
        NativesTesting.normalFormLimit
      )
      Result
        .assert(JitTesting.sameOutcomes(jit.outcome, expected.outcome))
        .log(s"the JIT's reading: ${jit.outcome}")
  }
