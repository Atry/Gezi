package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.frontend.TermOf
import gezi.ir.{Configured, NoFacts}
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ParallelSetReading
import gezi.weakhead.ReadingState

/** Laws of the read-out by membership (`ParallelSetReading.Membership`, the
  * directed test of whether a head reads a normal form another head reads), on
  * generated Scott families, each a list of constructors with zero to two
  * recursive fields, the first with none, and the family's criterion
  * `fixpoint (λself. (K0 + K1 self … + …))`, a filter by an infinite type: (1)
  * a value of the family under its criterion reads, within the limit, exactly
  * the normal forms the value alone reads; (2) the parallel of two values
  * reads, by either read-out, the one normal form both values read when they
  * read the same, and none otherwise: each value alone reads one closed βη
  * normal form, its set of one head read with no test of membership, and two
  * distinct closed βη normal forms are separable, so their parallel has no
  * normal form.
  *
  * Purpose: catch a read-out that does not finish on a parallel filter by an
  * infinite type, or a membership test (`headReads`, which both read-outs use
  * on a set of several heads) that answers otherwise than the equality of the
  * two normal forms. The families are generated, so the laws hold of the
  * read-out and not of the library's types.
  */
class MembershipReadOutLawTest extends GeneratedProperties:

  /** The readings are of no facts: the terms are as written. */
  private given NoFacts.type = NoFacts

  /** A closed term of the library's configuration under no facts. */
  private type Program = TermOf[Configured[NoFacts.type]]

  /** The limit of a reading, the natives' tests' confirmation limit. */
  private val limit: Long = NativesTesting.confirmationLimit

  /** A family: the number of recursive fields of each constructor. */
  private final case class Family(constructors: Vector[Int]):

    private def constructorText(index: Int): String =
      val binders =
        (0 until constructors(index)).map(field => s"λf$field. ").mkString
      val cases =
        constructors.indices.map(alternative => s"λc$alternative. ").mkString
      val applied =
        (s"c$index" +: (0 until constructors(index)).map(field => s"f$field"))
          .mkString(" ")
      s"$binders$cases$applied"

    val constructorTerms: Vector[Program] =
      constructors.indices.toVector.map(index => closed(constructorText(index)))

    /** The criterion, with the fixed point combinator written out. */
    val criterion: Program =
      val members = constructors.indices.map(index =>
        (s"(${constructorText(index)})" +: Vector.fill(constructors(index))(
          "self"
        )).mkString(" ")
      )
      closed(
        s"((λx. λf. f (x x f)) (λx. λf. f (x x f))) (λself. (${members.mkString(" + ")}))"
      )

  private def closed(text: String): Program = Term.closed(
    Defunctionalization.thunkInstruction[NoFacts.type](Lambdalattice.term(text))
  )

  private val families: Gen[Family] =
    Gen
      .int(Range.linear(0, 2))
      .list(Range.linear(1, 2))
      .map(fields => Family(0 +: fields.toVector))

  /** A value of the family, at most the depth. */
  private def value(family: Family, depth: Int): Gen[Program] =
    val choices =
      if depth == 0 then Vector(0) else family.constructors.indices.toVector
    Gen
      .elementUnsafe(choices.toList)
      .flatMap(index =>
        (0 until family.constructors(index)).foldLeft(
          Gen.constant(family.constructorTerms(index))
        )((applied, _) =>
          applied.flatMap(function =>
            value(family, depth - 1).map(field => function(field))
          )
        )
      )

  private def read(
      parallelSetReading: ParallelSetReading,
      term: Program
  ): Option[Set[Configured[NoFacts.type]]] =
    NormalForms
      .normalForm(
        Mode.TablingWeakHead,
        parallelSetReading,
        JitTesting.termValue(term)
      )
      .collected
      .result(
        ReadingState
          .fresh(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(forms, _) => Some(forms.toSet)
      case Computed.Stopped(_)     => None

  /** One reading of each read-out before the laws, so that the reader's first
    * call, which took 2.4 s of the first sample while each later one took at
    * most 5 ms (measured 2026-11-22, two cores, load 5), is charged to the
    * fixture (FailFastSuite), not to a law.
    */
  private lazy val warmedUp: (
      Option[Set[Configured[NoFacts.type]]],
      Option[Set[Configured[NoFacts.type]]]
  ) =
    val family = Family(Vector(0, 1))
    (
      read(ParallelSetReading.Whole, family.constructorTerms(0)),
      read(
        ParallelSetReading.Membership,
        family.constructorTerms(0) ∥ family.criterion
      )
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => warmedUp)

  property(
    "a value under its family's criterion reads, by either read-out, what the value alone reads"
  ) {
    for
      family <- families.forAll
      depth <- Gen.int(Range.linear(0, 2)).forAll
      member <- value(family, depth).forAll
    yield
      val alone = read(ParallelSetReading.Whole, member)
      Result.all(
        List(
          Result
            .assert(alone.exists(_.nonEmpty))
            .log("the value alone reads a normal form within the limit"),
          Result
            .diff(
              read(ParallelSetReading.Membership, member ∥ family.criterion),
              alone
            )(_ == _)
            .log("the read-out by membership"),
          // Two distinct heads with one read in common: the whole read-out's test answers true here.
          Result
            .diff(
              read(ParallelSetReading.Whole, member ∥ family.criterion),
              alone
            )(_ == _)
            .log("the whole read-out")
        )
      )
  }

  property(
    "the parallel of two values reads the normal form they share, or none"
  ) {
    for
      first <- families.forAll
      second <- families.forAll
      left <- value(first, 2).forAll
      right <- value(second, 2).forAll
    yield
      val leftAlone = read(ParallelSetReading.Whole, left)
      val rightAlone = read(ParallelSetReading.Whole, right)
      val expected = if leftAlone == rightAlone then leftAlone
      else Some(Set.empty[Configured[NoFacts.type]])
      Result.all(
        List(
          Result
            .assert(
              leftAlone.exists(_.size == 1) && rightAlone.exists(_.size == 1)
            )
            .log("each value alone reads one normal form"),
          Result
            .diff(read(ParallelSetReading.Whole, left ∥ right), expected)(
              _ == _
            )
            .log("the whole read-out"),
          Result
            .diff(read(ParallelSetReading.Whole, right ∥ left), expected)(
              _ == _
            )
            .log("the whole read-out, the heads swapped"),
          Result
            .diff(read(ParallelSetReading.Membership, left ∥ right), expected)(
              _ == _
            )
            .log("the read-out by membership")
        )
      )
  }

  private def readIn(
      mode: Mode,
      term: Program,
      steps: Long
  ): Option[Set[Configured[NoFacts.type]]] =
    NormalForms
      .normalForm(mode, ParallelSetReading.Whole, JitTesting.termValue(term))
      .collected
      .result(
        ReadingState
          .fresh(steps, gezi.weakhead.ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(forms, _) => Some(forms.toSet)
      case Computed.Stopped(_)     => None

  private val identity: Term = Term.λ(x => x)

  /** The Church numeral of the count. */
  private def church(count: Int): Term = Term.λ(f =>
    Term.λ(x => (1 to count).foldLeft(x)((applied, _) => f(applied)))
  )

  /** `(λa b. a) ∥ (λz s. s nat_type)` has no normal form (a and s nat_type
    * differ at their head variable under two binders), and `(λa b. a) ∥
    * nat_type` has λa b. a, nat_type's zero; both readings end, though the
    * second head of each has a read for every natural.
    */
  test(
    "a later head with infinitely many reads beside a first with one is tested, not enumerated"
  ) {
    val first = Term.λ(a => Term.λ(_ => a))
    val nat = JitTesting.libraryTerm[NoFacts.type]("nat_type")
    assertEquals(
      read(ParallelSetReading.Whole, first ∥ Term.λ(_ => Term.λ(s => s(nat)))),
      Some(Set.empty[Configured[NoFacts.type]])
    )
    assertEquals(
      read(ParallelSetReading.Whole, first ∥ nat),
      read(ParallelSetReading.Whole, first)
    )
    // The same sets with their heads in the other order: the heads are tried in turn, so the order decides nothing.
    assertEquals(
      read(ParallelSetReading.Whole, Term.λ(_ => Term.λ(s => s(nat))) ∥ first),
      Some(Set.empty[Configured[NoFacts.type]])
    )
    assertEquals(
      read(ParallelSetReading.Whole, nat ∥ first),
      read(ParallelSetReading.Whole, first)
    )
  }

  /** The steps of the whole read-out of the term, with no limit in practice. */
  private def spent(term: Program): (Option[Int], Long) =
    NormalForms
      .normalForm(
        Mode.WeakHead,
        ParallelSetReading.Whole,
        JitTesting.termValue(term)
      )
      .collected
      .result(
        ReadingState
          .fresh(10000000, gezi.weakhead.ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(forms, after) => (Some(forms.size), after.budget.spent)
      case Computed.Stopped(after)     => (None, after.budget.spent)

  /** `(λx. x (a1 + … + an)) ∥ (λx. E x (a1 + … + an))`, the ai the Church
    * numerals 0 to n - 1 and E the Church numeral m applied to the identity
    * twice, which reduces to the identity in m steps, n = 50 and m = 1,000,
    * under the untabled weak head: the whole read-out reads the n normal forms
    * `λx. x ai` and spends at most two shares of 4,096 steps plus twice the
    * steps F of reading the first head alone plus the steps S of reading the
    * second alone. Derived: neither head ends within its share (F and S pass
    * 4,096), so both shares are given up, then the first head is read, F, its
    * reads expanded (its normal forms), at most F again, and the second head
    * descended once, at most S, each subterm evaluated once for the targets
    * alive there. Testing each target alone would evaluate the second head n
    * times.
    */
  test(
    "the whole read-out tests the first head's reads in one descent of the other"
  ) {
    val count = 50
    val members = Term.choice((0 until count).map(church)*)
    val first = Term.λ(x => x(members))
    val second = Term.λ(x => church(1000)(identity)(identity)(x)(members))
    val (firstForms, firstSteps) = spent(first)
    val (secondForms, secondSteps) = spent(second)
    val (bothForms, bothSteps) = spent(first ∥ second)
    assertEquals(
      (firstForms, secondForms, bothForms),
      (Some(count), Some(count), Some(count))
    )
    assert(
      firstSteps > 4096 && secondSteps > 4096,
      s"the heads alone take $firstSteps and $secondSteps steps"
    )
    assert(
      bothSteps <= 2 * 4096 + 2 * firstSteps + secondSteps,
      s"$bothSteps steps, the first head alone $firstSteps, the second $secondSteps"
    )
  }

  /** Sets nested d = 60 deep, `V0 = λa b. a`, `V(k+1) = (λz. z Vk) ∥ (λz. z T)`
    * with `T = Y (λt. λa b. a + λz. z t)`, which reads every chain
    * `λz. z (… (λa b. a))`: the exact reading of `V60` is its chain of depth
    * 60, which T reads, and the whole read-out ends within 1,000,000 steps
    * under the untabled weak head. Derived: each set costs at most its two
    * shares, 8,192 steps, more than reading its first head and descending its
    * second, and the shares of the nested sets add up (each set read in full
    * once), so about 60 · 8,192 + the steps of reading the chains, well within
    * the limit; shares retried from scratch at every level would multiply
    * instead, past it.
    */
  test("nested sets cost their shares once each, adding up") {
    val zero = Term.λ(a => Term.λ(_ => a))
    val fixed = Term.λ(f => Term.λ(x => f(x(x)))(Term.λ(x => f(x(x)))))
    val chains = fixed(Term.λ(t => Term.choice(zero, Term.λ(z => z(t)))))
    val nested = (1 to 60).foldLeft(zero)((inner, _) =>
      Term.λ(z => z(inner)) ∥ Term.λ(z => z(chains))
    )
    val chain = (1 to 60).foldLeft(zero)((inner, _) => Term.λ(z => z(inner)))
    assertEquals(
      readIn(Mode.WeakHead, nested, 1000000),
      readIn(Mode.WeakHead, chain, 1000000)
    )
  }
