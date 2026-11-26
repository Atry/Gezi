package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily
import gezi.contest.corpora.common.ProblemField

import gezi.frontend.Term
import gezi.frontend.Term.λ

/** `problems/respelled_cycles`: `W W I`, the shape and
  * the argument of each point read from `respelled_point/3`, the context
  * its second field, a template of one hole (`λhole. hole false false` or
  * `λhole. hole false hole`), and the arguments from the facts
  * `argument_term/3`.
  */
final class RespelledCycles(corpora: Corpora) extends HardFamily:

  import corpora.prelude.*

  private def file: ProblemFamily =corpora.contestRespelledCycles

  private def respelledPoints: Vector[(String, ProblemField, String)] =
    file.rows("respelled_point").map {
      case Vector(point, context, argument) => (ProblemData.text(point), context, ProblemData.text(argument))
      case fields => throw IllegalArgumentException(s"a respelled_point has ${fields.size} fields, not three")
    }

  /** The context of the point applied to `self`: the data writes it as a
    * template of one hole, whose body the data spells.
    */
  private def contextTerm(context: ProblemField, self: ProblemTerm): ProblemTerm = ProblemData.program(context, Vector(self))

  /** `shape(Context, Argument)`: `\p. \arg. C[p p Passed]`, the argument's
    * binder and its passed term from the fact `argument_term(Argument, Arg,
    * Passed)`.
    */
  private def shape(context: ProblemField, argument: String): ProblemTerm =
    λ(p => λ(binder =>
      contextTerm(context, p(p)(file.template("argument_term", Map(0 -> argument), Map(1 -> binder), 2)))))

  def respelled(context: ProblemField, argument: String): ProblemTerm =
    shape(context, argument)(shape(context, argument))(identity)

  def points: Map[String, () => ProblemTerm] =
    respelledPoints.map((point, context, argument) => point -> (() => respelled(context, argument))).toMap

  def intended: Vector[(String, Intended)] =
    respelledPoints.map(point => point._1 -> Intended(IntendedOutcome.Failed, IntendedValue.NoValue))

  def unreadFiniteHeads: Vector[(String, String)] = Vector.empty

  def cycles: Vector[(String, String, String)] =
    respelledPoints.map(point =>
      (point._1, "false_only",
        "M = W W I passes a new spelling of I every lap; its argument reduces back, so M =beta C[M] with C[true] ->> false"))

  def cycleClaims: Vector[CycleClaim] = Vector.empty

/** `problems/certificate_cycles`: the certificate
  * judgment over a cycle of Count members, the points' counts read from
  * `cycle_point/2`.
  */
final class CertificateCycles(corpora: Corpora, clauses: HardClauses) extends HardFamily:

  import corpora.prelude.*

  private def file: ProblemFamily =corpora.contestCertificateCycles

  private def cyclePoints: Vector[(String, Int)] =
    file.rows("cycle_point").map(arguments =>
      ProblemData.text(arguments(0)) -> ProblemData.small(arguments(1))
    )

  private def memberPassing(judgment: ProblemTerm, passed: ProblemTerm): ProblemTerm =
    clauses.objectTriple(trueValue)(λ(that => clauses.identityOf(judgment(that))(passed)))(falseValue)

  private def chainedMember(judgment: ProblemTerm, self: ProblemTerm, remaining: Int): ProblemTerm =
    (1 to remaining).foldLeft(self)((next, _) => memberPassing(judgment, next))

  private def cycleMemberGenerator(judgment: ProblemTerm, count: Int): ProblemTerm =
    λ(self => memberPassing(judgment, chainedMember(judgment, self, count - 1)))

  private def cycleMemberOf(judgment: ProblemTerm, count: Int): ProblemTerm =
    λ(left => cycleMemberGenerator(judgment, count)(left(left)))(
      λ(right => cycleMemberGenerator(judgment, count)(right(right))))

  private def cycleJudgmentGenerator(count: Int): ProblemTerm =
    λ(judge => λ(subject =>
      clauses.objectTag(subject)(
        clauses.objectBase(subject)(clauses.naturalCertificate)(
          judge(clauses.objectMethod(subject)(cycleMemberOf(judge, count)))))(
        judge(subject)(λ(_ => λ(second => second))))))

  private def cycleJudgment(count: Int): ProblemTerm =
    λ(left => cycleJudgmentGenerator(count)(left(left)))(λ(right => cycleJudgmentGenerator(count)(right(right))))

  def typingCycle(count: Int): ProblemTerm = λ(judge => judge(cycleMemberOf(judge, count)))(cycleJudgment(count))

  def points: Map[String, () => ProblemTerm] =
    cyclePoints.map((point, count) => point -> (() => typingCycle(count))).toMap

  def intended: Vector[(String, Intended)] =
    cyclePoints.map(point => point._1 -> Intended(IntendedOutcome.Head, IntendedValue.CertificateValue("natural")))

  def unreadFiniteHeads: Vector[(String, String)] = Vector.empty

  def cycles: Vector[(String, String, String)] =
    cyclePoints.map(point =>
      (point._1, "certificate_cycle",
        "J m0: the certificate is given back after the members' cycle; the stream one makes it J T, T of value bad"))

  def cycleClaims: Vector[CycleClaim] = CycleClaim.facts(file, true)

/** `problems/continuation_cycles`: `Y (\self. \true.
  * \false. Body)`, each body read from `continuation_body/5` and each class
  * from `continuation_class/2`.
  */
final class ContinuationCycles(corpora: Corpora) extends HardFamily:

  import corpora.prelude.*

  private def file: ProblemFamily =corpora.contestContinuationCycles

  private def classes: Vector[(String, String)] =
    file.rows("continuation_class").map(arguments =>
      ProblemData.text(arguments(0)) -> ProblemData.text(arguments(1))
    )

  def continuationPoint(point: String): ProblemTerm =
    fixpoint(λ(self => λ(trueVariable => λ(falseVariable =>
      file.template("continuation_body", Map(0 -> point),
        Map(1 -> self, 2 -> trueVariable, 3 -> falseVariable), 4)))))

  def points: Map[String, () => ProblemTerm] =
    classes.map((point, _) => point -> (() => continuationPoint(point))).toMap

  def intended: Vector[(String, Intended)] =
    classes.map(point => point._1 -> Intended(IntendedOutcome.Failed, IntendedValue.NoValue))

  def unreadFiniteHeads: Vector[(String, String)] = Vector.empty

  def cycles: Vector[(String, String, String)] =
    classes.map((point, cycleClass) =>
      (point, cycleClass,
        "M = Y G in continuation passing style: every lap calls M again in tail position with its continuations rebuilt, so M t f never reaches a head"))

  def cycleClaims: Vector[CycleClaim] = Vector.empty

/** `problems/easy_terms`: Omega, read from the fact
  * `omega/1`, in four contexts; the classes read from `easy_point/2`.
  */
final class EasyTerms(corpora: Corpora) extends HardFamily:

  import corpora.prelude.*

  private def file: ProblemFamily =corpora.contestEasyTerms

  private def easyPoints: Vector[(String, String)] =
    file.rows("easy_point").map(arguments =>
      ProblemData.text(arguments(0)) -> ProblemData.text(arguments(1))
    )

  private def omega: ProblemTerm = file.program("omega")

  def points: Map[String, () => ProblemTerm] = Map(
    "easy_second_first" -> (() => λ(p => λ(q => omega(q)(p)))),
    "easy_nested" -> (() => λ(p => λ(q => omega(omega(p)(q))(q)))),
    "easy_applied" -> (() => λ(p => λ(_ => omega(p)))),
    "easy_constant" -> (() => λ(_ => λ(_ => omega)))
  )

  def intended: Vector[(String, Intended)] =
    easyPoints.map(point => point._1 -> Intended(IntendedOutcome.Failed, IntendedValue.NoValue))

  def unreadFiniteHeads: Vector[(String, String)] = Vector.empty

  def cycles: Vector[(String, String, String)] =
    easyPoints.map((point, cycleClass) =>
      (point, cycleClass, "a test with no head; Jacopini: lambda beta plus Omega = N is consistent for every closed N"))

  def cycleClaims: Vector[CycleClaim] = CycleClaim.facts(file, true)

/** `problems/arithmetic_theorems`: the search for a
  * counterexample to a predicate of linear arithmetic, the points read from
  * `theorem_point/3`.
  */
final class ArithmeticTheorems(corpora: Corpora) extends HardFamily:

  import corpora.prelude.*

  private def file: ProblemFamily =corpora.contestArithmeticTheorems

  /** Point, predicate and outcome: the predicate the term of a natural's
    * property the row writes, importing what it uses off its scope,
    * the outcome a
    * constructor of problems/arithmetic_theorems/outcome
    * (`ArithmeticTheorems.outcome`).
    */
  private def theoremPoints: Vector[(String, ProblemField, ArithmeticTheorems.TheoremOutcome)] =
    file.rows("theorem_point").map(arguments =>
      (ProblemData.text(arguments(0)), arguments(1), ArithmeticTheorems.outcome(arguments(2)))
    )

  private def isTheorem(outcome: ArithmeticTheorems.TheoremOutcome): Boolean = outcome match
    case ArithmeticTheorems.TheoremOutcome.Theorem           => true
    case ArithmeticTheorems.TheoremOutcome.Counterexample(_) => false

  private val conjunction: ProblemTerm = λ(left => λ(right => left(right)(falseValue)))

  /** `Y (\self. \n. and (P n) (self (successor n))) zero`, P the predicate. */
  def search(predicate: ProblemField): ProblemTerm =
    val property = ProblemData.program(predicate, Vector.empty)
    fixpoint(λ(self => λ(n => conjunction(property(n))(self(successor(n))))))(zero)

  def points: Map[String, () => ProblemTerm] =
    theoremPoints.map((point, predicate, _) => point -> (() => search(predicate))).toMap

  def intended: Vector[(String, Intended)] =
    theoremPoints.filterNot(point => isTheorem(point._3)).map(point =>
      point._1 -> Intended(IntendedOutcome.Head, IntendedValue.BooleanValue(false))) ++
      theoremPoints.filter(point => isTheorem(point._3)).map(point =>
        point._1 -> Intended(IntendedOutcome.Failed, IntendedValue.NoValue))

  def unreadFiniteHeads: Vector[(String, String)] =
    theoremPoints.filterNot(point => isTheorem(point._3)).map(point =>
      point._1 -> "one lap per n below the least counterexample K, each P n reducing to true, then and false (...) reduces to false (module comment)")

  def cycles: Vector[(String, String, String)] =
    theoremPoints.filter(point => isTheorem(point._3)).map(point =>
      (point._1, "both_booleans", "a theorem of linear arithmetic: M reduces one lap per n for ever and has no head"))

  def cycleClaims: Vector[CycleClaim] = Vector.empty

object ArithmeticTheorems:

  /** The outcome of a point, the constructors of
    * problems/arithmetic_theorems/outcome in order: the predicate is a
    * theorem, or fails first at the counterexample.
    */
  enum TheoremOutcome:
    case Theorem
    case Counterexample(value: Int)

  /** The outcome a field writes, a constructor of
    * problems/arithmetic_theorems/outcome read by its position
    * (`ProblemData.alternative`).
    */
  def outcome(field: ProblemField): TheoremOutcome =
    ProblemData.alternative(field, ProblemData.caseCount[TheoremOutcome]) match
      case (0, Vector())      => TheoremOutcome.Theorem
      case (1, Vector(value)) => TheoremOutcome.Counterexample(ProblemData.small(value))
      case (position, fields) =>
        throw IllegalArgumentException(s"an outcome of contest_arithmetic_theorems at position $position has ${fields.size} fields")

/** `problems/infinite_members`: lemmas on infinite
  * members of a parametric stream type; the sizes read from `size/2`, the
  * points' answers and arguments from `infinite_point/4`.
  */
final class InfiniteMembers(corpora: Corpora) extends HardFamily:

  import corpora.prelude.*

  private def contest = corpora.contest

  private def file: ProblemFamily =corpora.contestInfiniteMembers

  private def size(name: String): Int =
    ProblemData.small(file.row("size", Map(0 -> name))(1))

  private def infinitePoints: Vector[(String, IntendedValue, String, String)] =
    file.rows("infinite_point").map(arguments =>
      (ProblemData.text(arguments(0)), IntendedValue.read(arguments(1)), ProblemData.text(arguments(2)),
        ProblemData.text(arguments(3)))
    )

  /** `element(Index)`: true at the multiples of 3. */
  private def element(index: Int): ProblemTerm = if index % 3 == 0 then trueValue else falseValue

  /** `periodic`: one fixpoint over a period of `size(period)` cells. */
  def periodic: ProblemTerm =
    fixpoint(λ(self => (0 until size("period")).foldRight[ProblemTerm](self)((index, rest) => cons(element(index))(rest))))

  /** `layers(Count, Stream)`. */
  def layers(count: Int, stream: ProblemTerm): ProblemTerm = (1 to count).foldLeft(stream)((inner, _) => map(identity)(inner))

  private def stack: ProblemTerm =
    fixpoint(λ(self => λ(count => λ(stream =>
      count(stream)(λ(predecessor => map(λ(x => x))(self(predecessor)(stream))))))))

  private def premiseFields(build: (ProblemTerm, ProblemTerm, ProblemTerm) => ProblemTerm): ProblemTerm =
    build(λ(_ => λ(_ => trueValue)), zero, zero)

  private def reproduce: ProblemTerm =
    λ(self => λ(_ => λ(_ => λ(_ => λ(consVariable =>
      premiseFields((head, tail, extra) => consVariable(head)(tail)(extra)(self(self))))))))

  private def premisePassingNonStream: ProblemTerm =
    λ(_ => λ(consVariable => premiseFields((head, tail, extra) => consVariable(head)(tail)(extra)(reproduce(reproduce)))))

  def points: Map[String, () => ProblemTerm] = Map(
    "infinite_stream_map_identity_layers" -> (() =>
      contest.streamNth(contest.numeral(size("index")))(layers(size("layers"), periodic))),
    "infinite_stream_map_identity_counted" -> (() =>
      contest.streamNth(contest.numeral(size("index") + 1))(stack(contest.numeral(size("layers")))(periodic))),
    "infinite_stream_map_identity_shifted" -> (() =>
      contest.streamNth(contest.numeral(size("index") - 1))(layers(size("layers"), periodic))),
    "infinite_stream_map_identity_non_stream_case" -> (() =>
      map(identity)(λ(_ => λ(c => c(zero)(zero)(zero))))(λ(_ => λ(_ => λ(_ => trueValue))))(
        λ(_ => λ(_ => λ(_ => falseValue))))),
    "infinite_stream_map_identity_non_stream_nth" -> (() =>
      contest.streamNth(zero)(map(identity)(λ(_ => λ(c => c(λ(g => g(trueValue)(falseValue)))(zero)(falseValue)))))),
    "infinite_stream_map_identity_premised_non_stream" -> (() =>
      contest.streamNth(zero)(map(λ(_ => falseValue))(premisePassingNonStream)))
  )

  def intended: Vector[(String, Intended)] =
    infinitePoints.map(point => point._1 -> Intended(IntendedOutcome.Head, point._2))

  def unreadFiniteHeads: Vector[(String, String)] = infinitePoints.map(point => point._1 -> point._4)

  def cycles: Vector[(String, String, String)] = Vector.empty

  def cycleClaims: Vector[CycleClaim] = Vector.empty

/** A hidden family whose points are traps with a finite head, each with its
  * value and argument: `problems/api_capture_traps`,
  * `problems/api_domain_traps` and `problems/leading_zero_traps`, whose
  * purpose is `inheritance`.
  */
abstract class FiniteHeadTraps extends HardFamily:

  /** Point, intended value and the argument of its finite head. */
  def traps: Vector[(String, IntendedValue, String)]

  def intended: Vector[(String, Intended)] = traps.map(trap => trap._1 -> Intended(IntendedOutcome.Head, trap._2))

  def unreadFiniteHeads: Vector[(String, String)] = traps.map(trap => trap._1 -> trap._3)

  def cycles: Vector[(String, String, String)] = Vector.empty

  def cycleClaims: Vector[CycleClaim] = Vector.empty

/** `problems/api_capture_traps`: a library function's
  * generator applied to itself a bounded number of times, and a times whose
  * plus is captured; the traps read from `capture_trap/3`.
  */
final class ApiCaptureTraps(corpora: Corpora) extends FiniteHeadTraps:

  import corpora.prelude.*

  private def arithmetic = corpora.mergeDynamic

  def traps: Vector[(String, IntendedValue, String)] =
    corpora.contestApiCaptureTraps.rows("capture_trap").map(arguments =>
      (ProblemData.text(arguments(0)), IntendedValue.read(arguments(1)), ProblemData.text(arguments(2)))
    )

  /** `bounded_self(Count)`: natural_equal's generator applied Count times
    * to `\a. \b. false`.
    */
  private def boundedSelf(count: Int): ProblemTerm =
    (1 to count).foldLeft(λ(_ => λ(_ => falseValue)))((previous, _) => naturalEqualBody(previous))

  private def naturalNumeral(count: Int): ProblemTerm = (1 to count).foldLeft(zero)((rest, _) => successor(rest))

  def equalSelfTerm(bound: Int, count: Int): ProblemTerm =
    if count <= bound then throw IllegalArgumentException(s"$count is not above $bound")
    else boundedSelf(bound)(naturalNumeral(count))(naturalNumeral(count))

  def timesPlusTerm(left: BigInt, right: BigInt): ProblemTerm =
    val times =
      λ(plus => λ(zeroVariable => arithmetic.timesFunction(plus, zeroVariable))(arithmetic.binary(0)))(
        λ(_ => λ(_ => arithmetic.binary(0))))
    times(arithmetic.binary(left))(arithmetic.binary(right))(trueValue)(λ(_ => falseValue))(λ(_ => falseValue))

  def points: Map[String, () => ProblemTerm] = Map(
    "hidden_capture_equal_self_three_five" -> (() => equalSelfTerm(3, 5)),
    "hidden_capture_equal_self_ten_twelve" -> (() => equalSelfTerm(10, 12)),
    "hidden_capture_times_plus_sixty_four_three" -> (() => timesPlusTerm(64, 3)),
    "hidden_capture_times_plus_one_thousand_twenty_four_five" -> (() => timesPlusTerm(1024, 5))
  )

/** `problems/api_domain_traps`: library functions
  * applied outside their domain; the traps read from `domain_trap/2`, all
  * intended false.
  */
final class ApiDomainTraps(corpora: Corpora) extends FiniteHeadTraps:

  import corpora.prelude.*

  private def arithmetic = corpora.mergeDynamic

  def traps: Vector[(String, IntendedValue, String)] =
    corpora.contestApiDomainTraps.rows("domain_trap").map(arguments =>
      (ProblemData.text(arguments(0)), IntendedValue.BooleanValue(false), ProblemData.text(arguments(1)))
    )

  private def impostor: ProblemTerm = λ(z => λ(s => s(z)))

  def points: Map[String, () => ProblemTerm] = Map(
    "hidden_api_natural_equal_impostor" -> (() => naturalEqual(successor(impostor))(successor(zero))),
    "hidden_api_natural_at_least_impostor" -> (() => naturalAtLeast(successor(zero))(successor(impostor))),
    "hidden_api_binary_equality_non_canonical" -> (() =>
      arithmetic.withArithmetic(names =>
        names.equality(arithmetic.binaryEven(arithmetic.binaryZero))(arithmetic.binaryZero))),
    "hidden_api_binary_plus_non_canonical" -> (() =>
      arithmetic.withArithmetic(names =>
        names.equality(names.plus(arithmetic.binaryEven(arithmetic.binaryZero))(arithmetic.binaryZero))(
          arithmetic.binaryZero)))
  )

/** `problems/leading_zero_traps`: binary numerals with
  * a leading zero against canonical ones; the traps read from
  * `leading_zero_point/3`.
  */
final class LeadingZeroTraps(corpora: Corpora) extends FiniteHeadTraps:

  import corpora.prelude.*

  private def arithmetic = corpora.mergeDynamic

  def traps: Vector[(String, IntendedValue, String)] =
    corpora.contestLeadingZeroTraps.rows("leading_zero_point").map(arguments =>
      (ProblemData.text(arguments(0)), IntendedValue.read(arguments(1)), ProblemData.text(arguments(2)))
    )

  /** `leading_zero(N)`: N in binary over `even zero` instead of zero. */
  def leadingZero(number: BigInt): ProblemTerm =
    if number == 0 then arithmetic.binaryEven(arithmetic.binaryZero)
    else if number % 2 == 0 then arithmetic.binaryEven(leadingZero(number / 2))
    else arithmetic.binaryOdd(leadingZero(number / 2))

  def equalTerm(number: BigInt): ProblemTerm =
    arithmetic.withArithmetic(names => names.equality(leadingZero(number))(arithmetic.binary(number)))

  def timesTerm(left: BigInt): ProblemTerm =
    arithmetic.withArithmetic(names =>
      λ(zeroVariable =>
        λ(times => names.equality(times(arithmetic.binary(left))(leadingZero(0)))(arithmetic.binary(0)))(
          arithmetic.timesFunction(names.plus, zeroVariable)))(arithmetic.binary(0)))

  def points: Map[String, () => ProblemTerm] = Map(
    "hidden_leading_zero_equal_one_thousand" -> (() => equalTerm(1000)),
    "hidden_leading_zero_equal_thirty_two_digits" -> (() => equalTerm(BigInt("12345678901234567890123456789012"))),
    "hidden_leading_zero_times_one_thousand_one" -> (() => timesTerm(1001)),
    "hidden_leading_zero_times_thirty_two_digits" -> (() => timesTerm(BigInt("98765432109876543210987654321097")))
  )

/** A tautology family: points whose term is a quantified circuit, a finite
  * head of purpose `hinted`.
  */
abstract class TautologyFamily(corpora: Corpora) extends HardFamily:

  /** Point, variable count, formula and intended boolean. */
  def circuits: Vector[(String, Int, Formula, Boolean)]

  /** The argument of the points' finite heads. */
  def argument: String

  def points: Map[String, () => ProblemTerm] =
    circuits.map((point, count, formula, _) => point -> (() => corpora.tautology.quantified(count, formula))).toMap

  def intended: Vector[(String, Intended)] =
    circuits.map(circuit => circuit._1 -> Intended(IntendedOutcome.Head, IntendedValue.BooleanValue(circuit._4)))

  def unreadFiniteHeads: Vector[(String, String)] = circuits.map(circuit => circuit._1 -> argument)

  def cycles: Vector[(String, String, String)] = Vector.empty

  def cycleClaims: Vector[CycleClaim] = Vector.empty

/** The family `contest_tautology_circuits`, its points and intended answers
  * built here with no table of its own: pigeonhole, parity and two circuits
  * false at one assignment.
  */
final class TautologyCircuits(corpora: Corpora) extends TautologyFamily(corpora):

  /** `pigeonhole(Pigeons, Holes)`. */
  def pigeonhole(pigeons: Int, holes: Int): Formula =
    val placements = (1 to pigeons).toVector.map(pigeon =>
      Formula.folded(Formula.Or(_, _), (1 to holes).toVector.map(hole => Formula.Variable((pigeon - 1) * holes + hole))))
    val exclusions =
      for
        hole <- (1 to holes).toVector
        pigeon <- (1 to pigeons).toVector
        other <- (1 to pigeons).toVector
        if pigeon < other
      yield Formula.Not(Formula.And(
        Formula.Variable((pigeon - 1) * holes + hole), Formula.Variable((other - 1) * holes + hole)))
    Formula.Not(Formula.And(Formula.folded(Formula.And(_, _), placements), Formula.folded(Formula.And(_, _), exclusions)))

  /** `parity(Count)`. */
  def parity(count: Int): Formula =
    val variables = Formula.variables(1, count)
    Formula.Not(Formula.Exclusive(
      Formula.folded(Formula.Exclusive(_, _), variables), Formula.folded(Formula.Exclusive(_, _), variables.reverse)))

  /** `differs_from_alternation(Index)`. */
  def differsFromAlternation(index: Int): Formula =
    if index % 2 == 1 then Formula.Not(Formula.Variable(index)) else Formula.Variable(index)

  def circuits: Vector[(String, Int, Formula, Boolean)] = Vector(
    ("hidden_pigeonhole_4_3", 12, pigeonhole(4, 3), true),
    ("hidden_parity_12", 12, parity(12), true),
    ("hidden_parity_16", 16, parity(16), true),
    ("hidden_last_false_14", 14, Formula.folded(Formula.Or(_, _), Formula.variables(1, 14)), false),
    ("hidden_middle_false_14", 14, Formula.folded(Formula.Or(_, _), (1 to 14).map(differsFromAlternation)), false)
  )

  def argument: String =
    "the term reduces by beta to the conjunction of the circuit's values over every assignment, each true or false by the connectives' definitions; the setter evaluated the circuit at every assignment (module comment)"

/** `problems/adder_tautologies`: ripple-carry adders;
  * the points' answers read from `adder_point/2`.
  */
final class AdderTautologies(corpora: Corpora) extends TautologyFamily(corpora):

  /** `sum_bits(Width, Left, Right)`: the sum bits of the two numbers. */
  def sumBits(width: Int, left: Vector[Formula], right: Vector[Formula]): Vector[Formula] =
    (0 until width).foldLeft((Vector.empty[Formula], Option.empty[Formula]))((state, index) =>
      val (bits, carry) = state
      val a = left(index)
      val b = right(index)
      val exclusive = Formula.Exclusive(a, b)
      carry match
        case None => (bits :+ exclusive, Some(Formula.And(a, b)))
        case Some(carried) =>
          (bits :+ Formula.Exclusive(exclusive, carried),
            Some(Formula.Or(Formula.And(a, b), Formula.And(carried, exclusive))))
    )._1

  /** `commutes(Width)`. */
  def commutes(width: Int): Formula =
    val a = Formula.variables(1, width)
    val b = Formula.variables(width + 1, 2 * width)
    Formula.folded(
      Formula.And(_, _),
      sumBits(width, a, b).zip(sumBits(width, b, a)).map((forward, backward) =>
        Formula.Not(Formula.Exclusive(forward, backward)))
    )

  private def answers: Map[String, Boolean] =
    corpora.contestAdderTautologies
      .rows("adder_point")
      .map(arguments =>
        ProblemData.text(arguments(0)) -> (Template.read(arguments(1)) match
          case Template.BooleanTemplate(value) => value
          case other => throw IllegalArgumentException(s"adder_point: ${other.written}")
        )
      )
      .toMap

  def circuits: Vector[(String, Int, Formula, Boolean)] = Vector(
    ("hidden_adder_commutes_6", 12, commutes(6), answers("hidden_adder_commutes_6")),
    ("hidden_adder_commutes_8", 16, commutes(8), answers("hidden_adder_commutes_8")),
    ("hidden_adder_commutes_unless_zero_8", 16,
      Formula.And(commutes(8), Formula.folded(Formula.Or(_, _), Formula.variables(1, 16))),
      answers("hidden_adder_commutes_unless_zero_8"))
  )

  def argument: String =
    "the term reduces by beta to the conjunction of the circuit's values over every assignment; the setter evaluated the circuit at every assignment (module comment)"
