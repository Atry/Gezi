package gezi.contest.corpora.oldcorpora

/** A formula of the circuit grammar of the rewriting framework
  * as
  * `attractor_reference/3` reads the argument of `every_assignment`:
  * `binder(Formula)`, `bound(Index)` the de Bruijn index of an enclosing
  * binder (0 the innermost), and `node(Name, Children)` for the entries
  * `true`, `false`, `not`, `and`, `or`, `exclusive` and `every_assignment`,
  * whose one child is again a binder.
  */
enum QuantifiedFormula:

  /** `binder(Body)`: a function of one Boolean. */
  case Binder(body: QuantifiedFormula)

  /** `bound(Index)`: the variable of the binder `index` binders out. */
  case Bound(index: Int)

  /** `node(Name, Children)`: an entry of the library applied. */
  case Node(name: String, children: Vector[QuantifiedFormula])

/** A value a native reference reads or writes: a natural number, a Boolean,
  * a list of values, or the argument of `every_assignment`, a binder of the
  * circuit grammar.
  */
enum ReferenceValue:

  /** A natural number, unary or binary in the term. */
  case Natural(value: BigInt)

  /** A Boolean, `true` or `false`. */
  case Truth(value: Boolean)

  /** A list, its elements in order. */
  case Elements(values: Vector[ReferenceValue])

  /** A function of one Boolean, read by the circuit grammar. */
  case Quantified(binder: QuantifiedFormula.Binder)

/** The native references of the attractor library, the port of
  * `gezi/prolog/gezi/old_corpora/attractor_references.pl`: the
  * reference computation of each attractor of `problems/attractors`
  * that has a native implementation, on the numbers, Booleans and lists its
  * canonical arguments stand for.
  *
  * A native reference is an encoding of values, so it is no part of the
  * library's API declarations: it
  * is a reference implementation of the old corpora, kept for their tests
  * only, as `BetaEtaNormalisation` is. The
  * test `ContestAttractorsStandardLibraryTest` checks each reference against
  * its definition's normal form.
  */
object AttractorReferences:

  import ReferenceValue.*

  /** `attractor_reference(Name, Arguments, Result)`: the reference
    * computation of a function with a native implementation, on the values
    * its canonical arguments stand for; none for a function with none, and
    * for `every_assignment` whose formula has an index past the argument's
    * own binders, which reads nothing (the Prolog fails in both cases).
    * Throws `IllegalArgumentException` for arguments of another shape than
    * the function's, where the Prolog failed silently.
    */
  def attractorReference(name: String, arguments: Vector[ReferenceValue]): Option[ReferenceValue] =
    (name, arguments) match
      case ("merge_binary_increment", Vector(Natural(number)))          => Some(Natural(number + 1))
      case ("merge_binary_plus", Vector(Natural(left), Natural(right))) => Some(Natural(left + right))
      case ("merge_binary_times", Vector(Natural(left), Natural(right))) => Some(Natural(left * right))
      case ("merge_binary_equality", Vector(Natural(left), Natural(right))) => Some(Truth(left == right))
      case ("natural_equal", Vector(Natural(left), Natural(right)))     => Some(Truth(left == right))
      case ("natural_double", Vector(Natural(number)))                  => Some(Natural(2 * number))
      case ("natural_at_least", Vector(Natural(left), Natural(right)))  => Some(Truth(left >= right))
      // natural_difference m n is the truncated difference: n = 0 gives m,
      // m = 0 gives 0, and otherwise the difference of the predecessors
      // (prelude's definition), so by induction on n it is max(m - n, 0).
      case ("natural_difference", Vector(Natural(left), Natural(right))) => Some(Natural((left - right).max(0)))
      // The list functions, their lists given as lists of values.
      case ("length", Vector(Elements(values))) => Some(Natural(values.size))
      // binary_to_unary: a BinNat, least significant bit first, bit + 2 * rest.
      case ("binary_to_unary", Vector(Elements(values))) => Some(Natural(bitsValue(bits(values))))
      // binary_increment: a one bit carries, a zero bit stops the carry, and
      // the empty list is one, as the prelude's recursion does bit by bit (a
      // trailing zero bit is kept).
      case ("binary_increment", Vector(Elements(values))) => Some(truths(bitsIncremented(bits(values))))
      // unary_to_binary: n increments of the empty list, the bits of n least
      // significant first with no trailing zero.
      case ("unary_to_binary", Vector(Natural(number))) => Some(truths(numberBits(number)))
      case ("bit_set_member", Vector(Elements(set), Natural(index))) =>
        Some(if index < set.size then set(index.toInt) else Truth(false))
      case ("bit_set_insert", Vector(Elements(set), Natural(index))) =>
        Some(Elements(if index < set.size then set.updated(index.toInt, Truth(true)) else set))
      case ("bit_set_full", Vector(Elements(set))) => Some(Truth(!set.contains(Truth(false))))
      case ("bits_prefix", Vector(Elements(left), Elements(right))) => Some(Truth(right.startsWith(left)))
      case ("bit_set_union", Vector(Elements(left), Elements(right))) => Some(Elements(united(left, right)))
      // every_assignment f is true exactly when f is true at both Booleans.
      // The formula is decided by enumerating the assignments, one variable
      // per binder, a nested every_assignment as the conjunction over both
      // values of its variable (the Prolog decided it with library(clpb),
      // the nested one as the negation of an existential over the
      // negation); an index past the argument's own binders reads nothing.
      case ("every_assignment", Vector(Quantified(binder))) =>
        if !scoped(binder, 0) then None
        else Some(Truth(holdsForBoth(binder, List.empty)))
      case (known, _) if implemented(known) =>
        throw IllegalArgumentException(s"the native reference of $known takes no arguments $arguments")
      case _ => None

  private val implemented: Set[String] = Set(
    "merge_binary_increment", "merge_binary_plus", "merge_binary_times", "merge_binary_equality",
    "natural_equal", "natural_double", "natural_at_least", "natural_difference", "length",
    "binary_to_unary", "binary_increment", "unary_to_binary", "bit_set_member", "bit_set_insert",
    "bit_set_full", "bits_prefix", "bit_set_union", "every_assignment"
  )

  private def bits(values: Vector[ReferenceValue]): Vector[Boolean] = values.map {
    case Truth(bit) => bit
    case other      => throw IllegalArgumentException(s"not a bit: $other")
  }

  private def truths(bits: Vector[Boolean]): ReferenceValue = Elements(bits.map(Truth(_)))

  private def bitsValue(bits: Vector[Boolean]): BigInt =
    bits.foldRight(BigInt(0))((bit, rest) => (if bit then 1 else 0) + 2 * rest)

  private def bitsIncremented(bits: Vector[Boolean]): Vector[Boolean] =
    val carried = bits.takeWhile(identity)
    val rest = bits.drop(carried.size)
    if rest.isEmpty then carried.map(_ => false) :+ true
    else (carried.map(_ => false) :+ true) ++ rest.tail

  private def numberBits(number: BigInt): Vector[Boolean] =
    if number < 0 then throw IllegalArgumentException(s"not a natural number: $number")
    else
      Vector.unfold(number)(remaining => if remaining == 0 then None else Some((remaining.testBit(0), remaining >> 1)))

  private def united(left: Vector[ReferenceValue], right: Vector[ReferenceValue]): Vector[ReferenceValue] =
    val common = left.zip(right).map((bit, other) => Truth(bit == Truth(true) || other == Truth(true)))
    common ++ left.drop(common.size) ++ right.drop(common.size)

  /** Every index of the formula reads a binder of the formula's own, `depth`
    * binders enclosing it.
    */
  private def scoped(formula: QuantifiedFormula, depth: Int): Boolean = formula match
    case QuantifiedFormula.Binder(body)     => scoped(body, depth + 1)
    case QuantifiedFormula.Bound(index)     => index >= 0 && index < depth
    case QuantifiedFormula.Node(_, children) => children.forall(scoped(_, depth))

  private def holdsForBoth(binder: QuantifiedFormula.Binder, environment: List[Boolean]): Boolean =
    holds(binder.body, true :: environment) && holds(binder.body, false :: environment)

  /** The formula's truth under the values of its enclosing binders, the
    * innermost first.
    */
  private def holds(formula: QuantifiedFormula, environment: List[Boolean]): Boolean = formula match
    case QuantifiedFormula.Bound(index)                   => environment(index)
    case QuantifiedFormula.Node("true", Vector())         => true
    case QuantifiedFormula.Node("false", Vector())        => false
    case QuantifiedFormula.Node("not", Vector(operand))   => !holds(operand, environment)
    case QuantifiedFormula.Node("and", Vector(left, right)) => holds(left, environment) && holds(right, environment)
    case QuantifiedFormula.Node("or", Vector(left, right))  => holds(left, environment) || holds(right, environment)
    case QuantifiedFormula.Node("exclusive", Vector(left, right)) => holds(left, environment) != holds(right, environment)
    case QuantifiedFormula.Node("every_assignment", Vector(binder: QuantifiedFormula.Binder)) =>
      holdsForBoth(binder, environment)
    case other => throw IllegalArgumentException(s"not a formula of the circuit grammar: $other")
