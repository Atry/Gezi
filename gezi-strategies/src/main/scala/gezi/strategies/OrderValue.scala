package gezi.strategies

/** A value or a rank of a module of a normality degree, written as the
  * Prolog baseline wrote it (an integer, an atom, a compound term; a list is
  * a chain of `'[|]'` cells ending in `[]`) and ordered as Prolog's standard
  * order of terms orders it: a number before an atom before a compound, numbers
  * by value, atoms by their characters, compounds by arity, then name, then
  * arguments from the left. The extraction compares entries by their lists
  * of ranks in that order, and the greedy fixed point depends on it, so the
  * order is the baseline's to the last tie.
  */
enum OrderValue:
  case Number(value: BigInt)
  case Atom(name: String)
  case Compound(name: String, arguments: Vector[OrderValue])

/** The constructions of values and their order. */
object OrderValue:

  /** The integer as a value. */
  def number(value: Int): OrderValue = Number(BigInt(value))

  /** The Prolog list of the elements. */
  def list(elements: OrderValue*): OrderValue =
    elements.foldRight(Atom("[]"): OrderValue)((element, tail) => Compound("[|]", Vector(element, tail)))

  /** The Prolog pair `Left-Right`. */
  def pair(left: OrderValue, right: OrderValue): OrderValue = Compound("-", Vector(left, right))

  /** Prolog's standard order of terms. */
  given ordering: Ordering[OrderValue] with
    def compare(left: OrderValue, right: OrderValue): Int = (left, right) match
      case (Number(leftValue), Number(rightValue)) => leftValue.compare(rightValue)
      case (Number(_), _)                          => -1
      case (_, Number(_))                          => 1
      case (Atom(leftName), Atom(rightName))       => leftName.compareTo(rightName)
      case (Atom(_), _)                            => -1
      case (_, Atom(_))                            => 1
      case (Compound(leftName, leftArguments), Compound(rightName, rightArguments)) =>
        val byArity = leftArguments.size.compare(rightArguments.size)
        if byArity != 0 then byArity
        else
          val byName = leftName.compareTo(rightName)
          if byName != 0 then byName
          else elementsCompared(leftArguments, rightArguments, 0, leftArguments.size)

  /** The first difference of the elements from `index` to `count`, in the
    * standard order, both vectors at least `count` long; 0 when they agree. A loop over the
    * indices, so that comparing makes nothing (the extraction compares
    * ranks at every candidate; zipping the arguments made 421 MB of one
    * extraction, JFR).
    */
  @scala.annotation.tailrec
  private def elementsCompared(left: Vector[OrderValue], right: Vector[OrderValue], index: Int, count: Int): Int =
    if index >= count then 0
    else
      val byElement = ordering.compare(left(index), right(index))
      if byElement != 0 then byElement else elementsCompared(left, right, index + 1, count)

  /** The order of lists of ranks, one rank for each module: the standard
    * order of the Prolog lists `list(left*)` and `list(right*)`, which is
    * lexicographic with a proper prefix first (the empty list is an atom,
    * before any compound), compared element by element without making the
    * lists.
    */
  val ranksOrdering: Ordering[Vector[OrderValue]] =
    (left: Vector[OrderValue], right: Vector[OrderValue]) =>
      val byPrefix = elementsCompared(left, right, 0, left.size.min(right.size))
      if byPrefix != 0 then byPrefix else left.size.compare(right.size)
