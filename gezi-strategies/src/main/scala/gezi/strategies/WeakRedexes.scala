package gezi.strategies

/** The fold state of `weak_redexes`: the count of weak redexes, which is the
  * value and the rank, and how many arguments the term, as the head of a
  * spine, still waits for to make a weak redex, `None` for none
  * (`redexes(Count, Pending)`).
  */
final case class RedexesState(count: BigInt, waiting: Option[Int]) extends FoldState

/** The reading of `weak_redexes`: the arguments the term still waits for,
  * which an application over it reads; at most the holes of a thunk of the
  * graph, finitely many.
  */
final case class RedexesReading(waiting: Option[Int]) extends ModuleReading

/** A module of a breadth round, the module `weak_redexes`, the port of
  * `gezi/prolog/gezi/baseline/weak_redexes.pl`, whose module
  * documentation this follows: the number of WEAK REDEXES of the term, the
  * weak redexes of combinatory logic (Hindley and Seldin, Lambda-Calculus
  * and Combinators, 2008, chapter 2), a combinator applied to as many
  * arguments as it takes, read on the IR. The head of an application spine
  * takes N arguments when it is a thunk with N holes, N at least 1, or an
  * instruction whose term is one (the define's term of the index, else the layer
  * the instruction stands for); every spine whose head takes N arguments and that
  * has at least N counts once, under binders and in the bodies of thunks
  * alike; a thunk's filling counts at every occurrence of its slot in the
  * resolved body. An instruction's own term is not counted, and an instruction whose
  * term is an application, a choice or a parallel takes no argument (a
  * reading of the term's structure, never of its name).
  */
object WeakRedexes extends NormalityModule:

  val name: String = "weak_redexes"

  val meetsExtractionContract: Boolean = true

  def folded(layer: OrderTerm, reading: TermReading): FoldState = state(layer, reading)

  private def state(term: OrderTerm, reading: TermReading): RedexesState = term match
    case OrderTerm.Folded(folded, _) => TermOrder.ownState[RedexesState](folded)
    case OrderTerm.Name(instruction)   => RedexesState(0, pendingOfHead(reading.instructionLayer(instruction)))
    case leaf if TermReading.leafTerm(leaf) => RedexesState(0, None)
    case OrderTerm.Apply(function, argument) =>
      val functionState = state(function, reading)
      val argumentState = state(argument, reading)
      val (contracted, waiting) = functionState.waiting match
        case Some(1)     => (1, None)
        case Some(count) => (0, Some(count - 1))
        case None        => (0, None)
      RedexesState(functionState.count + argumentState.count + contracted, waiting)
    case OrderTerm.Choice(members) => RedexesState(members.map(state(_, reading).count).sum, None)
    case OrderTerm.Parallel(left, right, _) =>
      RedexesState(state(left, reading).count + state(right, reading).count, None)
    case OrderTerm.Thunk(code, holes, fillings) =>
      val body = state(TermReading.resolved(code, holes, fillings), reading)
      RedexesState(body.count, if holes.nonEmpty then Some(holes.size) else body.waiting)
    case other => TermOrder.refused(other)

  /** A thunk with N holes, N at least 1, waits for N arguments; any other
    * term for none (`pending_of_head/2`).
    */
  private def pendingOfHead(term: OrderTerm): Option[Int] = term match
    case OrderTerm.Thunk(_, holes, _) if holes.nonEmpty => Some(holes.size)
    case _                                              => None

  def rank(state: FoldState): OrderValue = OrderValue.Number(TermOrder.ownState[RedexesState](state).count)

  override def reading(state: FoldState): ModuleReading =
    RedexesReading(TermOrder.ownState[RedexesState](state).waiting)

  def value(state: FoldState): OrderValue = rank(state)
