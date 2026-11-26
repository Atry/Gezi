package gezi.jit

import gezi.weakhead.EvaluationError
import gezi.weakhead.EvaluationErrorReason
import gezi.frontend.Defunctionalization
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Hole
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** One clause of a code's emission, the data a generation strategy writes
  * for one spine of the code (jit_emission.pl, WHAT AN EMITTED PREDICATE
  * COMPUTES): a leaf of the code and the codes of the arguments it is
  * applied to, in application order, each a code over the instance's slots
  * whose instance the clause builds at run time, never evaluates.
  */
enum EmittedClause:

  /** A slot's value applied to the arguments: its heads read at run time
    * (jit_head/2, jit_function_applied/3).
    */
  case SlotLeaf(index: Int, arguments: Vector[Code])

  /** A thunk of the code left with a hole and no argument: the head, its
    * holes filled when the clause was written.
    */
  case LambdaLeaf(code: Code, holes: Vector[Hole], fillings: Vector[Code])

  /** A thunk of the code whose holes the arguments filled when the clause
    * was written: an inner instance of its code, applied to the arguments
    * left. The clause calls the inner code's compiled closure through the
    * JIT, as the Prolog clause called the inner code's predicate by name.
    */
  case InstanceLeaf(code: Code, fillings: Vector[Code], arguments: Vector[Code])

  /** A parallel applied to the arguments: its heads, a decode point's at run
    * time when its criterion reaches one (jit_parallel_head/3).
    */
  case ParallelLeaf(left: Code, right: Code, arguments: Vector[Code])

  /** A choice applied to arguments, built and evaluated as a value; with no
    * argument, a choice of two members whose second is a parallel, whether
    * a fallback point depending on the values its slots hold.
    */
  case ChoiceLeaf(members: Vector[Code], arguments: Vector[Code])

  /** The whole instance built and its heads taken by the JIT's own rules
    * (the strategy `interpreted_instances`).
    */
  case InterpretedInstance

/** The emission of a code: the number of its slots, the instance's
  * fillings it reads, and its clauses in order, whose answers are, in order,
  * the heads of an instance of the code.
  */
final case class Emission(slotCount: Int, clauses: Vector[EmittedClause])

/** A generation strategy (jit_emission.pl, GENERATION STRATEGIES; plan
  * principle 151): how a code's clauses are written. The contract the JIT
  * relies on: the emission's slot count is the code's; its clauses answer,
  * in order, the heads the JIT's own rules answer for the instance of the
  * code, and drop and reorder none; the emission is data, a function of the
  * code, and reads no state.
  */
trait GenerationStrategy:

  /** The emission of the code, read from its identifier. */
  def emission(code: Code): Emission

/** What a clause starts with at run time, under the instance's fillings: a
  * term whose heads, applied to the arguments, it answers; a head; an inner
  * instance applied to the arguments; or a parallel applied to the
  * arguments.
  */
enum ClauseStart:
  case Evaluation(term: JitValue, arguments: Vector[JitValue])
  case Answer(head: JitHead)
  case Instance(code: Code, fillings: Vector[JitValue], arguments: Vector[JitValue])
  case ParallelHead(left: JitValue, right: JitValue, arguments: Vector[JitValue])

/** A code compiled by a backend: its emission, and the start of each clause
  * under an instance's fillings.
  */
trait CompiledCode:

  /** The emission the code was compiled from. */
  def emission: Emission

  /** The start of the clause at the index under the fillings, which are at
    * least as many as the code's slots.
    */
  def clause(index: Int, fillings: Vector[JitValue]): ClauseStart

/** A compilation backend: turns a code's emission into something that
  * runs. The closure backend (`ClosureBackend`) compiles each clause into a
  * Scala closure; a backend that emits bytecode or TASTy would implement the
  * same trait, the subrepo's `gezi.ematching.Backend` being the
  * precedent. Every backend runs an emission the same way: the same clause
  * starts, in the same order.
  */
trait CompilationBackend:

  /** The code compiled from its emission. */
  def compiled(code: Code, emission: Emission): CompiledCode

/** The strategy `predicate_per_code`, the default (jit_emission.pl,
  * code_emission/3): one clause for each spine of the code's body, so that
  * a choice applied to nothing is one clause per member, holes filled when the clause is written, and an inner
  * instance a call of its code.
  */
object PredicatePerCode extends GenerationStrategy:

  def emission(code: Code): Emission =
    Emission(CodeReading.slotCount(code), spines(code, Vector.empty))

  /** The clauses of the code applied to the arguments (tree_spines/5): an
    * application adds its argument in front; a choice applied to nothing
    * gives its members' clauses in order, unless it is a candidate fallback
    * point, two members the second a parallel.
    */
  @tailrec
  private def spines(code: Code, arguments: Vector[Code]): Vector[EmittedClause] =
    code.layer match
      case Slot(index) => Vector(EmittedClause.SlotLeaf(index, arguments))
      case Apply(function, argument) => spines(function, argument +: arguments)
      case Thunk(inner, holes, fillings) => Vector(thunkApplied(inner, holes, fillings, arguments))
      case Choice(left, right) =>
        val members = Vector(left, right)
        if arguments.nonEmpty then Vector(EmittedClause.ChoiceLeaf(members, arguments))
        else if members.size == 2 && members(1).layer.isInstanceOf[Parallel[?]] then
          Vector(EmittedClause.ChoiceLeaf(members, Vector.empty))
        else members.flatMap(member => memberSpines(member))
      case Parallel(left, right) => Vector(EmittedClause.ParallelLeaf(left, right, arguments))

  private def memberSpines(member: Code): Vector[EmittedClause] =
    spines(member, Vector.empty)

  /** A thunk of the code applied to the arguments, its holes filled now
    * (thunk_applied/8; the first beta clause of D2 of `lean/README.md`, "Design decisions").
    */
  @tailrec
  private def thunkApplied(
      inner: Code,
      holes: Vector[Hole],
      fillings: Vector[Code],
      arguments: Vector[Code]
  ): EmittedClause =
    if holes.isEmpty then EmittedClause.InstanceLeaf(inner, fillings, arguments)
    else if arguments.isEmpty then EmittedClause.LambdaLeaf(inner, holes, fillings)
    else thunkApplied(inner, holes.tail, CodeReading.holeFilled(holes.head, holes.tail, fillings, arguments.head), arguments.tail)

/** The strategy `interpreted_instances` (jit_emission.pl): one clause, which
  * builds the whole instance and takes its heads by the JIT's own rules, as
  * an instance beyond the compilation budget is interpreted.
  */
object InterpretedInstances extends GenerationStrategy:

  def emission(code: Code): Emission =
    Emission(CodeReading.slotCount(code), Vector(EmittedClause.InterpretedInstance))

/** The closure backend: each clause of an emission compiled once into a
  * Scala closure from the instance's fillings to the clause's start, the
  * instances of its argument codes built by closures compiled from the code
  * trees, so that what a clause does is chosen when it is compiled.
  */
object ClosureBackend extends CompilationBackend:

  def compiled(code: Code, emission: Emission): CompiledCode =
    CompiledClosures(code, emission, emission.clauses.map(clauseClosure(code, _)))

  private final case class CompiledClosures(
      code: Code,
      emission: Emission,
      closures: Vector[Vector[JitValue] => ClauseStart]
  ) extends CompiledCode:
    def clause(index: Int, fillings: Vector[JitValue]): ClauseStart = closures(index)(fillings)

  /** A closure that builds the instance of a code under the fillings. */
  private type Builder = Vector[JitValue] => TailRec[JitValue]

  private def clauseClosure(
      code: Code,
      clause: EmittedClause,
  ): Vector[JitValue] => ClauseStart = clause match
    case EmittedClause.SlotLeaf(index, arguments) =>
      val builders = arguments.map(builder(_))
      fillings => ClauseStart.Evaluation(fillings(index), built(builders, fillings))
    case EmittedClause.LambdaLeaf(inner, holes, innerFillings) =>
      val builders = innerFillings.map(builder(_))
      fillings => ClauseStart.Answer(JitHead.Lambda(inner, holes, built(builders, fillings)))
    case EmittedClause.InstanceLeaf(inner, innerFillings, arguments) =>
      val fillingBuilders = innerFillings.map(builder(_))
      val argumentBuilders = arguments.map(builder(_))
      fillings => ClauseStart.Instance(inner, built(fillingBuilders, fillings), built(argumentBuilders, fillings))
    case EmittedClause.ParallelLeaf(left, right, arguments) =>
      val leftBuilder = builder(left)
      val rightBuilder = builder(right)
      val argumentBuilders = arguments.map(builder(_))
      fillings =>
        ClauseStart.ParallelHead(leftBuilder(fillings).result, rightBuilder(fillings).result, built(argumentBuilders, fillings))
    case EmittedClause.ChoiceLeaf(members, arguments) =>
      val memberBuilders = members.map(builder(_))
      val argumentBuilders = arguments.map(builder(_))
      fillings => ClauseStart.Evaluation(JitValue.Choice(built(memberBuilders, fillings)), built(argumentBuilders, fillings))
    case EmittedClause.InterpretedInstance =>
      fillings => ClauseStart.Evaluation(CodeReading.instance(code, fillings), Vector.empty)

  private def built(builders: Vector[Builder], fillings: Vector[JitValue]): Vector[JitValue] =
    builders.map(_(fillings).result)

  /** The builder of the code's instance (tree_instance/3): a slot reads its
    * value, a nested thunk keeps its code and holes while its fillings are
    * built. The builder is compiled from the code tree once, each call
    * trampolined.
    */
  private def builder(code: Code): Builder =
    builderOf(code).result

  private def builderOf(code: Code): TailRec[Builder] =
    code.layer match
      case Slot(index) =>
        done(fillings =>
          if index < fillings.size then done(fillings(index))
          else throw EvaluationError(EvaluationErrorReason.SlotWithoutValue(index, fillings.size))
        )
      case Apply(function, argument) =>
        for
          functionBuilder <- tailcall(builderOf(function))
          argumentBuilder <- tailcall(builderOf(argument))
        yield (fillings: Vector[JitValue]) =>
          for
            functionValue <- tailcall(functionBuilder(fillings))
            argumentValue <- tailcall(argumentBuilder(fillings))
          yield JitValue.Apply(functionValue, argumentValue)
      case Parallel(left, right) =>
        for
          leftBuilder <- tailcall(builderOf(left))
          rightBuilder <- tailcall(builderOf(right))
        yield (fillings: Vector[JitValue]) =>
          for
            leftValue <- tailcall(leftBuilder(fillings))
            rightValue <- tailcall(rightBuilder(fillings))
          yield JitValue.Parallel(leftValue, rightValue)
      case Choice(left, right) =>
        allBuilders(Vector(left, right)).map(builders =>
          (fillings: Vector[JitValue]) => allBuilt(builders, fillings).map(JitValue.Choice(_))
        )
      case Thunk(inner, holes, innerFillings) =>
        allBuilders(innerFillings).map(builders =>
          (fillings: Vector[JitValue]) => allBuilt(builders, fillings).map(JitValue.Thunk(inner, holes, _))
        )

  private def allBuilders(codes: Vector[Code]): TailRec[Vector[Builder]] =
    def from(index: Int, found: Vector[Builder]): TailRec[Vector[Builder]] =
      if index >= codes.size then done(found)
      else tailcall(builderOf(codes(index))).flatMap(next => from(index + 1, found :+ next))
    from(0, Vector.empty)

  private def allBuilt(builders: Vector[Builder], fillings: Vector[JitValue]): TailRec[Vector[JitValue]] =
    def from(index: Int, found: Vector[JitValue]): TailRec[Vector[JitValue]] =
      if index >= builders.size then done(found)
      else tailcall(builders(index)(fillings)).flatMap(next => from(index + 1, found :+ next))
    from(0, Vector.empty)

/** The readings of codes the strategies and the JIT share. */
object CodeReading:

  /** The number of slots of the code (code_slot_count/2): one more than the
    * largest slot index it reads, inner thunks' codes read only through
    * their fillings. Each code identifier is read once.
    */
  def slotCount(code: Code): Int =
    @tailrec
    def counted(pending: List[Code], seen: Set[Code], count: Int): Int =
      pending match
        case Nil => count
        case next :: rest if seen.contains(next) => counted(rest, seen, count)
        case next :: rest =>
          val nowSeen = seen + next
          next.layer match
            case Slot(index)               => counted(rest, nowSeen, count.max(index + 1))
            case Apply(function, argument) => counted(function :: argument :: rest, nowSeen, count)
            case Parallel(left, right)     => counted(left :: right :: rest, nowSeen, count)
            case Choice(left, right)       => counted(left :: right :: rest, nowSeen, count)
            case Thunk(_, _, fillings)     => counted(fillings.toList ++ rest, nowSeen, count)
    counted(List(code), Set.empty, 0)

  /** The fillings after the first hole takes the argument (hole_filled/5),
    * over any kind of filling.
    */
  def holeFilled[Filling](hole: Hole, remaining: Vector[Hole], fillings: Vector[Filling], argument: Filling): Vector[Filling] =
    hole match
      case Hole.Ignored => fillings
      case Hole.Bound(slot) =>
        val position = Defunctionalization.fillingPosition(remaining, slot).min(fillings.size)
        if position == fillings.size then fillings :+ argument
        else (fillings.take(position) :+ argument) ++ fillings.drop(position)

  /** The instance of the code under the fillings (instance_term/3), a
    * run-time value of the JIT.
    */
  def instance(code: Code, fillings: Vector[JitValue]): JitValue =
    instanceOf(code, fillings).result

  private def instanceOf(code: Code, fillings: Vector[JitValue]): TailRec[JitValue] =
    code.layer match
      case Slot(index) =>
        if index < fillings.size then done(fillings(index))
        else throw EvaluationError(EvaluationErrorReason.SlotWithoutValue(index, fillings.size))
      case Apply(function, argument) =>
        for
          functionInstance <- tailcall(instanceOf(function, fillings))
          argumentInstance <- tailcall(instanceOf(argument, fillings))
        yield JitValue.Apply(functionInstance, argumentInstance)
      case Parallel(left, right) =>
        for
          leftInstance <- tailcall(instanceOf(left, fillings))
          rightInstance <- tailcall(instanceOf(right, fillings))
        yield JitValue.Parallel(leftInstance, rightInstance)
      case Choice(left, right) => allInstances(Vector(left, right), fillings).map(JitValue.Choice(_))
      case Thunk(inner, holes, innerFillings) =>
        allInstances(innerFillings, fillings).map(JitValue.Thunk(inner, holes, _))

  private def allInstances(codes: Vector[Code], fillings: Vector[JitValue]): TailRec[Vector[JitValue]] =
    def from(index: Int, found: Vector[JitValue]): TailRec[Vector[JitValue]] =
      if index >= codes.size then done(found)
      else tailcall(instanceOf(codes(index), fillings)).flatMap(next => from(index + 1, found :+ next))
    from(0, Vector.empty)
