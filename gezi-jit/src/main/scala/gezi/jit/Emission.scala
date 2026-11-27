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
import gezi.ir.{Configured, NativeSpecializer}

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
enum ClauseStart[C <: NativeSpecializer & Singleton]:
  case Evaluation(term: JitValue[C], arguments: Vector[JitValue[C]])
  case Answer(head: JitHead[C])
  case Instance(code: Code, fillings: Vector[JitValue[C]], arguments: Vector[JitValue[C]])
  case ParallelHead(left: JitValue[C], right: JitValue[C], arguments: Vector[JitValue[C]])

/** A code compiled by a backend: its emission, and the start of each clause
  * under an instance's fillings.
  */
trait CompiledCode[C <: NativeSpecializer & Singleton]:

  /** The emission the code was compiled from. */
  def emission: Emission

  /** The start of the clause at the index under the fillings, which are at
    * least as many as the code's slots.
    */
  def clause(index: Int, fillings: Vector[JitValue[C]]): ClauseStart[C]

/** A compilation backend: turns a code's emission into something that
  * runs. The closure backend (`ClosureBackend`) compiles each clause into a
  * Scala closure; a backend that emits bytecode or TASTy would implement the
  * same trait, the subrepo's `gezi.ematching.Backend` being the
  * precedent. Every backend runs an emission the same way: the same clause
  * starts, in the same order.
  */
trait CompilationBackend:

  /** The code compiled from its emission, each parallel its instances hold
    * built by `parallel` (the facts' native specializer, `NativeSpecializer.parallelOfValues`).
    */
  def compiled[C <: NativeSpecializer & Singleton](code: Code, emission: Emission, parallel: (JitValue[C], JitValue[C]) => JitValue[C])(using C): CompiledCode[C]

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

  def compiled[C <: NativeSpecializer & Singleton](code: Code, emission: Emission, parallel: (JitValue[C], JitValue[C]) => JitValue[C])(using C): CompiledCode[C] =
    CompiledClosures[C](code, emission, emission.clauses.map(clauseClosure(code, _, parallel)))

  /** A closure that builds the instance of a code under the fillings. */
  private type Builder[C <: NativeSpecializer & Singleton] = Vector[JitValue[C]] => TailRec[JitValue[C]]

  private final case class CompiledClosures[C <: NativeSpecializer & Singleton](
      code: Code,
      emission: Emission,
      closures: Vector[Vector[JitValue[C]] => ClauseStart[C]]
  ) extends CompiledCode[C]:
    def clause(index: Int, fillings: Vector[JitValue[C]]): ClauseStart[C] = closures(index)(fillings)

  private def clauseClosure[C <: NativeSpecializer & Singleton](
      code: Code,
      clause: EmittedClause,
      parallel: (JitValue[C], JitValue[C]) => JitValue[C]
  )(using C): Vector[JitValue[C]] => ClauseStart[C] =
    def builder(code: Code): Builder[C] = builderOf(code, parallel).result
    clause match
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
        fillings => ClauseStart.Evaluation(CodeReading.instance(code, fillings, parallel), Vector.empty)

  private def built[C <: NativeSpecializer & Singleton](builders: Vector[Builder[C]], fillings: Vector[JitValue[C]])(using C): Vector[JitValue[C]] =
    builders.map(_(fillings).result)

  /** The builder of the code's instance (tree_instance/3): a slot reads its
    * value, a nested thunk keeps its code and holes while its fillings are
    * built. The builder is compiled from the code tree once, each call
    * trampolined.
    */
  private def builderOf[C <: NativeSpecializer & Singleton](code: Code, parallel: (JitValue[C], JitValue[C]) => JitValue[C])(using C): TailRec[Builder[C]] =
    code.layer match
      case Slot(index) => done(fillings => done(slotValue(fillings, index)))
      case Apply(function, argument) =>
        for
          functionBuilder <- tailcall(builderOf(function, parallel))
          argumentBuilder <- tailcall(builderOf(argument, parallel))
        yield (fillings: Vector[JitValue[C]]) =>
          for
            functionValue <- tailcall(functionBuilder(fillings))
            argumentValue <- tailcall(argumentBuilder(fillings))
          yield JitValue.Apply(functionValue, argumentValue)
      case Parallel(left, right) =>
        for
          leftBuilder <- tailcall(builderOf(left, parallel))
          rightBuilder <- tailcall(builderOf(right, parallel))
        yield (fillings: Vector[JitValue[C]]) =>
          for
            leftValue <- tailcall(leftBuilder(fillings))
            rightValue <- tailcall(rightBuilder(fillings))
          yield parallel(leftValue, rightValue)
      case Choice(left, right) =>
        allBuilders(Vector(left, right), parallel).map(builders =>
          (fillings: Vector[JitValue[C]]) => allBuilt(builders, fillings).map(JitValue.Choice(_))
        )
      case Thunk(inner, holes, innerFillings) =>
        // A closure's captures are mostly bare slots, which need no step of
        // the trampoline and are read in one pass.
        val bareSlots = innerFillings.collect { case Code.Slot(index) => index }
        if bareSlots.size == innerFillings.size then
          done(fillings => done(JitValue.Thunk(inner, holes, bareSlots.map(slotValue(fillings, _)))))
        else
          allBuilders(innerFillings, parallel).map(builders =>
            (fillings: Vector[JitValue[C]]) => allBuilt(builders, fillings).map(JitValue.Thunk(inner, holes, _))
          )

  /** The value of the slot under the fillings. */
  private def slotValue[C <: NativeSpecializer & Singleton](fillings: Vector[JitValue[C]], index: Int)(using C): JitValue[C] =
    if index < fillings.size then fillings(index)
    else throw EvaluationError(EvaluationErrorReason.SlotWithoutValue(index, fillings.size))

  private def allBuilders[C <: NativeSpecializer & Singleton](codes: Vector[Code], parallel: (JitValue[C], JitValue[C]) => JitValue[C])(using C): TailRec[Vector[Builder[C]]] =
    def from(index: Int, found: Vector[Builder[C]]): TailRec[Vector[Builder[C]]] =
      if index >= codes.size then done(found)
      else tailcall(builderOf(codes(index), parallel)).flatMap(next => from(index + 1, found :+ next))
    from(0, Vector.empty)

  private def allBuilt[C <: NativeSpecializer & Singleton](builders: Vector[Builder[C]], fillings: Vector[JitValue[C]])(using C): TailRec[Vector[JitValue[C]]] =
    def from(index: Int, found: Vector[JitValue[C]]): TailRec[Vector[JitValue[C]]] =
      if index >= builders.size then done(found)
      else tailcall(builders(index)(fillings)).flatMap(next => from(index + 1, found :+ next))
    from(0, Vector.empty)

/** The readings of codes the strategies and the JIT share. */
object CodeReading:

  /** The number of slots of the code (code_slot_count/2): one more than the
    * largest slot index it reads, inner thunks' codes read only through
    * their fillings, as the code's facts hold them (`Code.facts`).
    */
  def slotCount(code: Code): Int = Code.facts(code).slotsRead.lastOption.fold(0)(_ + 1)

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
    * run-time value of the JIT, each parallel built by `parallel`.
    */
  def instance[C <: NativeSpecializer & Singleton](code: Code, fillings: Vector[JitValue[C]], parallel: (JitValue[C], JitValue[C]) => JitValue[C])(using C): JitValue[C] =
    instanceOf(code, fillings, parallel).result

  private def instanceOf[C <: NativeSpecializer & Singleton](code: Code, fillings: Vector[JitValue[C]], parallel: (JitValue[C], JitValue[C]) => JitValue[C])(using C): TailRec[JitValue[C]] =
    code.layer match
      case Slot(index) =>
        if index < fillings.size then done(fillings(index))
        else throw EvaluationError(EvaluationErrorReason.SlotWithoutValue(index, fillings.size))
      case Apply(function, argument) =>
        for
          functionInstance <- tailcall(instanceOf(function, fillings, parallel))
          argumentInstance <- tailcall(instanceOf(argument, fillings, parallel))
        yield JitValue.Apply(functionInstance, argumentInstance)
      case Parallel(left, right) =>
        for
          leftInstance <- tailcall(instanceOf(left, fillings, parallel))
          rightInstance <- tailcall(instanceOf(right, fillings, parallel))
        yield parallel(leftInstance, rightInstance)
      case Choice(left, right) => allInstances(Vector(left, right), fillings, parallel).map(JitValue.Choice(_))
      case Thunk(inner, holes, innerFillings) =>
        allInstances(innerFillings, fillings, parallel).map(JitValue.Thunk(inner, holes, _))

  private def allInstances[C <: NativeSpecializer & Singleton](
      codes: Vector[Code],
      fillings: Vector[JitValue[C]],
      parallel: (JitValue[C], JitValue[C]) => JitValue[C]
  )(using C): TailRec[Vector[JitValue[C]]] =
    def from(index: Int, found: Vector[JitValue[C]]): TailRec[Vector[JitValue[C]]] =
      if index >= codes.size then done(found)
      else tailcall(instanceOf(codes(index), fillings, parallel)).flatMap(next => from(index + 1, found :+ next))
    from(0, Vector.empty)
