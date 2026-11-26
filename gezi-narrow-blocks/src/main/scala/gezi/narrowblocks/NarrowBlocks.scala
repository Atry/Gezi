package gezi.narrowblocks

import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.ir.Code
import gezi.ir.Spine
import gezi.ir.CodeLayer
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.jit.BackendFacts
import gezi.jit.NativeBackend
import gezi.jit.NativeBinding
import gezi.jit.NativeName
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.JvmTypeName
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.FoldState
import gezi.strategies.ModuleReading
import gezi.strategies.NormalityModule
import gezi.strategies.OrderTerm
import gezi.strategies.OrderValue
import gezi.strategies.TermOrder
import gezi.strategies.TermReading
import gezi.ir

/** What a closed term is to the narrow blocks' grammar:
  * a closed term
  * of no narrow kind, decoded where a filter or a parameter reads it; a
  * narrow natural; a filter's criterion, `binary_set true` admitting zero
  * and `binary_set false` the positive naturals only, or its function; a
  * boolean, by its term λt.λ_. t or λ_.λf. f; the identity, by its term
  * λx. x, or λx. b x x with b a boolean, which is the identity by the β rule,
  * or by its value, a thunk `λx. F x` that applied to a neutral value reads to
  * that value (`readsAsIdentity`; the library's markers `constructor` and
  * `generic`, `λx. (λ"$k". λv. v) "$k" x`); a
  * native, with its
  * places and the arguments given; a closed function of its parameters, a
  * recursion's body (its first hole the recursion itself), or both; the
  * fixed point combinator by value, alone or applied to a recursion's body
  * and some of its arguments. No kind is read from a marker: the grammar
  * reads no hint.
  */
enum NarrowKind:
  case Closed
  case Value
  case Criterion(admitsZero: Boolean)
  case CriterionFunction
  case Truth(value: Boolean)
  case Identity
  case Native(name: NativeName, places: Int, supplied: Int)
  case Thunk(function: Boolean, recursion: Boolean, holes: Int)
  case Fixpoint
  case FixpointApplied(parameters: Int, supplied: Int)

/** What a slot of a narrow block's code holds while it is read: a binder of
  * the block (a parameter, the recursion itself, or one a let or a branch
  * binds), or a closed term of a kind, with what the reader keeps of it.
  */
enum NarrowItem[+Closed]:
  case Parameter(binder: Int)
  case Recursion(binder: Int, parameters: Int)
  case Known(kind: NarrowKind, closed: Closed)

/** A narrow block's expression, a natural: a closed term decoded by a
  * filter's criterion, or a code of the block that reads no binder, with the
  * closed terms of its slots, decoded the same way; a closed narrow natural; a binder; a native's call;
  * a call of a closed partial application of a native or of a recursion,
  * already applied to some of its operands (`PartialApplication`, the
  * partial application and the rest of the operands, read as the full call
  * by the compiler's reader); a closed function's call; the recursion's own call; a recursion's call,
  * the fixed point combinator applied to its body; a branch on a natural,
  * zero, even with its half or odd with its half; a let; a closed natural
  * folded at compile time (`Folded`).
  */
enum NarrowExpression[+Closed]:
  case Literal(closed: Closed)

  /** A closed natural of natives over literals, with the value the compiler
    * computed for it by running its natives, which are pure: emitted as the
    * literal of that value.
    */
  case Folded(closed: Closed, value: BigInt)
  case ClosedCode(code: Code, environment: Map[Int, Closed])
  case Value(closed: Closed)
  case Variable(binder: Int)
  case Native(name: NativeName, arguments: Vector[NarrowExpression[Closed]])
  case PartialApplication(partial: Closed, arguments: Vector[NarrowExpression[Closed]])
  case Call(function: Closed, arguments: Vector[NarrowExpression[Closed]])
  case SelfCall(arguments: Vector[NarrowExpression[Closed]])
  case RecursionCall(body: Closed, arguments: Vector[NarrowExpression[Closed]])
  case Branch(
      scrutinee: NarrowExpression[Closed],
      zero: NarrowExpression[Closed],
      evenHalf: Int,
      even: NarrowExpression[Closed],
      oddHalf: Int,
      odd: NarrowExpression[Closed]
  )
  case Let(binder: Int, value: NarrowExpression[Closed], body: NarrowExpression[Closed])

/** The narrow blocks of the binary naturals' backend: the small first-order
  * input the block compiler accepts, read in one walk of a term's codes, so
  * that the check is mechanical: the input the backend accepts is a narrow,
  * particular shape, checked by one scan that reads no hint. Every
  * value is a canonical binary natural.
  *
  * The grammar, of an expression of a block's code:
  *   - `e ∥ c`, c a criterion (`binary_set p`, the define whose
  *     `native_specialization` the backend represents), e a binder, a closed
  *     term (decoded by c) or an expression;
  *   - a native applied to its places' count of operands, an operand an
  *     expression, a filtered binder or a closed term;
  *   - a closed native partially applied (its supplied operands narrow,
  *     `NarrowKind.Native(name, places, supplied)`), applied to the rest of
  *     its places' count, read as the native's full call, the supplied
  *     operands first in their order; over-application and a partial value
  *     left as a value are refused;
  *   - a closed function applied to its parameters' count of operands;
  *   - the recursion's own binder applied to its parameters' count;
  *   - the fixed point combinator by value applied to a recursion's body
  *     and its parameters' count of operands;
  *   - `(e ∥ c) z (λh. a) (λh. b)`, a branch of a natural on the binary
  *     naturals' Scott encoding: z at zero, a at 2h, b at 2h + 1;
  *   - `(λx. b) e`, a let;
  *   - a closed narrow natural.
  * A bare binder is an expression only as an operand. A closed function's
  * body, and a recursion's (its first hole the recursion), is an
  * expression.
  *
  * The fixed point combinator is recognized by its term, `Θ = A A`, A =
  * λx.λf. f (λv. x x f v), whose β rule Θ G = G (λv. Θ G v) the block
  * compiler reads as recursion: by structure, not by a name (CONTRIBUTING.md, "Structure only: no names, and every function a pure function of the term"). Natives and the criterion are read from the
  * library's `native` declarations and `combinator_property` facts, the
  * backend's facts. Nothing here holds a type: the kinds are of the
  * grammar's productions.
  */
object NarrowBlocks:

  /** The fixed point combinator by value, as the front end writes it. */
  lazy val fixpointByValue: Instruction =
    val half = λ(x => λ(f => f(λ(v => x(x)(f)(v)))))
    Defunctionalization.thunkInstruction(half(half).deBruijnTerm(Map.empty))

  /** The fields' count of the constructor native of one of the backend's
    * data families, if the name is one: a backend fact.
    */
  private def constructorFields(natives: NativeBackend, name: NativeName): Option[Int] =
    natives.families
      .flatMap(family => family.shapeParameters.flatMap(family.constructors(_)))
      .collectFirst { case constructor if constructor.native == name => constructor.fields.size }

  /** The kind of a name of the library, the natives read from the entry's
    * backend: the first native the term is bound to (`BackendFacts.bindings`:
    * a function by a `native` declaration, or a codec's constructor by its
    * position in a `data_family`).
    */
  def nameKind(instruction: Instruction, index: StandardLibraryIndex, natives: NativeBackend): NarrowKind =
    if instruction == fixpointByValue then NarrowKind.Fixpoint
    else if truthOf(instruction).isDefined then truthOf(instruction).fold(NarrowKind.Closed)(NarrowKind.Truth(_))
    else
      BackendFacts.bindings(index, natives).collectFirst { case NativeBinding(`instruction`, name) => name } match
        case Some(name) =>
          natives.natives.get(name) match
            case Some(native) => NarrowKind.Native(name, native.parameters.size, 0)
            case None =>
              constructorFields(natives, name) match
                case Some(fields) => NarrowKind.Native(name, fields, 0)
                case None         => NarrowKind.Closed
        case None =>
          val properties = index.combinatorProperties.collect { case CombinatorProperty(`instruction`, property) => property }
          if properties.exists {
              case Property.NativeSpecialization(_)      => true
              case Property.JvmType(JvmTypeName.Generic) => true
              case _                                     => false
            }
          then NarrowKind.CriterionFunction
          else truthOf(instruction).fold(NarrowKind.Closed)(NarrowKind.Truth(_))

  /** The boolean a term is by its structure: λt.λ_. t or λ_.λf. f, under
    * applications of the identity (λx. x, or a thunk of one parameter whose
    * code is a boolean filling applied to two codes, the selected one the
    * parameter, as `selectedByTruth` reads it); a noinline name's
    * instruction is its own term, read the same way.
    */
  private def truthOf(instruction: Instruction): Option[Boolean] =
    if instruction.opaque then None
    else
      instruction.layer match
        case ir.Thunk(code, holes, fillings) =>
          thunkKind(code, holes, fillings.map(filling => NarrowItem.Known(closedShape(filling), ()))) match
            case NarrowKind.Truth(value) => Some(value)
            case _                       => None
        case ir.Apply(function, argument) =>
          function.layer match
            case ir.Thunk(code, holes, fillings)
                if thunkKind(code, holes, fillings.map(filling => NarrowItem.Known(closedShape(filling), ()))) == NarrowKind.Identity ||
                  readsAsIdentity(function) =>
              truthOf(argument)
            case _ => None
        case _ => None

  /** The kind of a filling that `thunkKind`'s recognition of the identity
    * reads: a boolean, when the filling is itself a thunk that is one
    * whatever its own fillings are (they are read as closed terms of no
    * narrow kind, so the reading does not descend), or nothing narrow.
    */
  private def closedShape(filling: Instruction): NarrowKind =
    filling.layer match
      case ir.Thunk(code, holes, fillings) if !filling.opaque =>
        thunkKind(code, holes, fillings.map(_ => NarrowItem.Known(NarrowKind.Closed, ()))) match
          case NarrowKind.Truth(value) => NarrowKind.Truth(value)
          case _                       => NarrowKind.Closed
      case _ => NarrowKind.Closed

  /** The kind of an application of closed terms of the kinds given. */
  def applicationKind(function: NarrowKind, argument: NarrowKind): NarrowKind = (function, argument) match
    case (NarrowKind.Native(name, places, supplied), operand) if operandKind(operand) =>
      if supplied + 1 == places then NarrowKind.Value else NarrowKind.Native(name, places, supplied + 1)
    case (NarrowKind.Fixpoint, NarrowKind.Thunk(_, true, holes)) =>
      if holes == 1 then NarrowKind.Value else NarrowKind.FixpointApplied(holes - 1, 0)
    case (NarrowKind.FixpointApplied(parameters, supplied), operand) if operandKind(operand) =>
      if supplied + 1 == parameters then NarrowKind.Value else NarrowKind.FixpointApplied(parameters, supplied + 1)
    case (NarrowKind.Thunk(true, _, 1), operand) if operandKind(operand) => NarrowKind.Value
    case (NarrowKind.Identity, kind)                                     => kind
    case (NarrowKind.CriterionFunction, NarrowKind.Truth(value))         => NarrowKind.Criterion(value)
    case _                                                               => NarrowKind.Closed

  /** The kind of a parallel of closed terms of the kinds given. */
  def parallelKind(left: NarrowKind, right: NarrowKind): NarrowKind = right match
    case NarrowKind.Criterion(_) if operandKind(left) => NarrowKind.Value
    case _                                            => NarrowKind.Closed

  /** The kind of a choice: the kind of its chosen member (`chosenMember`),
    * else no narrow kind.
    */
  def choiceKind(members: Vector[NarrowKind]): NarrowKind =
    chosenMember(members).fold(NarrowKind.Closed)(members(_))

  /** The member of a choice the backend compiles: the first of a narrow
    * kind, the members those of the choice's whole
    * right `+` spine searched left to right, the order the member list had
    * before the choice became binary (of a
    * layer over two kinds, its left side then its right, the right
    * side's own kind already its chosen member's). A lemma should not rely on
    * this position: commutativity, if it is ever applied to the choice,
    * makes the order no longer the author's. The others are dropped, which loses
    * answers only and never adds one: M + N ⊑ M, so M + N ⊑_O M, and an
    * answer N0 of M, M ⊑_O N0, is one of M + N; and C[M] refines C[M + N]
    * in every context (application is monotone by (8) and (10)); the backend
    * may drop the members it does not compile, the untyped ones among them.
    * Which member is
    * the typed branch is not read: no marker is recognized.
    *
    * FIXME: the first narrow member by position is taken and the https://github.com/Atry/private-overlay/issues/2032
    * others are dropped, a choice fixed here. Which member to compile is to become an option of one interface chosen
    * by configuration (entry data and `Defaults`).
    */
  def chosenMember(members: Vector[NarrowKind]): Option[Int] =
    members.indexWhere(narrow) match
      case -1    => None
      case found => Some(found)

  /** Whether the kind is one of the grammar's productions. */
  def narrow(kind: NarrowKind): Boolean = kind != NarrowKind.Closed

  /** Whether a term of the kind may be an operand: a natural, a closed term
    * read as a literal, or a native of no operands, such as the binary
    * naturals' zero, a natural as it stands. Without the last, a sum with the
    * numeral zero was no block, and a block holding `plus zero zero` was
    * refused, the inner sum read as a literal that does not decode
    * (measured 2026-11-19). With it, a canonical numeral is a natural of natives over
    * zero, which the compiler's reader folds back into one literal
    * (`NarrowExpression.Folded`).
    */
  private def operandKind(kind: NarrowKind): Boolean = kind match
    case NarrowKind.Value | NarrowKind.Closed | NarrowKind.Native(_, 0, 0) => true
    case _                                                                  => false

  /** The steps within which `readsAsIdentity` reads a thunk's function.
    * MEASURED 2026-11-19 (the markers spelled as tags, the least of
    * the limits 20, 50, 100, 200, 400, 800 and 1,600 within which the reading
    * gave the identity, when the function was read applied to a neutral
    * value; FIXME: remeasure on the reading of `NormalForms.soleHeadReads`): https://github.com/Atry/private-overlay/issues/1968
    * `generic` within 800, `constructor` (the longest key, then `__constructor`,
    * before every key was shortened by a byte)
    * above 800 and within 1,600. 4,000 is 2.5 times the largest. A larger
    * limit costs every thunk of the shape `λx. F x` that is no identity up to
    * that many steps: EntryTracesTest's hot point took 61.8 s at 10,000.
    *
    * FIXME: this fixed budget decides the extraction's cost, and https://github.com/Atry/private-overlay/issues/2036
    * `readsAsIdentity` reads on a path of its own (`Mode.TablingWeakHead` from `ReadingState.knowingTop`), not through
    * the entry's executor. The budget and the reading are to become options of one interface chosen by configuration
    * (entry data and `Defaults`).
    */
  private val identityReadingLimit: Long = 4000L

  /** The identity `λv. v`, the normal form `readsAsIdentity` reads a
    * function against.
    */
  private val identityTerm: Instruction =
    gezi.frontend.Defunctionalization.thunkInstruction(gezi.frontend.DeBruijnTerm.Lambda(gezi.frontend.DeBruijnTerm.Variable(0)))

  /** Whether the closed thunk is the identity by its value, whatever its
    * spelling: a thunk of one parameter whose code is a function applied to
    * the parameter, `λx. F x` with F not reading x, whose function F, a closed
    * term, has under tabling(weak_head) one parallel set of one head that
    * reads the normal form `λv. v` (`NormalForms.soleHeadReads`), within
    * `identityReadingLimit` steps; then `λx. F x` is `λx. x` by the β rule. F
    * is read as the thunk `λx. F` (the same code and slots, x unused) applied
    * to the closed thunk itself, and the binder of `λv. v` is opened by the
    * normal-form reader's own variable, so this reading mints no neutral value
    * (a free variable, `CONTRIBUTING.md`, "Types live only in the term").
    * The head of F is
    * not compared with `λv. v` by its spelling: in the markers' spelling as tags,
    * `λx. (λ"$k". λv. v) "$k" x`,
    * the
    * literal partial function and `λv` are one lambda chain, so F's head is
    * that chain applied to the key's bits, whose code is the partial
    * function's body. The structural readings of `thunkKind` (`λx. x`,
    * `λx. b x x`) do not reach the markers either: the identity by the β
    * rule, read as a pure function of the term, no name and no hint. A reading that
    * does not finish within the limit is no identity.
    */
  def readsAsIdentity(thunk: Instruction): Boolean =
    !thunk.opaque && (thunk.layer match
      case ir.Thunk(code, holes @ Vector(Hole.Bound(bound)), fillings) =>
        code.layer match
          case ir.Apply(function, argument) if argument.layer == ir.Slot(bound) && !mentions(function, bound) =>
            val functionUnderBinder = Instruction(ir.Thunk(function, holes, fillings))
            gezi.weakhead.NormalForms
              .soleHeadReads(
                gezi.weakhead.Mode.TablingWeakHead,
                gezi.weakhead.Value.Apply(functionUnderBinder, thunk),
                identityTerm
              )
              .result(gezi.weakhead.ReadingState.knowingTop(identityReadingLimit)) match
              case gezi.weakhead.Computed.Done(identity, _) => identity
              case gezi.weakhead.Computed.Stopped(_)         => false
          case _ => false
      case _ => false
    )

  /** Whether the code reads the slot outside a thunk of its own. */
  private def mentions(code: Code, slot: Int): Boolean = code.layer match
    case ir.Slot(index)               => index == slot
    case ir.Apply(function, argument) => mentions(function, slot) || mentions(argument, slot)
    case ir.Parallel(left, right)     => mentions(left, slot) || mentions(right, slot)
    case ir.Choice(left, right)       => mentions(left, slot) || mentions(right, slot)
    case ir.Thunk(_, _, fillings)     => fillings.exists(mentions(_, slot))

  /** The kind of a closed thunk whose fillings are the items given: a
    * function when its body is an expression with every hole a parameter, a
    * recursion's body when it is one with its first hole the recursion.
    */
  def thunkKind[Closed](code: Code, holes: Vector[Hole], fillings: Vector[NarrowItem[Closed]]): NarrowKind =
    (holes, code.layer) match
      case (Vector(Hole.Bound(first), Hole.Ignored), ir.Slot(slot)) if slot == first => NarrowKind.Truth(true)
      case (Vector(Hole.Ignored, Hole.Bound(second)), ir.Slot(slot)) if slot == second => NarrowKind.Truth(false)
      case (Vector(Hole.Bound(bound)), ir.Slot(slot)) if slot == bound => NarrowKind.Identity
      case (Vector(Hole.Bound(bound)), ir.Apply(_, _))
          if selectedByTruth(code, holes, fillings).exists(_.layer == ir.Slot(bound)) =>
        NarrowKind.Identity
      case _ => functionKind(code, holes, fillings)

  /** The code a boolean selects in a thunk's code: a filling of the thunk
    * that is a boolean (`NarrowKind.Truth`), applied to exactly two codes, is
    * the first of them when it is λt.λ_. t and the second when it is
    * λ_.λf. f, by two steps of the β rule. None for any other code.
    */
  private def selectedByTruth[Closed](code: Code, holes: Vector[Hole], fillings: Vector[NarrowItem[Closed]]): Option[Code] =
    Spine.of(code) match
      case (head, Vector(first, second)) =>
        head.layer match
          case ir.Slot(slot) =>
            environment(holes, holes.map(_ => NarrowItem.Known(NarrowKind.Closed, Option.empty[Closed])), fillings.map {
              case NarrowItem.Known(kind, closed) => NarrowItem.Known(kind, Option(closed))
              case NarrowItem.Parameter(binder)   => NarrowItem.Parameter(binder)
              case NarrowItem.Recursion(binder, parameters) => NarrowItem.Recursion(binder, parameters)
            }).get(slot).collect { case NarrowItem.Known(NarrowKind.Truth(value), Some(_)) =>
              if value then first else second
            }
          case _ => None
      case _ => None

  private def functionKind[Closed](code: Code, holes: Vector[Hole], fillings: Vector[NarrowItem[Closed]]): NarrowKind =
    if holes.isEmpty then NarrowKind.Closed
    else
      val function = body(code, holes, fillings, recursion = false).isDefined
      val recursion = body(code, holes, fillings, recursion = true).isDefined
      if function || recursion then NarrowKind.Thunk(function, recursion, holes.size) else NarrowKind.Closed

  /** The expression of a closed thunk's body, its holes bound to binders
    * numbered from 0 in lambda order, the first the recursion when
    * `recursion`.
    */
  def body[Closed](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[NarrowItem[Closed]],
      recursion: Boolean
  ): Option[NarrowExpression[Closed]] = explained(code, holes, fillings, recursion).toOption

  /** The expression of the body as `body` reads it, or where and why it is
    * not one: the first code of the walk that no production reads.
    */
  def explained[Closed](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[NarrowItem[Closed]],
      recursion: Boolean
  ): Either[String, NarrowExpression[Closed]] =
    val holeItems = holes.indices.toVector.map(position =>
      if recursion && position == 0 then NarrowItem.Recursion(position, holes.size - 1)
      else NarrowItem.Parameter(position)
    )
    expression(code, environment(holes, holeItems, fillings), holes.size).map(_._1)

  /** A slot's item described for a reason. */
  private def described[Closed](item: Option[NarrowItem[Closed]]): String = item match
    case Some(NarrowItem.Known(kind, _))             => kind.toString
    case Some(NarrowItem.Parameter(binder))          => s"parameter $binder"
    case Some(NarrowItem.Recursion(binder, count))   => s"recursion $binder of $count"
    case None                                        => "no item"

  private def environment[Closed](
      holes: Vector[Hole],
      holeItems: Vector[NarrowItem[Closed]],
      fillings: Vector[NarrowItem[Closed]]
  ): Map[Int, NarrowItem[Closed]] =
    Defunctionalization.slotValues(holes, holeItems, fillings).zipWithIndex.map(_.swap).toMap

  /** The expression of the code under the environment, and the next binder
    * number free.
    */
  private def expression[Closed](
      code: Code,
      environment: Map[Int, NarrowItem[Closed]],
      nextBinder: Int
  ): Either[String, (NarrowExpression[Closed], Int)] =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(NarrowItem.Known(NarrowKind.Value, closed)) => Right((NarrowExpression.Value(closed), nextBinder))
          case other => Left(s"an expression is the slot $slot, a ${described(other)}")
      case ir.Parallel(value, criterion) if criterionRead(criterion, environment) =>
        operand(value, environment, nextBinder)
      case ir.Apply(_, _) =>
        val (head, arguments) = Spine.of(code)
        application(head, arguments, environment, nextBinder)
      case other => Left(s"an expression is ${other.getClass.getSimpleName}: $other")

  /** A filter of a block's code: its criterion admits every canonical
    * natural, so that it holds of every natural the block makes; a block
    * that filters by another criterion is not narrow.
    */
  private def criterionRead[Closed](code: Code, environment: Map[Int, NarrowItem[Closed]]): Boolean =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot).exists {
          case NarrowItem.Known(NarrowKind.Criterion(true), _) => true
          case _                                                => false
        }
      case _ => false

  /** An operand: a filtered or bare binder that is no recursion, a closed
    * term, a native of no operands read as its literal (`operandKind`), or
    * an expression.
    */
  private def operand[Closed](
      code: Code,
      environment: Map[Int, NarrowItem[Closed]],
      nextBinder: Int
  ): Either[String, (NarrowExpression[Closed], Int)] =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(NarrowItem.Parameter(binder))                => Right((NarrowExpression.Variable(binder), nextBinder))
          case Some(NarrowItem.Known(NarrowKind.Value, closed))  => Right((NarrowExpression.Value(closed), nextBinder))
          case Some(NarrowItem.Known(NarrowKind.Closed, closed)) => Right((NarrowExpression.Literal(closed), nextBinder))
          case Some(NarrowItem.Known(NarrowKind.Native(_, 0, 0), closed)) => Right((NarrowExpression.Literal(closed), nextBinder))
          case other => Left(s"an operand is the slot $slot, a ${described(other)}")
      case ir.Parallel(value, criterion) if criterionRead(criterion, environment) =>
        operand(value, environment, nextBinder)
      case _ =>
        closedSlots(code, environment) match
          case Some(closedEnvironment) => Right((NarrowExpression.ClosedCode(code, closedEnvironment), nextBinder))
          case None                    => expression(code, environment, nextBinder)

  /** The closed terms of the slots a code reads, an inner thunk's fillings
    * included, when every one holds a closed term of no narrow kind and no
    * binder: the code is then a closed term of the block, decoded where it
    * is an operand.
    */
  private def closedSlots[Closed](code: Code, environment: Map[Int, NarrowItem[Closed]]): Option[Map[Int, Closed]] =
    def slotsRead(of: Code): Vector[Int] = of.layer match
      case ir.Slot(slot)                => Vector(slot)
      case ir.Apply(function, argument) => slotsRead(function) ++ slotsRead(argument)
      case ir.Parallel(left, right)     => slotsRead(left) ++ slotsRead(right)
      case ir.Choice(left, right)       => slotsRead(left) ++ slotsRead(right)
      case ir.Thunk(_, _, fillings)     => fillings.flatMap(slotsRead)
    val read = slotsRead(code).distinct.map(slot =>
      environment.get(slot).collect { case NarrowItem.Known(NarrowKind.Closed, closed) => slot -> closed }
    )
    Option.when(read.forall(_.isDefined))(read.flatten.toMap)

  private def operands[Closed](
      codes: Vector[Code],
      environment: Map[Int, NarrowItem[Closed]],
      nextBinder: Int
  ): Either[String, (Vector[NarrowExpression[Closed]], Int)] =
    codes.foldLeft(Right((Vector.empty[NarrowExpression[Closed]], nextBinder)): Either[String, (Vector[NarrowExpression[Closed]], Int)]) {
      (sofar, code) =>
        sofar.flatMap((done, next) => operand(code, environment, next).map((made, after) => (done :+ made, after)))
    }

  private def application[Closed](
      head: Code,
      arguments: Vector[Code],
      environment: Map[Int, NarrowItem[Closed]],
      nextBinder: Int
  ): Either[String, (NarrowExpression[Closed], Int)] =
    head.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(NarrowItem.Known(NarrowKind.Native(name, places, 0), _)) if arguments.size == places =>
            operands(arguments, environment, nextBinder).map((made, after) => (NarrowExpression.Native(name, made), after))
          case Some(NarrowItem.Known(NarrowKind.Native(name, places, supplied), closed))
              if supplied > 0 && arguments.size == places - supplied =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (NarrowExpression.PartialApplication(closed, made), after)
            )
          case Some(NarrowItem.Recursion(_, parameters)) if arguments.size == parameters =>
            operands(arguments, environment, nextBinder).map((made, after) => (NarrowExpression.SelfCall(made), after))
          case Some(NarrowItem.Known(NarrowKind.Thunk(true, _, holes), closed)) if arguments.size == holes =>
            operands(arguments, environment, nextBinder).map((made, after) => (NarrowExpression.Call(closed, made), after))
          case Some(NarrowItem.Known(NarrowKind.FixpointApplied(parameters, 0), closed)) if arguments.size == parameters =>
            operands(arguments, environment, nextBinder).map((made, after) => (NarrowExpression.RecursionCall(closed, made), after))
          case Some(NarrowItem.Known(NarrowKind.FixpointApplied(parameters, supplied), closed))
              if supplied > 0 && arguments.size == parameters - supplied =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (NarrowExpression.PartialApplication(closed, made), after)
            )
          case Some(NarrowItem.Known(NarrowKind.Fixpoint, _)) =>
            arguments.headOption.map(_.layer) match
              case Some(ir.Slot(bodySlot)) =>
                environment.get(bodySlot) match
                  case Some(NarrowItem.Known(NarrowKind.Thunk(_, true, holes), closed)) if arguments.size == holes =>
                    operands(arguments.tail, environment, nextBinder).map((made, after) =>
                      (NarrowExpression.RecursionCall(closed, made), after)
                    )
                  case other => Left(s"the fixed point combinator is applied to a ${described(other)}")
              case other => Left(s"the fixed point combinator is applied to $other")
          case other => Left(s"the head of an application of ${arguments.size} is the slot $slot, a ${described(other)}")
      case ir.Parallel(value, criterion) if criterionRead(criterion, environment) && arguments.size == 3 =>
        for
          (scrutinee, afterScrutinee) <- operand(value, environment, nextBinder)
          (zero, afterZero) <- operand(arguments(0), environment, afterScrutinee)
          (evenHalf, even, afterEven) <- branch(arguments(1), environment, afterZero)
          (oddHalf, odd, afterOdd) <- branch(arguments(2), environment, afterEven)
        yield (NarrowExpression.Branch(scrutinee, zero, evenHalf, even, oddHalf, odd), afterOdd)
      case ir.Thunk(inner, Vector(hole), fillings) if arguments.size == 1 =>
        for
          (value, afterValue) <- operand(arguments.head, environment, nextBinder)
          innerEnvironment <- innerEnvironment(inner, Vector(hole), fillings, Vector(NarrowItem.Parameter(afterValue)), environment)
          (body, afterBody) <- expression(inner, innerEnvironment, afterValue + 1)
        yield (NarrowExpression.Let(afterValue, value, body), afterBody)
      case other => Left(s"the head of an application of ${arguments.size} is $other")

  /** A branch's lambda of one hole, its half's binder and its body. */
  private def branch[Closed](
      code: Code,
      environment: Map[Int, NarrowItem[Closed]],
      nextBinder: Int
  ): Either[String, (Int, NarrowExpression[Closed], Int)] =
    code.layer match
      case ir.Thunk(inner, Vector(hole), fillings) =>
        for
          innerEnvironment <- innerEnvironment(inner, Vector(hole), fillings, Vector(NarrowItem.Parameter(nextBinder)), environment)
          (body, after) <- expression(inner, innerEnvironment, nextBinder + 1)
        yield (nextBinder, body, after)
      case other => Left(s"a branch is no lambda of one hole: $other")

  /** The environment of an inner thunk's code: its holes at the items given,
    * its other slots at its fillings, slots of the enclosing code.
    */
  private def innerEnvironment[Closed](
      inner: Code,
      holes: Vector[Hole],
      fillings: Vector[Code],
      holeItems: Vector[NarrowItem[Closed]],
      environment: Map[Int, NarrowItem[Closed]]
  ): Either[String, Map[Int, NarrowItem[Closed]]] =
    val fillingItems = fillings.map(_.layer match
      case ir.Slot(slot) => environment.get(slot)
      case _                    => None
    )
    Either.cond(
      fillingItems.forall(_.isDefined),
      NarrowBlocks.environment(holes, holeItems, fillingItems.flatten),
      s"an inner thunk's fillings are not slots: ${fillings.map(_.layer)}"
    )

/** The fold state of `narrow_blocks`: the narrow kind of the term, and its
  * residual, what the reader reads of it where it stands outside every block
  * (`NarrowBlockOrder`, its rank).
  */
final case class NarrowBlockState(kind: NarrowKind, residual: BigInt) extends FoldState

/** The reading of a `narrow_blocks` state (`NarrowBlockOrder.reading`): its
  * narrow kind.
  */
final case class NarrowBlockReading(kind: NarrowKind) extends ModuleReading

/** The ordering module `narrow_blocks`: a term's rank is its residual, the
  * size of what the reader reads of it once its blocks are computed. The
  * block compiler compiles every maximal closed narrow natural
  * (`NarrowKind.Value`) into a block, computes it once and puts its numeral
  * in its place (`LemmaRoute`'s `blocksComputed`); the reader reads the
  * rest, whatever its kind.
  * So:
  *   - a `Value` term is one block: one for its numeral and, for each child,
  *     what the block reads of it, a `Closed` operand's residual (a constant
  *     the block decodes), a `Value` child's residual less the one of its
  *     numeral (the same block), and nothing of a child of any other narrow
  *     kind, which the block compiles whatever its spelling, so that every
  *     module reads it as unpriced (`compiledChildren`);
  *   - any other term, of a narrow kind or `Closed`, counts one for its own
  *     layer (a thunk its code's layers) and its children's residuals: the
  *     reader reads it whole.
  * So an extraction that orders by it first spells every class it can as a
  * narrow block, and a class that cannot be one by the spelling that leaves
  * the reader the least: the extraction prices a term by whether it passes
  * the check.
  * The rank is a sum of the priced children's residuals, so composed with
  * `Compression` the cost is monotone within a reading and strictly
  * monotone at priced positions (`gezi.extraction.CostModel`, THE
  * CONTRACT). It reads the term, the library's backend facts and the
  * entry's natives (`natives`) only.
  *
  * FIXME: parts of a https://github.com/Atry/private-overlay/issues/2039
  * block are priced other than the block reads them. A thunk is never a
  * `Value` (`NarrowBlocks.thunkKind`), and its fillings are not dropped
  * however its parent reads it, since the extraction folds a thunk's code
  * part by part before the thunk's kind is known (`NarrowCodeFolding`): a
  * function compiled inside a block counts its code's layers wherever it is
  * a filling of a thunk inside the block. And a compiled child is unpriced
  * whole, the `Closed` constants under it included, which the block decodes
  * once at compile time: a spelling that moves a constant under a native's
  * partial application leaves it uncounted. Measured 2026-11-17
  * (NarrowSpellingProbeTest, scratch): `contest-entries-solo`'s nested_10000_hot/direct ranks 6
  * in both spellings of its λ-term, where the model before ranked 24 and
  * 2,352; `contest-entries-wren`'s calls_10000_hot/direct's unreduced term 60 and its reduct
  * 2,349, where it ranked 1,922 and 175.
  */
final case class NarrowBlockOrder(natives: NativeBackend) extends NormalityModule:

  val name: String = "narrow_blocks"

  val meetsExtractionContract: Boolean = true

  def folded(layer: OrderTerm, reading: TermReading): FoldState =
    val narrowKind = kind(layer, reading)
    NarrowBlockState(narrowKind, residual(layer, narrowKind, reading))

  /** The residual of a layer of the kind given: a narrow choice's is its
    * chosen member's, the backend compiling that member and dropping the
    * others (`chosenChoiceMember`), with no layer of its own left to the
    * reader; any other `Value` layer is one block; any other layer the
    * reader reads whole.
    */
  private def residual(layer: OrderTerm, layerKind: NarrowKind, reading: TermReading): BigInt = layer match
    case OrderTerm.Choice(members) if NarrowBlocks.narrow(layerKind) => memberResidual(chosen(members, reading), reading)
    case _ if layerKind == NarrowKind.Value                         => 1 + inBlock(layer, reading)
    case _                                                          => interpreted(layer)

  /** The member of a narrow choice the backend compiles. A choice is narrow
    * only when a member is (`choiceKind`), so a narrow choice has one.
    */
  private def chosen(members: Vector[OrderTerm], reading: TermReading): OrderTerm =
    NarrowBlocks.chosenMember(members.map(kind(_, reading))) match
      case Some(position) => members(position)
      case None =>
        throw IllegalStateException(
          s"a choice reached as narrow has no chosen member, though choiceKind is chosenMember's member's kind and Closed when there is none: $members"
        )

  /** A chosen member's residual: a folded member's from its state, a nested
    * member's as `folded` would give it.
    */
  private def memberResidual(member: OrderTerm, reading: TermReading): BigInt = member match
    case OrderTerm.Folded(state, _) => TermOrder.ownState[NarrowBlockState](state).residual
    case nested                     => residual(nested, kind(nested, reading), reading)

  /** What a block reads of a `Value` layer's children; of a thunk, which is
    * never a `Value`, nothing is asked.
    */
  private def inBlock(term: OrderTerm, reading: TermReading): BigInt = term match
    case OrderTerm.Apply(function, argument) => blockOperand(function, reading) + blockOperand(argument, reading)
    case OrderTerm.Parallel(left, right, _)  => blockOperand(left, reading) + blockOperand(right, reading)
    case _                                   => 0

  /** What a block reads of a child: nothing of an unpriced one; a `Value`
    * child's residual less the one of its numeral, since it is part of the
    * block; a `Closed` child's residual, a constant the block decodes; and a
    * folded child of any other narrow kind, which `compiledChildren` leaves
    * priced only where the extraction cannot drop it (a specialization's
    * typed member), its residual, as the reader would read it. A nested term
    * of a whole term's fold is read as the extraction reads the production:
    * a `Value` one by its residual less its numeral's one, one of any other
    * narrow kind not at all, a `Closed` one by its residual.
    */
  private def blockOperand(child: OrderTerm, reading: TermReading): BigInt = child match
    case OrderTerm.Unpriced(_) => 0
    case OrderTerm.Folded(state, _) =>
      val childState = TermOrder.ownState[NarrowBlockState](state)
      if childState.kind == NarrowKind.Value then childState.residual - 1 else childState.residual
    case nested =>
      val nestedKind = kind(nested, reading)
      if nestedKind == NarrowKind.Value then residual(nested, nestedKind, reading) - 1
      else if NarrowBlocks.narrow(nestedKind) then 0
      else interpreted(nested)

  /** The positions of a `Value` application's or parallel's children of a
    * narrow kind other than `Value`, which the block compiles whatever their
    * spelling: every module reads them as unpriced
    * (`ModuleCostModel.droppedChildren`), and the extraction spells each by
    * its class's least entry of its reading. No position of any other layer.
    */
  override def compiledChildren(layer: OrderTerm, reading: TermReading): Vector[Boolean] =
    val children = layer match
      case OrderTerm.Apply(function, argument) => Vector(function, argument)
      case OrderTerm.Parallel(left, right, _)  => Vector(left, right)
      case _                                   => Vector.empty
    if kind(layer, reading) != NarrowKind.Value then children.map(_ => false)
    else
      children.map(child =>
        val childKind = kind(child, reading)
        NarrowBlocks.narrow(childKind) && childKind != NarrowKind.Value
      )

  override val compilesChildren: Boolean = true

  /** The narrow kind of a term: a folded child's from its state, an
    * unpriced child's from its reading, which is its kind (`reading`), so
    * that a filter's unpriced criterion of a criterion's kind makes the
    * filter narrow.
    */
  private def kind(term: OrderTerm, reading: TermReading): NarrowKind = term match
    case OrderTerm.Folded(state, _)             => TermOrder.ownState[NarrowBlockState](state).kind
    case OrderTerm.Unpriced(NarrowBlockReading(unpricedKind)) => unpricedKind
    case OrderTerm.Name(instruction)         => NarrowBlocks.nameKind(instruction, reading.index, natives)
    case OrderTerm.Apply(function, argument) => NarrowBlocks.applicationKind(kind(function, reading), kind(argument, reading))
    case OrderTerm.Parallel(left, right, _)     => NarrowBlocks.parallelKind(kind(left, reading), kind(right, reading))
    case OrderTerm.Choice(members)           => NarrowBlocks.choiceKind(members.map(kind(_, reading)))
    case OrderTerm.Thunk(code, holes, fillings) =>
      NarrowBlocks.thunkKind(code, holes, fillings.map(filling => NarrowItem.Known(kind(filling, reading), ())))
    case _ => NarrowKind.Closed

  /** The residual of a layer that is no block: one for each of its own
    * layers and its children's residuals.
    */
  private def interpreted(term: OrderTerm): BigInt = term match
    case OrderTerm.Folded(state, _)                => TermOrder.ownState[NarrowBlockState](state).residual
    case OrderTerm.Apply(function, argument)    => 1 + interpreted(function) + interpreted(argument)
    case OrderTerm.Parallel(left, right, _)        => 1 + interpreted(left) + interpreted(right)
    case OrderTerm.Choice(members)              => 1 + members.map(interpreted).sum
    case OrderTerm.Thunk(code, _, fillings)     => codeSize(code) + fillings.map(interpreted).sum
    case _                                      => 1

  private def codeSize(code: Code): BigInt = code.layer match
    case ir.Slot(_)                   => 1
    case ir.Apply(function, argument) => 1 + codeSize(function) + codeSize(argument)
    case ir.Parallel(left, right)     => 1 + codeSize(left) + codeSize(right)
    case ir.Choice(_, _) =>
      // One for the chain, as for the member list the choice was before it
      // became binary, and the members of its right `+` spine.
      val Code.ChoiceMembers(members) = code
      1 + members.map(codeSize).sum
    case ir.Thunk(inner, _, fillings) => 1 + codeSize(inner) + fillings.map(codeSize).sum

  def rank(state: FoldState): OrderValue =
    OrderValue.Number(TermOrder.ownState[NarrowBlockState](state).residual)

  def value(state: FoldState): OrderValue = rank(state)

  /** The state's narrow kind: every parent's fold reads it (`kind` of
    * `OrderTerm.Folded`), and the rank does not carry it, so two entries of
    * one class whose kinds differ are two readings, kept side by side
    * (`gezi.extraction.CostModel`, THE CONTRACT: a parent reads of a
    * child its cost and its reading only): with one reading, two entries of
    * one rank and different kinds would fold a parent to two costs.
    */
  override def reading(state: FoldState): ModuleReading =
    NarrowBlockReading(TermOrder.ownState[NarrowBlockState](state).kind)

  /** The member of a narrow choice the backend compiles, the first of a
    * narrow kind (`NarrowBlocks.chosenMember`), read from the members'
    * readings, which are their kinds; the backend drops the others. Nothing
    * when no member is narrow: the choice is then no block and every member
    * runs.
    */
  /** The parse summary of a thunk's code part by part (`NarrowCodeFolding`). */
  override val codeFolding: Option[gezi.strategies.CodeFolding] = Some(NarrowCodeFolding)

  override def chosenChoiceMember(memberReadings: Vector[ModuleReading]): Option[Int] =
    val kinds = memberReadings.collect { case NarrowBlockReading(kind) => kind }
    if kinds.size != memberReadings.size then
      throw IllegalArgumentException(s"a reading of no narrow_blocks state among the members: $memberReadings")
    NarrowBlocks.chosenMember(kinds)
