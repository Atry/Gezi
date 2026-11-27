package gezi.narrowblocks.groups

import gezi.frontend.Defunctionalization
import gezi.frontend.Term.λ
import gezi.ir.Code
import gezi.ir.Spine
import gezi.ir.Hole
import gezi.jit.BackendFacts
import gezi.jit.BinaryNaturalFamily
import gezi.jit.BooleanFamily
import gezi.jit.FamilyIdentity
import gezi.jit.NativeBackend
import gezi.jit.NativeBinding
import gezi.jit.NativeName
import gezi.jit.NativePlace
import gezi.jit.Representation
import gezi.standardlibrary.CombinatorProperty
import gezi.weakhead.BooleanCodec
import gezi.standardlibrary.JvmTypeName
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir
import gezi.ir.{Configured, NativeSpecializer, Pure}

enum GroupKind:
  case Closed
  case Value
  case Criterion(admitsZero: Boolean)
  case CriterionFunction(
      family: Option[FamilyIdentity],
      parameterFamily: Option[FamilyIdentity]
  )
  case Constant(bindings: Vector[NativeName])
  case DeclaredCriterion(family: FamilyIdentity, arity: Int, supplied: Int)
  case BooleanCriterion
  case Truth(value: Boolean)
  case Native(name: NativeName, places: Int, supplied: Int)
  case TruthNative(name: NativeName, places: Int)
  case Thunk(function: Boolean, recursion: Boolean, holes: Int)
  case Fixpoint
  case FixpointApplied(parameters: Int, supplied: Int)
  case ListCriterionFunction
  case ListCriterion(element: GroupRepresentation)
  case IntCriterion(family: FamilyIdentity)

enum GroupItem[+Closed]:
  case Entry(binder: Int)
  case Parameter(binder: Int)
  case FilteredParameter(binder: Int, representation: GroupRepresentation)
  case Recursion(binder: Int, parameters: Int)
  case Known(kind: GroupKind, closed: Closed)

enum GroupExpression[+Closed]:
  case Literal(closed: Closed)
  case ClosedCode(code: Code, environment: Map[Int, Closed])
  case Value(closed: Closed)
  case Variable(binder: Int)
  case Native(name: NativeName, arguments: Vector[GroupExpression[Closed]])
  case PartialApplication(
      partial: Closed,
      arguments: Vector[GroupExpression[Closed]]
  )
  case Call(function: Closed, arguments: Vector[GroupExpression[Closed]])
  case SelfCall(arguments: Vector[GroupExpression[Closed]])
  case RecursionCall(body: Closed, arguments: Vector[GroupExpression[Closed]])
  case Branch(
      scrutinee: GroupExpression[Closed],
      zero: GroupExpression[Closed],
      evenHalf: Int,
      even: GroupExpression[Closed],
      oddHalf: Int,
      odd: GroupExpression[Closed]
  )
  case Let(
      binder: Int,
      value: GroupExpression[Closed],
      body: GroupExpression[Closed]
  )
  case Filtered(
      value: GroupExpression[Closed],
      representation: GroupRepresentation
  )
  case Select(
      scrutinee: GroupExpression[Closed],
      whenTrue: GroupExpression[Closed],
      whenFalse: GroupExpression[Closed]
  )
  case Choice(left: GroupExpression[Closed], right: GroupExpression[Closed])
  case Constructed(
      family: FamilyIdentity,
      constructor: Int,
      term: Closed,
      filter: Vector[Closed],
      fields: Vector[GroupExpression[Closed]]
  )
  case ListBranch(
      scrutinee: GroupExpression[Closed],
      nil: GroupExpression[Closed],
      head: Int,
      tail: Int,
      cons: GroupExpression[Closed]
  )
  case ListConstructed(
      constructor: Closed,
      fields: Vector[GroupExpression[Closed]],
      element: GroupRepresentation
  )

enum GroupRepresentation:
  case Natural
  case Positive
  case Truth

  /** An array list `array_list E` whose elements are of the representation: the
    * naturals, the positive naturals, or a family held as a JVM `int`.
    */
  case ListOf(element: GroupRepresentation)
  case IntOf(family: FamilyIdentity)

/** The grammar of a group block: a copy-on-write copy of the narrow blocks'
  * grammar ([[gezi.narrowblocks.lists.NarrowBlocks]]), read by one mechanical
  * scan of a written closed thunk that reads only syntax, the library's
  * `native` declarations and the backend's facts, and no hint. A representation
  * comes only from a criterion written in the term: a filter's, or the contract
  * of the native whose place an operand fills.
  *
  * A group block computes, for a group of argument values, the group of the
  * thunk's results: a table whose rows are combinations of values
  * (`GroupBackend`). Each production's guarantee on groups:
  *   - an occurrence of a binder branches over the binder's group, each
  *     occurrence on its own, so that the combinations of two occurrences of
  *     one parameter are all there. A parameter of the block is read only under
  *     a filter, at each of its occurrences: the entry decodes an argument in
  *     the representation the filter names, never in one read from the argument
  *     (a let's binder or a branch's half, a value the block computes, may
  *     stand bare);
  *   - a let `(λy. b) e` is b with each occurrence of y branching over e's
  *     group on its own, as e substituted at every occurrence by the β rule;
  *   - a native applied to its places' count of operands is called row by row,
  *     by its static method (`gezi.jit.StaticBlockMethod`): each row's result
  *     is the native's define on that row's single values, by the native's
  *     equation `native = define`, an equation on single values; a row on which
  *     the method answers that there is no normal form stops the block, as a
  *     filter's rejection does. A block with a native that has no static
  *     method, or whose operand's filter does not license the native's place,
  *     is not compiled (`GroupCompilation`); FIXME:
  *     https://github.com/Atry/private-overlay/issues/2224 an operand that is a
  *     group in its row is called value by value, which loses the cross answers
  *     of a define that reads that parameter twice (`square (2 + 3)` by
  *     `λx. times x x` has 6), and is to be fixed: a place called value by
  *     value only under a lemma that the choice distributes there, other rows
  *     left to a row-wise fallback.
  *   - a filter `e ∥ c` reads a value of c's kind (`GroupCompilation` compiles
  *     no block where e is of another kind, nor enters one with an argument of
  *     another kind) and keeps the rows whose value c's representation admits;
  *     a row it rejects stops the block, which gives no value, the reading
  *     reading the application: the rejected term `e ∥ c` has no answer itself,
  *     but a context consuming it can have one (`(cons zero nil ∥ array_list P)
  *     false (λh t. true)` is true), so a dropped row would lose it. The block
  *     itself so loses no answer; the machine's reading of the application
  *     still loses this one at its decode point (a FIXME at
  *     `gezi.jit.Jit.readingDecoded`), as it loses an argument's member the
  *     parameter's filter excludes before the block is entered
  *     (`gezi.jit.Jit.entryDecoded`). The filters: `binary_set true` the
  *     naturals, `binary_set false` the positive naturals, the booleans'
  *     criterion the truth values; `array_list E`, E a naturals' criterion or
  *     the criterion of a family held as a JVM `int`, reads a list and keeps it
  *     relabelled under E when E admits its every element, the empty list under
  *     any E (`StorageEncoding.relabelled`; a list's criterion is read only as
  *     `array_list`, `list_type E` is no filter of a block, and
  *     `GroupCompilation` compiles no block where the filtered value is not a
  *     list). A native's place of positive naturals takes only an operand
  *     filtered by the positive naturals' criterion, or a constant of their
  *     representation (`GroupCompilation`);
  *   - a recursion's call `fixpoint G e1 … en ∥ c`, filtered, is in each row
  *     the call on each operand's group in that row, by the β rule: the group
  *     is substituted at every read of the parameter in G, each read its own
  *     member, so G's parameters are group valued as the block's own are, and a
  *     call is named by its operands' groups (`GroupProgram`, THE CALLS), each
  *     call once per run. A row in which an operand waits makes no call. No
  *     operand has an empty group: the entry's groups are nonempty, a branch
  *     partitions its rows' values, and every operation that would drop a row
  *     stops the block, so by induction every finished call has a nonempty
  *     group of results. A run whose calls all wait on waiting calls is a cycle
  *     and stops the block with no value, so that the reading reads the
  *     application without it: the block gives no answer there rather than
  *     reading a headless cycle as no answer. FIXME:
  *     https://github.com/Atry/private-overlay/issues/2226 a cycle of group
  *     keys can arise where calls of single values ended; iterating from Ω
  *     would give the cycle's exact group;
  *   - a branch on a natural or a boolean computes, row by row, the branch its
  *     value selects, by the β rule of the Scott encoding; so does a branch on
  *     a list filtered by `array_list E`, `l n (λh t. c)`: n on the empty list,
  *     c with h the first element, a value of E, and t the suffix after it, a
  *     list of E;
  *   - an array list's constructor under its filter, `nil ∥ array_list E` or
  *     `cons e l ∥ array_list E`, nil and cons the array lists' codec's
  *     constructors at their positions (`GroupCompilation` checks them against
  *     the backend's facts, and l of the list kind of E), is, row by row, the
  *     list of e's value before l's: the unique spelling of that list, by the β
  *     rule; under the positive naturals' criterion a row whose head is zero
  *     stops the block, as a filter's rejection does;
  *   - a choice `e1 + e2` of two expressions is the union of their groups,
  *     deduplicated by rows, which neither adds nor loses an answer. A choice
  *     with one member an expression and the other not is read as that member
  *     alone: in general a refinement, its normal forms among those of the
  *     choice (M + N ⊑_O M); equal to the choice when it is a specialization
  *     choice whose argument the entry decoded into the criterion T, by the
  *     specialization lemma `f = f + λx. f (x ∥ T)`. The scan recognizes no
  *     specialization choice by its shape: it reads the one member that is an
  *     expression. FIXME: https://github.com/Atry/private-overlay/issues/2223
  *     in general this loses the other member's answers, and is to be fixed:
  *     the block computes the member that is an expression and the other is
  *     read row by row by the reading, its answers joined, which waits on a
  *     row-wise fallback of blocks.
  *   - a closed natural is a constant column, and a closed term written in the
  *     block is one only when it is a storage of a natural or of a value the
  *     backend holds as a JVM primitive (`GroupCompilation`);
  *   - a library name the backend binds as the constructor of no fields of more
  *     than one family is read as the family its place names, never by the
  *     order of its bindings: as a boolean where it is the argument of a
  *     criterion constructor whose parameter is a boolean (P6), the backend
  *     having checked that the booleans' constructor is the Scott boolean, so
  *     that the name equals that boolean by the β rule; as the declared
  *     family's constructor under that family's filter (the production below);
  *     elsewhere as a closed term, which no block reads unless it is a storage;
  *   - a declared family's constructor applied to its fields' count of
  *     expressions and filtered by the family's criterion,
  *     `C e1 … en ∥ T a1 … ak`, C the constructor at its position in T's
  *     `data_family` and each ai the canonical naturals' criterion, is the
  *     row's value of the family, made of each row's field values: by the β
  *     rule its fields are the expressions' values, and its spelling is the
  *     unique one `C (f1 ∥ F1) … ∥ T a1 … ak` when each field's representation
  *     Fi, as `data_fields` gives it at the ai, is the canonical naturals',
  *     which `GroupCompilation` checks against the backend's facts (it compiles
  *     no block otherwise). A constructor applied without its family's filter
  *     is no production.
  * There is no identity read by its value (the function applied to a neutral
  * value of the narrow blocks' `readsAsIdentity`), and no natural folded at
  * compile time by running a native.
  */
object GroupGrammar:

  /** The naturals' representation a naturals' criterion reads: the canonical
    * naturals' when it admits zero, the positive ones' otherwise.
    */
  def naturals(admitsZero: Boolean): GroupRepresentation =
    if admitsZero then GroupRepresentation.Natural
    else GroupRepresentation.Positive

  /** The fixed point combinator by value, as the front end writes it. */
  lazy val fixpointByValue: Pure =
    val half = λ(x => λ(f => f(λ(v => x(x)(f)(v)))))
    Defunctionalization.pure(half(half).deBruijnTerm(Map.empty))

  /** The fields' count of the constructor native of one of the backend's data
    * families, if the name is one: a backend fact.
    */
  private def constructorFields(
      natives: NativeBackend,
      name: NativeName
  ): Option[Int] =
    natives.families
      .flatMap(family => family.shapeParameters.flatMap(family.constructors(_)))
      .collectFirst {
        case constructor if constructor.native == name =>
          constructor.fields.size
      }

  /** The kind of a name of the library, the natives read from the entry's
    * backend: the first native the term is bound to (`BackendFacts.bindings`: a
    * function by a `native` declaration, or a codec's constructor by its
    * position in a `data_family`), no narrow kind when that native's result is
    * a list (a list's constructor), a native of a boolean when it is a boolean;
    * a constant that keeps all its bindings when the term is bound to more than
    * one native, each the constructor of no fields of a family, so that the
    * place it stands in decides which family's it is read as
    * (`applicationKind`, and the declared family production); the booleans'
    * criterion when the term's `native_specialization` names the standard set's
    * boolean family (`BooleanFamily`); a criterion function, with the family
    * its parameter is of (P6), when it names another or the term's JVM type is
    * the generic one.
    */
  def nameKind[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      index: StandardLibraryIndex[C],
      natives: NativeBackend
  )(using
      specializer: C
  ): GroupKind =
    def named(key: Pure): Boolean =
      Configured.same(Configured.fromPure(specializer)(key), instruction)
    lazy val truth = truthOf(instruction)
    if named(fixpointByValue) then GroupKind.Fixpoint
    else if truth.isDefined then
      truth.fold(GroupKind.Closed)(GroupKind.Truth(_))
    else
      val bound = BackendFacts.bindings(index, natives).collect {
        case NativeBinding(key, name) if named(key) => name
      }
      if bound.size > 1 && bound.forall {
          case name @ NativeName.Constructor(_, _) =>
            constructorFields(natives, name).forall(_ == 0)
          case _ => false
        }
      then GroupKind.Constant(bound)
      // A name of several bindings of which some is no constructor of no
      // fields is read as no kind: no order among its bindings decides.
      else if bound.size > 1 then GroupKind.Closed
      else
        bound.headOption match
          case Some(name) =>
            natives.natives.get(name) match
              case Some(native) if native.result == NativePlace.AnyList =>
                GroupKind.Closed
              case Some(native)
                  if native.result == NativePlace.Fixed(Representation.Truth) =>
                GroupKind.TruthNative(name, native.parameters.size)
              case Some(native) =>
                GroupKind.Native(name, native.parameters.size, 0)
              case None =>
                constructorFields(natives, name) match
                  case Some(fields) => GroupKind.Native(name, fields, 0)
                  case None         => GroupKind.Closed
          case None =>
            val facts =
              index.combinatorProperties.filter(fact => named(fact.instruction))
            val properties = facts.map(_.property)
            if properties.contains(
                Property.NativeSpecialization(
                  Representation.arrayListFamily.name
                )
              )
            then GroupKind.ListCriterionFunction
            else if intHeld(properties, natives).isDefined then
              intHeld(properties, natives).fold(GroupKind.Closed)(
                GroupKind.IntCriterion(_)
              )
            else if properties.contains(
                Property.NativeSpecialization(BooleanFamily.identity.name)
              )
            then GroupKind.BooleanCriterion
            else if properties.contains(
                Property.JvmType(JvmTypeName.Generic)
              ) && properties.exists {
                case Property.DataFamily(_, _) => true
                case _                         => false
              }
            then
              val arity = properties
                .collectFirst { case Property.DataFamily(found, _) => found }
                .getOrElse(0)
              // The facts of one term share its one key.
              val Vector(key) = facts.map(_.instruction).distinct: @unchecked
              GroupKind.DeclaredCriterion(
                FamilyIdentity.Declared(key),
                arity,
                0
              )
            else if properties.exists {
                case Property.NativeSpecialization(_)      => true
                case Property.JvmType(JvmTypeName.Generic) => true
                case _                                     => false
              }
            then
              val family = properties
                .collectFirst { case Property.NativeSpecialization(name) =>
                  name
                }
                .flatMap(name => natives.family(FamilyIdentity.Codec(name)))
              GroupKind.CriterionFunction(
                family.map(_.identity),
                family.flatMap(_.parameterFamily)
              )
            else truth.fold(GroupKind.Closed)(GroupKind.Truth(_))

  /** The family of a criterion whose `native_specialization` names a codec that
    * holds its values as a JVM `int` and takes no parameter, the JVM type read
    * from the codec (`gezi.jit.DataFamily.jvmPrimitive`), never from the
    * family's name.
    */
  private def intHeld(
      properties: Vector[Property],
      natives: NativeBackend
  ): Option[FamilyIdentity] =
    properties
      .collectFirst { case Property.NativeSpecialization(name) => name }
      .flatMap(name => natives.family(FamilyIdentity.Codec(name)))
      .filter(family =>
        family.jvmPrimitive
          .contains(gezi.jit.JvmPrimitive.Int) && family.parameterFamily.isEmpty
      )
      .map(_.identity)

  /** The boolean a term is by its structure: λt.λ_. t or λ_.λf. f, under a
    * noinline name's instruction is its own term, read the same way.
    */
  private def truthOf[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C): Option[Boolean] =
    // A native storage the e-graph keeps as a leaf is read as no boolean, its view not read.
    if instruction.heldAsLeaf then None
    else
      instruction.layer match
        case ir.Thunk(code, holes, fillings) =>
          thunkKind(
            code,
            holes,
            fillings.map(filling => GroupItem.Known(closedShape(filling), ()))
          ) match
            case GroupKind.Truth(value) => Some(value)
            case _                      => None
        case _ => None

  /** The kind of a filling that `truthOf` reads: a boolean, when the filling is
    * itself a thunk that is one whatever its own fillings are (they are read as
    * closed terms of no narrow kind, so the reading does not descend), or
    * nothing narrow.
    */
  private def closedShape[C <: NativeSpecializer & Singleton](
      filling: Configured[C]
  )(using C): GroupKind =
    if filling.heldAsLeaf then GroupKind.Closed
    else
      filling.layer match
        case ir.Thunk(code, holes, fillings) if !filling.opaque =>
          thunkKind(
            code,
            holes,
            fillings.map(_ => GroupItem.Known(GroupKind.Closed, ()))
          ) match
            case GroupKind.Truth(value) => GroupKind.Truth(value)
            case _                      => GroupKind.Closed
        case _ => GroupKind.Closed

  /** The kind of an application of closed terms of the kinds given. */
  def applicationKind(function: GroupKind, argument: GroupKind): GroupKind =
    (function, argument) match
      case (GroupKind.Native(name, places, supplied), operand)
          if operandKind(operand) =>
        if supplied + 1 == places then GroupKind.Value
        else GroupKind.Native(name, places, supplied + 1)
      case (GroupKind.Fixpoint, GroupKind.Thunk(_, true, holes)) =>
        if holes == 1 then GroupKind.Value
        else GroupKind.FixpointApplied(holes - 1, 0)
      case (GroupKind.FixpointApplied(parameters, supplied), operand)
          if operandKind(operand) =>
        if supplied + 1 == parameters then GroupKind.Value
        else GroupKind.FixpointApplied(parameters, supplied + 1)
      case (GroupKind.Thunk(true, _, 1), operand) if operandKind(operand) =>
        GroupKind.Value
      // The binary naturals' criterion constructor, whose parameter is a
      // boolean (P6), reads its argument as one: a Scott boolean by its
      // structure, or a constant by its binding as the booleans' constructor,
      // which the backend's check (`BooleanFamily.constructorsShape`) has found
      // to be that Scott boolean. A criterion of another family is no
      // natural's filter, whatever its parameter is.
      case (
            GroupKind.CriterionFunction(Some(family), Some(parameter)),
            GroupKind.Truth(value)
          )
          if family == BinaryNaturalFamily.identity && parameter == BooleanFamily.identity =>
        GroupKind.Criterion(value)
      case (
            GroupKind.CriterionFunction(Some(family), Some(parameter)),
            GroupKind.Constant(bindings)
          )
          if family == BinaryNaturalFamily.identity && parameter == BooleanFamily.identity =>
        bindings
          .collectFirst {
            case NativeName.Constructor(family, position)
                if family == BooleanFamily.identity =>
              position
          }
          .fold(GroupKind.Closed)(position =>
            GroupKind.Criterion(position == BooleanCodec.position(true))
          )
      // A boolean bound once, as the booleans' constructor of no field, is a
      // native of no operand whose result is a truth value (`nameKind`), the
      // library's false among them: read as that constructor, as a constant of
      // several bindings is.
      case (
            GroupKind.CriterionFunction(Some(family), Some(parameter)),
            GroupKind.TruthNative(
              NativeName.Constructor(constructorFamily, position),
              0
            )
          )
          if family == BinaryNaturalFamily.identity && parameter == BooleanFamily.identity && constructorFamily == BooleanFamily.identity =>
        GroupKind.Criterion(position == BooleanCodec.position(true))
      case (
            GroupKind.DeclaredCriterion(family, arity, supplied),
            GroupKind.Criterion(true)
          ) if supplied < arity =>
        GroupKind.DeclaredCriterion(family, arity, supplied + 1)
      // The array lists' criterion applied to a naturals' criterion, or to the
      // criterion of a family held as a JVM `int`.
      case (GroupKind.ListCriterionFunction, GroupKind.Criterion(admitsZero)) =>
        GroupKind.ListCriterion(GroupGrammar.naturals(admitsZero))
      case (GroupKind.ListCriterionFunction, GroupKind.IntCriterion(family)) =>
        GroupKind.ListCriterion(GroupRepresentation.IntOf(family))
      case _ => GroupKind.Closed

  /** The kind of a parallel of closed terms of the kinds given: a natural
    * filtered by a criterion is a natural; anything else is a closed term,
    * decoded where an operand reads it.
    */
  def parallelKind(left: GroupKind, right: GroupKind): GroupKind = right match
    case GroupKind.Criterion(_) if operandKind(left) => GroupKind.Value
    case _                                           => GroupKind.Closed

  /** The kind of a choice: the kind of its chosen member (`chosenMember`), else
    * no narrow kind.
    */
  def choiceKind(members: Vector[GroupKind]): GroupKind =
    chosenMember(members).fold(GroupKind.Closed)(members(_))

  /** The member of a choice the backend compiles: the first of a narrow kind,
    * the members those of the choice's whole right `+` spine searched left to
    * right, the order the member list had before the choice became binary (of a
    * layer over two kinds, its left side then its right, the right side's own
    * kind already its chosen member's). A lemma should not rely on this
    * position: commutativity, if it is ever applied to the choice, makes the
    * order no longer the author's. The others are dropped, which loses answers
    * only and never adds one: M + N ⊑ M, so M + N ⊑_O M, and an answer N0 of M,
    * M ⊑_O N0, is one of M + N; and C[M] refines C[M + N] in every context
    * (application is monotone by (8) and (10)); the backend may drop the
    * members it does not compile, the untyped ones among them. Which member is
    * the typed branch is not read: no marker is recognized.
    *
    * FIXME: the first narrow member by position is taken and the
    * https://github.com/Atry/private-overlay/issues/2032 others are dropped, a
    * choice fixed here. Which member to compile is to become an option of one
    * interface chosen by configuration (entry data and `Defaults`).
    */
  def chosenMember(members: Vector[GroupKind]): Option[Int] =
    members.indexWhere(narrow) match
      case -1    => None
      case found => Some(found)

  /** Whether the kind is one of the grammar's productions. */
  def narrow(kind: GroupKind): Boolean = kind != GroupKind.Closed

  /** Whether a term of the kind may be an operand of a closed term's
    * application, for the kind of that application: a natural, a closed term, a
    * native of no operands, or a constant of several families. A block reads
    * each of the last three where it stands as a closed term, which it reads
    * only when it is a storage (`GroupCompilation`).
    */
  private def operandKind(kind: GroupKind): Boolean = kind match
    case GroupKind.Value | GroupKind.Closed | GroupKind.Native(_, 0, 0) |
        GroupKind.Constant(_) =>
      true
    case _ => false

  /** The kind of a closed thunk whose fillings are the items given: a function
    * when its body is an expression with every hole a parameter, a recursion's
    * body when it is one with its first hole the recursion.
    */
  def thunkKind[Closed](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[GroupItem[Closed]]
  ): GroupKind =
    (holes, code.layer) match
      case (Vector(Hole.Bound(first), Hole.Ignored), ir.Slot(slot))
          if slot == first =>
        GroupKind.Truth(true)
      case (Vector(Hole.Ignored, Hole.Bound(second)), ir.Slot(slot))
          if slot == second =>
        GroupKind.Truth(false)
      case _ => functionKind(code, holes, fillings)

  private def functionKind[Closed](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[GroupItem[Closed]]
  ): GroupKind =
    if holes.isEmpty then GroupKind.Closed
    else
      val function = body(code, holes, fillings, recursion = false).isDefined
      val recursion = body(code, holes, fillings, recursion = true).isDefined
      if function || recursion then
        GroupKind.Thunk(function, recursion, holes.size)
      else GroupKind.Closed

  /** The expression of a closed thunk's body, its holes bound to binders
    * numbered from 0 in lambda order, the first the recursion when `recursion`.
    */
  def body[Closed](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[GroupItem[Closed]],
      recursion: Boolean
  ): Option[GroupExpression[Closed]] =
    explained(code, holes, fillings, recursion).toOption

  /** The expression of the body as `body` reads it, or where and why it is not
    * one: the first code of the walk that no production reads.
    */
  def explained[Closed](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[GroupItem[Closed]],
      recursion: Boolean
  ): Either[String, GroupExpression[Closed]] =
    val holeItems = holes.indices.toVector.map(position =>
      // A recursion's parameters are values its calls bind, as a let binds
      // its binder; a block's are its entries, read only under a filter.
      if recursion && position == 0 then
        GroupItem.Recursion(position, holes.size - 1)
      else if recursion then GroupItem.Parameter(position)
      else GroupItem.Entry(position)
    )
    expression(code, environment(holes, holeItems, fillings), holes.size).map(
      _._1
    )

  /** A slot's item described for a reason. */
  private def described[Closed](item: Option[GroupItem[Closed]]): String =
    item match
      case Some(GroupItem.Known(kind, _))    => kind.toString
      case Some(GroupItem.Entry(binder))     => s"the block's parameter $binder"
      case Some(GroupItem.Parameter(binder)) => s"parameter $binder"
      case Some(GroupItem.FilteredParameter(binder, representation)) =>
        s"parameter $binder filtered as $representation"
      case Some(GroupItem.Recursion(binder, count)) =>
        s"recursion $binder of $count"
      case None => "no item"

  private def environment[Closed](
      holes: Vector[Hole],
      holeItems: Vector[GroupItem[Closed]],
      fillings: Vector[GroupItem[Closed]]
  ): Map[Int, GroupItem[Closed]] =
    Defunctionalization
      .slotValues(holes, holeItems, fillings)
      .zipWithIndex
      .map(_.swap)
      .toMap

  /** The expression of the code under the environment, and the next binder
    * number free.
    */
  private def expression[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(GroupItem.Known(GroupKind.Value, closed)) =>
            Right((GroupExpression.Value(closed), nextBinder))
          // A closed term written in the block is a constant column, as it
          // is where an operand stands (`operand`); the compilation admits
          // the block only when it is a storage of a natural, so that a
          // choice's constant member is read with the choice, never dropped.
          case Some(
                GroupItem.Known(
                  GroupKind.Closed | GroupKind.Native(_, 0, 0) |
                  GroupKind.Constant(_),
                  closed
                )
              ) =>
            Right((GroupExpression.Literal(closed), nextBinder))
          case other =>
            Left(s"an expression is the slot $slot, a ${described(other)}")
      // Only a natural's filter: an expression is a natural, and a filter
      // of another representation is read where an operand stands. A
      // list read as an expression made a block or a function whose value
      // is a list, and a block whose value is no natural gives none, which
      // makes its whole program's route give no program.
      case ir.Parallel(value, criterion)
          if naturalFilterRead(criterion, environment).isDefined =>
        filtered(value, criterion, environment, nextBinder)
      case ir.Parallel(value, criterion)
          if declaredFilterRead(criterion, environment).isDefined =>
        constructed(value, criterion, environment, nextBinder)
      case ir.Parallel(value, criterion)
          if listFilterRead(criterion, environment).isDefined =>
        filtered(value, criterion, environment, nextBinder)
      case ir.Parallel(value, criterion)
          if intCriterionRead(criterion, environment).isDefined =>
        filtered(value, criterion, environment, nextBinder)
      case ir.Apply(_, _) =>
        val (head, arguments) = Spine.of(code)
        application(head, arguments, environment, nextBinder)
      // A choice of two expressions is their union; a choice with one member
      // an expression is that member alone (the class's documentation).
      case ir.Choice(left, right) =>
        expression(left, environment, nextBinder) match
          case Right((leftExpression, afterLeft)) =>
            expression(right, environment, afterLeft) match
              case Right((rightExpression, afterRight)) =>
                Right(
                  (
                    GroupExpression.Choice(leftExpression, rightExpression),
                    afterRight
                  )
                )
              case Left(_) => Right((leftExpression, afterLeft))
          case Left(leftReason) =>
            expression(right, environment, nextBinder).left.map(rightReason =>
              s"a choice of no expression: $leftReason; $rightReason"
            )
      case other =>
        Left(s"an expression is ${other.getClass.getSimpleName}: $other")

  /** A natural's filter of a block's code: the binary naturals' criterion at
    * the parameter true, which admits every canonical natural, read as the
    * naturals; at false, which admits every one but zero, read as the positive
    * naturals; none for any other code.
    */
  private def naturalFilterRead[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[GroupRepresentation] =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot).collect {
          case GroupItem.Known(GroupKind.Criterion(admitsZero), _) =>
            GroupGrammar.naturals(admitsZero)
        }
      case _ => None

  /** A boolean's filter of a block's code: `boolean_type`. */
  private def booleanCriterionRead[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Boolean =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot).exists {
          case GroupItem.Known(GroupKind.BooleanCriterion, _) => true
          case _                                              => false
        }
      case _ => false

  /** The filter of a block's code by a criterion its facts represent in a codec
    * that holds its values as a JVM `int` (I1, `jvm_int_type` among them): the
    * family; none for any other code.
    */
  private def intCriterionRead[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[FamilyIdentity] =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot).collect {
          case GroupItem.Known(GroupKind.IntCriterion(family), _) => family
        }
      case _ => None

  /** The representation a filter of a block's code reads its value in: a
    * natural's filter (`naturalFilterRead`), a boolean's
    * (`booleanCriterionRead`), a list's (`listFilterRead`) or a 32-bit value
    * held as an `int`'s (`intCriterionRead`); none for any other code.
    */
  private def filterRead[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[GroupRepresentation] =
    naturalFilterRead(code, environment)
      .orElse(
        Option.when(booleanCriterionRead(code, environment))(
          GroupRepresentation.Truth
        )
      )
      .orElse(listFilterRead(code, environment))
      .orElse(
        intCriterionRead(code, environment).map(GroupRepresentation.IntOf(_))
      )

  /** An array list's filter of a block's code, `array_list E`: a slot holding
    * it closed, or the array lists' criterion applied to a slot holding a
    * naturals' criterion or the criterion of a family held as a JVM `int`; none
    * for any other code.
    */
  private def listFilterRead[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[GroupRepresentation] =
    def slotKind(of: Code): Option[GroupKind] = of.layer match
      case ir.Slot(slot) =>
        environment.get(slot).collect { case GroupItem.Known(kind, _) => kind }
      case _ => None
    code.layer match
      case ir.Slot(_) =>
        slotKind(code).collect { case GroupKind.ListCriterion(element) =>
          GroupRepresentation.ListOf(element)
        }
      case ir.Apply(function, element) =>
        (slotKind(function), slotKind(element)) match
          case (
                Some(GroupKind.ListCriterionFunction),
                Some(GroupKind.Criterion(admitsZero))
              ) =>
            Some(GroupRepresentation.ListOf(GroupGrammar.naturals(admitsZero)))
          case (
                Some(GroupKind.ListCriterionFunction),
                Some(GroupKind.IntCriterion(family))
              ) =>
            Some(GroupRepresentation.ListOf(GroupRepresentation.IntOf(family)))
          case _ => None
      case _ => None

  /** A declared family's filter of a block's code, `T a1 … ak`: T a slot
    * holding the criterion of a declared family of arity k, or of one already
    * applied to some of its parameters, and each ai a slot holding the
    * canonical naturals' criterion, as many as T still takes. The family, and
    * the closed terms of T and of each ai, in order; none for any other code.
    */
  private def declaredFilterRead[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[(FamilyIdentity, Vector[Closed])] =
    val (head, arguments) = Spine.of(code)
    def slotItem(of: Code): Option[GroupItem[Closed]] = of.layer match
      case ir.Slot(slot) => environment.get(slot)
      case _             => None
    slotItem(head).flatMap {
      case GroupItem.Known(
            GroupKind.DeclaredCriterion(family, arity, supplied),
            closed
          ) if supplied + arguments.size == arity =>
        val parameters = arguments.map(argument =>
          slotItem(argument).collect {
            case GroupItem.Known(GroupKind.Criterion(true), parameter) =>
              parameter
          }
        )
        Option.when(parameters.forall(_.isDefined))(
          (family, closed +: parameters.flatten)
        )
      case _ => None
    }

  /** A declared family's value, `C e1 … en ∥ T a1 … ak` with the filter one
    * `declaredFilterRead` reads and C a slot holding the constructor of that
    * family at some position, applied to its fields' count of operands.
    */
  private def constructed[Closed](
      value: Code,
      criterion: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    val (head, arguments) = Spine.of(value)
    for
      (family, filter) <- declaredFilterRead(criterion, environment).toRight(
        s"no declared family's filter: $criterion"
      )
      (position, term) <- (head.layer match
        case ir.Slot(slot) =>
          environment.get(slot) match
            case Some(
                  GroupItem.Known(
                    GroupKind.Native(
                      NativeName.Constructor(`family`, position),
                      places,
                      0
                    ),
                    term
                  )
                ) if places == arguments.size =>
              Right((position, term))
            // A constant bound to several families' constructors is read here
            // by the family the filter names.
            case Some(GroupItem.Known(GroupKind.Constant(bindings), term))
                if arguments.isEmpty =>
              bindings
                .collectFirst {
                  case NativeName.Constructor(found, position)
                      if found == family =>
                    (position, term)
                }
                .toRight(
                  s"a constant of no constructor of the filter's family: $bindings"
                )
            case other =>
              Left(
                s"a declared family's value is no constructor of it applied to its fields: ${described(other)}"
              )
        case other =>
          Left(
            s"a declared family's value is no constructor of it applied to its fields: $other"
          )
      )
      (fields, after) <- operands(arguments, environment, nextBinder)
    yield (
      GroupExpression.Constructed(family, position, term, filter, fields),
      after
    )

  /** A filtered value, `v ∥ c` with c a filter `filterRead` reads: the value as
    * an operand, checked where the filter stands (`GroupExpression.Filtered`).
    */
  private def filtered[Closed](
      value: Code,
      criterion: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    filterRead(criterion, environment) match
      case Some(GroupRepresentation.ListOf(element))
          if listConstructorHead(value, environment).isDefined =>
        listConstructed(value, element, environment, nextBinder)
      case Some(representation) =>
        filteredOperand(value, environment, nextBinder).map((read, after) =>
          (GroupExpression.Filtered(read, representation), after)
        )
      case None => Left(s"no filter a block reads: $criterion")

  /** The closed term at the head of a value an array list's filter may read as
    * a constructor: a slot holding a closed term of no kind the grammar calls
    * or computes (a closed term, a boolean by its structure, as the library's
    * nil is, or a constant of several bindings), applied to no operand or to
    * two, the arities of the array lists' nil and cons, which
    * `GroupCompilation` checks it is.
    */
  private def listConstructorHead[Closed](
      value: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[Closed] =
    val (head, arguments) = Spine.of(value)
    head.layer match
      case ir.Slot(slot) if arguments.size == 0 || arguments.size == 2 =>
        environment.get(slot).collect {
          case GroupItem.Known(
                GroupKind.Closed | GroupKind.Truth(_) | GroupKind.Constant(_),
                closed
              ) =>
            closed
        }
      case _ => None

  /** An array list's constructor applied to its operands under the array lists'
    * filter.
    */
  private def listConstructed[Closed](
      value: Code,
      element: GroupRepresentation,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    val (_, arguments) = Spine.of(value)
    for
      constructor <- listConstructorHead(value, environment).toRight(
        s"no array list's constructor: $value"
      )
      (fields, after) <- operands(arguments, environment, nextBinder)
    yield (GroupExpression.ListConstructed(constructor, fields, element), after)

  /** The operand under a filter: a block's parameter, which the grammar reads
    * only here, or any operand.
    */
  private def filteredOperand[Closed](
      value: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    value.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(GroupItem.Entry(binder)) =>
            Right((GroupExpression.Variable(binder), nextBinder))
          case _ => operand(value, environment, nextBinder)
      case _ => operand(value, environment, nextBinder)

  /** An operand: a filtered or bare binder that is no recursion, a closed term,
    * a native of no operands read as its literal (`operandKind`), or an
    * expression.
    */
  private def operand[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    code.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(GroupItem.Entry(binder)) =>
            Left(s"the block's parameter $binder outside a filter")
          case Some(GroupItem.Parameter(binder)) =>
            Right((GroupExpression.Variable(binder), nextBinder))
          case Some(GroupItem.FilteredParameter(binder, _)) =>
            Right((GroupExpression.Variable(binder), nextBinder))
          case Some(GroupItem.Known(GroupKind.Value, closed)) =>
            Right((GroupExpression.Value(closed), nextBinder))
          case Some(GroupItem.Known(GroupKind.Closed, closed)) =>
            Right((GroupExpression.Literal(closed), nextBinder))
          case Some(GroupItem.Known(GroupKind.Native(_, 0, 0), closed)) =>
            Right((GroupExpression.Literal(closed), nextBinder))
          case Some(GroupItem.Known(GroupKind.Constant(_), closed)) =>
            Right((GroupExpression.Literal(closed), nextBinder))
          case other =>
            Left(s"an operand is the slot $slot, a ${described(other)}")
      case ir.Parallel(value, criterion)
          if filterRead(criterion, environment).isDefined =>
        filtered(value, criterion, environment, nextBinder)
      case _ =>
        closedSlots(code, environment) match
          case Some(closedEnvironment) =>
            Right(
              (GroupExpression.ClosedCode(code, closedEnvironment), nextBinder)
            )
          case None => expression(code, environment, nextBinder)

  /** The closed terms of the slots a code reads, an inner thunk's fillings
    * included, when every one holds a closed term of no narrow kind and no
    * binder: the code is then a closed term of the block, decoded where it is
    * an operand.
    */
  private def closedSlots[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]]
  ): Option[Map[Int, Closed]] =
    def slotsRead(of: Code): Vector[Int] = of.layer match
      case ir.Slot(slot)                => Vector(slot)
      case ir.Apply(function, argument) =>
        slotsRead(function) ++ slotsRead(argument)
      case ir.Parallel(left, right) => slotsRead(left) ++ slotsRead(right)
      case ir.Choice(left, right)   => slotsRead(left) ++ slotsRead(right)
      case ir.Thunk(_, _, fillings) => fillings.flatMap(slotsRead)
    val read = slotsRead(code).distinct.map(slot =>
      environment.get(slot).collect {
        case GroupItem.Known(GroupKind.Closed, closed) => slot -> closed
      }
    )
    Option.when(read.forall(_.isDefined))(read.flatten.toMap)

  private def operands[Closed](
      codes: Vector[Code],
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (Vector[GroupExpression[Closed]], Int)] =
    codes.foldLeft(
      Right((Vector.empty[GroupExpression[Closed]], nextBinder)): Either[
        String,
        (Vector[GroupExpression[Closed]], Int)
      ]
    ) { (sofar, code) =>
      sofar.flatMap((done, next) =>
        operand(code, environment, next).map((made, after) =>
          (done :+ made, after)
        )
      )
    }

  private def application[Closed](
      head: Code,
      arguments: Vector[Code],
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    head.layer match
      case ir.Slot(slot) =>
        environment.get(slot) match
          case Some(GroupItem.Known(GroupKind.Native(name, places, 0), _))
              if arguments.size == places =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (GroupExpression.Native(name, made), after)
            )
          case Some(GroupItem.Known(GroupKind.TruthNative(name, places), _))
              if arguments.size == places =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (GroupExpression.Native(name, made), after)
            )
          // A native of a boolean applied to its places and then to the
          // boolean's two cases: the native's value is a Scott boolean, so
          // by the β rule the application is the case it selects.
          case Some(GroupItem.Known(GroupKind.TruthNative(name, places), _))
              if arguments.size == places + 2 =>
            operands(arguments.take(places), environment, nextBinder).flatMap(
              (made, afterOperands) =>
                branched(
                  GroupExpression.Native(name, made),
                  GroupRepresentation.Truth,
                  arguments.drop(places),
                  environment,
                  afterOperands
                )
                  .getOrElse(
                    Left(
                      s"a boolean native's cases are not two: ${arguments.size - places}"
                    )
                  )
            )
          case Some(
                GroupItem.Known(
                  GroupKind.Native(name, places, supplied),
                  closed
                )
              ) if supplied > 0 && arguments.size == places - supplied =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (GroupExpression.PartialApplication(closed, made), after)
            )
          case Some(GroupItem.Recursion(_, parameters))
              if arguments.size == parameters =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (GroupExpression.SelfCall(made), after)
            )
          case Some(GroupItem.Known(GroupKind.Thunk(true, _, holes), closed))
              if arguments.size == holes =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (GroupExpression.Call(closed, made), after)
            )
          // A closed `fixpoint G`, hoisted by the front end as one filling
          // (none of its operands supplied yet), is a partial application
          // too: the compiler's reader takes the body G from its spine
          // (`NarrowBlockCompilation`'s `fullCalls`). Read as a recursion's
          // call of the application itself, its body did not read, and
          // `fixpoint G b` in a block's code made no block.
          case Some(
                GroupItem.Known(
                  GroupKind.FixpointApplied(parameters, supplied),
                  closed
                )
              ) if arguments.size == parameters - supplied =>
            operands(arguments, environment, nextBinder).map((made, after) =>
              (GroupExpression.PartialApplication(closed, made), after)
            )
          case Some(GroupItem.Known(GroupKind.Fixpoint, _)) =>
            arguments.headOption.map(_.layer) match
              case Some(ir.Slot(bodySlot)) =>
                environment.get(bodySlot) match
                  case Some(
                        GroupItem.Known(GroupKind.Thunk(_, true, holes), closed)
                      ) if arguments.size == holes =>
                    operands(arguments.tail, environment, nextBinder).map(
                      (made, after) =>
                        (GroupExpression.RecursionCall(closed, made), after)
                    )
                  case other =>
                    Left(
                      s"the fixed point combinator is applied to a ${described(other)}"
                    )
              case other =>
                Left(s"the fixed point combinator is applied to $other")
          case Some(GroupItem.FilteredParameter(binder, representation)) =>
            branched(
              GroupExpression.Variable(binder),
              representation,
              arguments,
              environment,
              nextBinder
            )
              .getOrElse(
                Left(
                  s"a $representation's branch on the filtered parameter $binder has ${arguments.size} cases"
                )
              )
          case other =>
            Left(
              s"the head of an application of ${arguments.size} is the slot $slot, a ${described(other)}"
            )
      case ir.Parallel(value, criterion) =>
        filterRead(criterion, environment) match
          case Some(representation) =>
            // The branch reads the filtered value, so the filter stays on the
            // scrutinee: rows outside its representation have no case.
            filteredOperand(value, environment, nextBinder).flatMap(
              (scrutinee, afterScrutinee) =>
                branched(
                  GroupExpression.Filtered(scrutinee, representation),
                  representation,
                  arguments,
                  environment,
                  afterScrutinee
                )
                  .getOrElse(
                    Left(
                      s"a $representation's branch has ${arguments.size} cases"
                    )
                  )
            )
          case None =>
            Left(
              s"the head of an application of ${arguments.size} is a parallel of no filter a block reads: $criterion"
            )
      case ir.Thunk(inner, holes, fillings)
          if holes.nonEmpty && arguments.size == holes.size =>
        let(inner, holes, fillings, arguments, environment, nextBinder)
      case other =>
        Left(s"the head of an application of ${arguments.size} is $other")

  /** A branch on the scrutinee, read as the filter's representation reads one,
    * when the cases are as many as the representation's constructors:
    * `z (λh. a) (λh. b)` of a natural, `x y` of a boolean; none otherwise.
    */
  private def branched[Closed](
      scrutinee: GroupExpression[Closed],
      representation: GroupRepresentation,
      arguments: Vector[Code],
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Option[Either[String, (GroupExpression[Closed], Int)]] =
    representation match
      case GroupRepresentation.Natural | GroupRepresentation.Positive
          if arguments.size == 3 =>
        Some(
          for
            (zero, afterZero) <- operand(arguments(0), environment, nextBinder)
            (evenHalf, even, afterEven) <- branch(
              arguments(1),
              environment,
              afterZero
            )
            (oddHalf, odd, afterOdd) <- branch(
              arguments(2),
              environment,
              afterEven
            )
          yield (
            GroupExpression
              .Branch(scrutinee, zero, evenHalf, even, oddHalf, odd),
            afterOdd
          )
        )
      case GroupRepresentation.Truth if arguments.size == 2 =>
        Some(
          for
            (whenTrue, afterTrue) <- operand(
              arguments(BooleanCodec.position(true)),
              environment,
              nextBinder
            )
            (whenFalse, afterFalse) <- operand(
              arguments(BooleanCodec.position(false)),
              environment,
              afterTrue
            )
          yield (
            GroupExpression.Select(scrutinee, whenTrue, whenFalse),
            afterFalse
          )
        )
      // A Scott list `λn c. n` or `λn c. c h t`: the empty case, then the
      // cons case's lambda of the head and the tail.
      case GroupRepresentation.ListOf(_) if arguments.size == 2 =>
        Some(
          for
            (nil, afterNil) <- operand(arguments(0), environment, nextBinder)
            (head, tail, cons, afterCons) <- consCase(
              arguments(1),
              environment,
              afterNil
            )
          yield (
            GroupExpression.ListBranch(scrutinee, nil, head, tail, cons),
            afterCons
          )
        )
      case _ => None

  /** A let of the thunk's holes, `(λx1 … λxn. b) e1 … en`, the front end's
    * spelling of n nested lets: each value an operand, bound in order, a value
    * that is a filtered operand `e ∥ c` binding a filtered parameter
    * (`GroupItem.FilteredParameter`), then the body under all n.
    */
  private def let[Closed](
      inner: Code,
      holes: Vector[Hole],
      fillings: Vector[Code],
      arguments: Vector[Code],
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (GroupExpression[Closed], Int)] =
    val start: Either[
      String,
      (Vector[(Int, GroupExpression[Closed], GroupItem[Closed])], Int)
    ] = Right((Vector.empty, nextBinder))
    arguments
      .foldLeft(start)((sofar, argument) =>
        sofar.flatMap((bound, next) =>
          operand(argument, environment, next).map((value, afterValue) =>
            val item = argument.layer match
              case ir.Parallel(_, criterion) =>
                filterRead(criterion, environment).fold(
                  GroupItem.Parameter(afterValue)
                )(GroupItem.FilteredParameter(afterValue, _))
              case _ => GroupItem.Parameter(afterValue)
            (bound :+ (afterValue, value, item), afterValue + 1)
          )
        )
      )
      .flatMap((bound, afterValues) =>
        for
          innerEnvironment <- innerEnvironment(
            inner,
            holes,
            fillings,
            bound.map(_._3),
            environment
          )
          (body, afterBody) <- expression(inner, innerEnvironment, afterValues)
        yield (
          bound.foldRight(body)((binding, made) =>
            GroupExpression.Let(binding._1, binding._2, made)
          ),
          afterBody
        )
      )

  /** A list's branch's cons case, a lambda of two holes: the binders of the
    * head and of the tail, and its body.
    */
  private def consCase[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (Int, Int, GroupExpression[Closed], Int)] =
    code.layer match
      case ir.Thunk(inner, holes @ Vector(_, _), fillings) =>
        for
          innerEnvironment <- innerEnvironment(
            inner,
            holes,
            fillings,
            Vector(
              GroupItem.Parameter(nextBinder),
              GroupItem.Parameter(nextBinder + 1)
            ),
            environment
          )
          (body, after) <- expression(inner, innerEnvironment, nextBinder + 2)
        yield (nextBinder, nextBinder + 1, body, after)
      case other =>
        Left(s"a list's cons case is no lambda of two holes: $other")

  /** A branch's lambda of one hole, its half's binder and its body. */
  private def branch[Closed](
      code: Code,
      environment: Map[Int, GroupItem[Closed]],
      nextBinder: Int
  ): Either[String, (Int, GroupExpression[Closed], Int)] =
    code.layer match
      case ir.Thunk(inner, Vector(hole), fillings) =>
        for
          innerEnvironment <- innerEnvironment(
            inner,
            Vector(hole),
            fillings,
            Vector(GroupItem.Parameter(nextBinder)),
            environment
          )
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
      holeItems: Vector[GroupItem[Closed]],
      environment: Map[Int, GroupItem[Closed]]
  ): Either[String, Map[Int, GroupItem[Closed]]] =
    val fillingItems = fillings.map(_.layer match
      case ir.Slot(slot) => environment.get(slot)
      case _             => None)
    Either.cond(
      fillingItems.forall(_.isDefined),
      GroupGrammar.environment(holes, holeItems, fillingItems.flatten),
      s"an inner thunk's fillings are not slots: ${fillings.map(_.layer)}"
    )
