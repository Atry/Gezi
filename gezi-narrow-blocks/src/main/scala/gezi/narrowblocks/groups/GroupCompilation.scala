package gezi.narrowblocks.groups

import java.math.BigInteger
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.StorageEncodingOperations
import gezi.jit.BinaryNaturalFamily
import gezi.jit.BinaryNaturalNatives
import gezi.jit.BinaryNaturalStorage
import gezi.jit.ConstructedNaturals
import gezi.jit.CriterionParameters
import gezi.jit.FamilyIdentity
import gezi.jit.NativeBackend
import gezi.jit.NativeName
import gezi.jit.NativePlace
import gezi.jit.Representation
import gezi.jit.StaticBlockMethod
import gezi.narrowblocks.NarrowBlockExtractor
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{Configured, NativeSpecializer}

/** What a group block's values are, known from its body's syntax: binary
  * naturals, truth values, values of one declared family, each the family's
  * constructor applied to its fields' storages and filtered by `filter`, the
  * family's criterion applied to its parameters as written, or array lists
  * `array_list E` whose elements are of the representation `element`: the
  * canonical naturals, the positive ones, or a family held as a JVM `int`.
  */
enum GroupResult:
  case Natural
  case Truth
  case Constructed(family: FamilyIdentity, filter: Representation[Nothing])
  case List(element: GroupRepresentation)
  case IntOf(family: FamilyIdentity)

/** A written thunk compiled to a group block: its body read by the group
  * grammar (`GroupGrammar`) with its parameters numbered from 0 in lambda
  * order, the representation each parameter is filtered by at its every
  * occurrence (`entries`, which its argument is decoded in at the block's
  * entry), the static method of every native it calls, what its values are, and
  * the JIT's storage encoding, whose array lists the block's lists are.
  */
final case class GroupBlock[C <: NativeSpecializer & Singleton](
    parameters: Int,
    entries: Vector[GroupRepresentation],
    body: GroupExpression[Configured[C]],
    methods: Map[NativeName, GroupMethod],
    result: GroupResult,
    recursionBodies: Vector[GroupRecursion[C]],
    recursionNumber: Map[Configured[C], Int],
    operations: StorageEncodingOperations[C]
)

/** A recursion a block calls, `fixpoint G a1 … an`: G's body read by the group
  * grammar, its first binder the recursion itself and its parameters the
  * binders from 1 to `parameters`, each bound to a call's group of values for
  * that argument.
  */
final case class GroupRecursion[C <: NativeSpecializer & Singleton](
    parameters: Int,
    body: GroupExpression[Configured[C]]
)

/** How a group block's run ended. */
enum GroupEnd:

  /** It finished with its results, a group of one or more values. */
  case Finished(results: Vector[GroupValue])

  /** It stopped with no value: its allowance about to run out, a stop asked
    * for, or a cycle met.
    */
  case Stopped

  /** It stopped with no value on a row it would have to drop: a filter's
    * rejection, a positive cons of zero, a native's or a constructor's row with
    * no value.
    */
  case Rejected

/** What a group block gave (`ended`), and the steps it spent, the recursions'
  * calls it finished and how many of these a dense table holds
  * (`GroupMemoOption.Dense`), however it ended.
  */
final case class GroupOutcome(
    ended: GroupEnd,
    steps: Long,
    finishedCalls: Int,
    denseCalls: Int,
    readBacks: GroupReadBacks
):

  /** The results when the run finished. */
  def results: Option[Vector[GroupValue]] = ended match
    case GroupEnd.Finished(results)           => Some(results)
    case GroupEnd.Stopped | GroupEnd.Rejected => None

  /** Whether the run stopped on a rejected row. */
  def rejected: Boolean = ended == GroupEnd.Rejected

/** What one run of a group program read back from its backend, and its rounds
  * (`GroupProgram`, THE DATA STAYS IN THE BACKEND): the columns its arguments
  * entered as; the calls of `asked` that read back identities and the (row,
  * identity) pairs they read back; the rounds' calls of `keys`; the calls of
  * `rowsAt` and the row numbers they read back; and the exits read by `rows`.
  * On a backend whose data lives on a device each read back is a
  * synchronisation, so these are what a design states and a test derives.
  */
final case class GroupReadBacks(
    rounds: Long,
    entryColumns: Long,
    identityCalls: Long,
    identityPairs: Long,
    keyTables: Long,
    parentReads: Long,
    parentRows: Long,
    exits: Long
)

object GroupReadBacks:
  val none: GroupReadBacks = GroupReadBacks(0, 0, 0, 0, 0, 0, 0, 0)

/** The group blocks of an entry's library and natives: the kinds of the
  * library's names, the compilation of a written thunk, and a block's run.
  *
  * A block is compiled from a written closed thunk's syntax alone: its kind by
  * the group grammar must be a function of its parameters; every native its
  * body or a recursion's calls must have a static method whose result the block
  * can hold (`GroupCompilation.resultHeld`); it calls no closed function other
  * than a recursion `fixpoint G a⃗`, whose parameters and result are of the
  * kinds the filters written in the term give (`recursionResult`); a native's
  * place of positive naturals takes only an operand filtered by the positive
  * naturals' criterion or a constant of their representation; every native's
  * place must be one of naturals, and every operand a natural, a branch on a
  * natural or a boolean must read one, the members of a choice and the cases of
  * a branch must be of one kind, and each field of a declared family's value
  * must be a natural whose representation the family's `data_fields` gives as
  * the canonical naturals' (`GroupResult`). A list is of the kind its
  * `array_list E` gives, E the canonical naturals', the positive ones' or a
  * family's held as a JVM `int`, one whose array lists the encoding makes: an
  * array list's filter reads a list; a native's place `NativePlace.NaturalList`
  * of the canonical naturals takes a list of either naturals', one of the
  * positive naturals only a list of theirs (a positive natural being a
  * canonical one); an array list's constructor is the codec's nil of no operand
  * or its cons of an element and a list of the filter's own E, by the backend's
  * facts (`Codecs.declaredConstructors`). The compilation reads no value and no
  * cost. Its facts are the JIT's own, so that the block's lists are array lists
  * of the JIT's storage encoding and leave the block with no copy.
  */
final case class GroupCompilation(facts: gezi.jit.BackendFacts):

  /** The library's index, read under no facts: the names of a block are the
    * library's pure keys.
    */
  val index: StandardLibraryIndex[NoFacts.type] = facts.index

  /** The natives and families of the backend. */
  val natives: NativeBackend = facts.nativeBackend

  /** The array lists' constructors by their positions in the codec's
    * `data_family`, a backend fact, pure keys; none when the library declares
    * no array lists.
    */
  private[groups] val listConstructors: Vector[Pure] =
    gezi.weakhead.Codecs
      .declaredConstructors(index)
      .collectFirst {
        case (name, terms) if name == Representation.arrayListFamily.name =>
          terms
      }
      .getOrElse(Vector.empty)

  /** The kinds of the library's names, as the narrow blocks read them: the
    * noinline names, the terms natives are bound to, the terms with combinator
    * properties, and the fixed point combinator. A name is a pure key of the
    * facts, the same under every configuration, so the kinds are read once,
    * under no facts.
    */
  val names: Map[Pure, GroupKind] =
    given NoFacts.type = NoFacts
    val noinline = index.withProperty(gezi.standardlibrary.Property.Noinline)
    val bound = NarrowBlockExtractor.boundKeys(index)
    (noinline ++ bound ++ index.combinatorProperties.map(
      _.instruction
    ) :+ GroupGrammar.fixpointByValue).distinct
      .map(key =>
        key -> GroupGrammar
          .nameKind(Configured.fromPure(NoFacts)(key), index, natives)
      )
      .toMap

  /** The block of the written thunk, or none when it is no block, compiled with
    * the encoding's operations of the configuration it is of
    * (`JitConfiguration.operations`), which the block keeps. The names are read
    * as terms of the configuration for this thunk: a table of the
    * configuration's own terms built from the pure keys.
    */
  def compiled[C <: NativeSpecializer & Singleton](
      thunk: Configured[C],
      operations: StorageEncodingOperations[C]
  )(using specializer: C): Option[GroupBlock[C]] =
    if thunk.heldAsLeaf then None
    else
      val namesIn: Map[Configured[C], GroupKind] = names.map((key, kind) =>
        Configured.fromPure[C](specializer)(key) -> kind
      )
      GroupCompiling(this, operations, namesIn).compiled(thunk)

/** The compilation of one written thunk of the configuration `C`: the library's
  * names as terms of `C`, the encoding's operations of `C` its lists are made
  * with, and the backend's natives and facts.
  */
private final class GroupCompiling[C <: NativeSpecializer & Singleton](
    compilation: GroupCompilation,
    operations: StorageEncodingOperations[C],
    names: Map[Configured[C], GroupKind]
)(using specializer: C):

  private def natives: NativeBackend = compilation.natives

  /** The array lists' constructors by their positions in the codec's
    * `data_family`, as terms of `C`.
    */
  private val listConstructors: Vector[Configured[C]] =
    compilation.listConstructors.map(Configured.fromPure(specializer))

  /** The block of the written thunk, or none when it is no block. */
  def compiled(thunk: Configured[C]): Option[GroupBlock[C]] =
    if thunk.heldAsLeaf then None
    else
      thunk.layer match
        case gezi.ir.Thunk(code, holes, fillings) =>
          val kinds = GroupScan.kinds(Vector(thunk), names)
          kinds.get(thunk) match
            case Some(GroupKind.Thunk(true, _, parameters)) =>
              GroupGrammar
                .body(
                  code,
                  holes,
                  fillings.map(filling =>
                    GroupItem.Known(
                      kinds.getOrElse(filling, GroupKind.Closed),
                      filling
                    )
                  ),
                  recursion = false
                )
                .flatMap(body =>
                  recursionsOf(body).flatMap(recursions =>
                    blockOf(parameters, body, recursions)
                  )
                )
            case _ => None
        case _ => None

  /** The recursions the body calls, each compiled from its G's syntax, the
    * recursions their bodies call included; none when one is no recursion the
    * grammar reads.
    */
  private def recursionsOf(
      body: GroupExpression[Configured[C]]
  ): Option[Map[Configured[C], GroupRecursion[C]]] =
    @scala.annotation.tailrec
    def gathered(
        pending: List[Configured[C]],
        found: Map[Configured[C], GroupRecursion[C]]
    ): Option[Map[Configured[C], GroupRecursion[C]]] =
      pending match
        case Nil                                        => Some(found)
        case current :: rest if found.contains(current) => gathered(rest, found)
        case current :: rest                            =>
          recursionOf(current) match
            case Some(recursion) =>
              gathered(
                GroupCompilation.recursionCalls(recursion.body) ::: rest,
                found.updated(current, recursion)
              )
            case None => None
    gathered(GroupCompilation.recursionCalls(body), Map.empty)

  /** The recursion G is, `λself x1 … xn. b`, its body read with the recursion
    * at its first hole.
    */
  private def recursionOf(recursion: Configured[C]): Option[GroupRecursion[C]] =
    if recursion.heldAsLeaf then None
    else
      recursion.layer match
        case gezi.ir.Thunk(code, holes, fillings) if holes.size >= 2 =>
          val kinds = GroupScan.kinds(Vector(recursion), names)
          GroupGrammar
            .body(
              code,
              holes,
              fillings.map(filling =>
                GroupItem
                  .Known(kinds.getOrElse(filling, GroupKind.Closed), filling)
              ),
              recursion = true
            )
            .map(GroupRecursion[C](holes.size - 1, _))
        case _ => None

  /** The block of the body, when its values and every recursion's are known
    * (`resultOf`), every native it or a recursion calls has a static method the
    * block can hold, no call is of a closed function, and every positive place
    * takes an operand the positive naturals' filter licenses or a constant of
    * their representation.
    */
  private def blockOf(
      parameters: Int,
      body: GroupExpression[Configured[C]],
      recursions: Map[Configured[C], GroupRecursion[C]]
  ): Option[GroupBlock[C]] =
    val entries = (0 until parameters).toVector.map(binder =>
      GroupCompilation.entryFilter(body, binder)
    )
    Option
      .when(entries.forall(_.isDefined))(entries.flatten)
      .flatMap(found =>
        resultOf(
          body,
          Typing[C](
            found.zipWithIndex
              .map((representation, binder) =>
                binder -> GroupCompilation.filteredKind(representation)
              )
              .toMap,
            recursions,
            None,
            Set.empty
          )
        )
          .flatMap(result =>
            licensedBlock(parameters, found, body, result, recursions)
          )
      )

  /** `blockOf`'s block of a body whose values are known. */
  private def licensedBlock(
      parameters: Int,
      entries: Vector[GroupRepresentation],
      body: GroupExpression[Configured[C]],
      result: GroupResult,
      recursions: Map[Configured[C], GroupRecursion[C]]
  ): Option[GroupBlock[C]] =
    val bodies = body +: recursions.values.map(_.body).toVector
    val calls = bodies.flatMap(nativeCalls)
    val methods = calls
      .filterNot((name, _) => GroupCompilation.constructors.contains(name))
      .map((name, arguments) => name -> staticMethod(name, arguments.size))
      .toMap
    val positive = calls.flatMap((name, arguments) =>
      natives.natives
        .get(name)
        .toVector
        .flatMap(native =>
          native.parameters.zip(arguments).collect {
            case (NativePlace.Fixed(BinaryNaturalNatives.positive), argument) =>
              argument
          }
        )
    )
    Option.when(
      !bodies.exists(callsClosedFunction) &&
        methods.values.forall(_.isDefined) &&
        bodies.flatMap(GroupCompilation.listElements).forall(listMade) &&
        bodies
          .flatMap(closedTerms)
          .forall(closed => GroupCompilation.constant(closed).isDefined) &&
        positive.forall {
          // The criterion written in the term licenses the place: a filter of
          // the positive naturals stops the block on a zero before the call.
          case GroupExpression.Filtered(_, GroupRepresentation.Positive) => true
          case GroupExpression.Literal(closed)                           =>
            GroupCompilation
              .constant(closed)
              .exists((representation, _) =>
                GroupCompilation.positiveLicensed(representation)
              )
          case GroupExpression.Value(closed) =>
            GroupCompilation
              .constant(closed)
              .exists((representation, _) =>
                GroupCompilation.positiveLicensed(representation)
              )
          case _ => false
        }
    )(
      GroupBlock[C](
        parameters,
        entries,
        body,
        methods.collect { case (name, Some(method)) => name -> method },
        result,
        recursions.values.toVector,
        recursions.keys.toVector.zipWithIndex.toMap,
        operations
      )
    )

  /** What the expression's values are under the typing's binders, when its
    * operands, branches, choices, declared families' fields and recursions are
    * of the kinds `GroupCompilation`'s documentation asks; none otherwise. A
    * recursion's parameters and its result are of the kinds the filters written
    * in the term give, never of a kind assumed and then checked
    * (`recursionResult`).
    */
  private def resultOf(
      expression: GroupExpression[Configured[C]],
      typing: Typing[C]
  ): Option[GroupResult] =
    def kindOf(of: GroupExpression[Configured[C]]): Option[GroupResult] =
      resultOf(of, typing)
    def all(
        expressions: Vector[GroupExpression[Configured[C]]],
        kind: GroupResult
    ): Boolean =
      expressions.forall(kindOf(_).contains(kind))
    def agreed(kinds: Vector[Option[GroupResult]]): Option[GroupResult] =
      kinds.headOption.flatten.filter(first => kinds.forall(_.contains(first)))
    expression match
      case GroupExpression.Variable(binder) => typing.binders.get(binder)
      case GroupExpression.Literal(closed)  =>
        GroupCompilation
          .constant(closed)
          .map((_, value) => GroupCompilation.constantKind(value))
      case GroupExpression.Value(closed) =>
        GroupCompilation
          .constant(closed)
          .map((_, value) => GroupCompilation.constantKind(value))
      case GroupExpression.Native(name, arguments)
          if GroupCompilation.constructors.contains(name) =>
        Option.when(all(arguments, GroupResult.Natural))(GroupResult.Natural)
      case GroupExpression.Native(name, arguments) =>
        natives.natives
          .get(name)
          .flatMap(native =>
            val placed =
              native.parameters.size == arguments.size && native.parameters
                .zip(arguments)
                .forall((place, argument) =>
                  kindOf(argument).exists(GroupCompilation.placeTakes(place, _))
                )
            GroupCompilation
              .resultKind(native.result, natives)
              .filter(_ => placed)
          )
      case GroupExpression.Filtered(
            GroupExpression.RecursionCall(recursion, arguments),
            representation
          ) =>
        recursionResult(recursion, arguments, representation, typing)
      case GroupExpression.Filtered(
            GroupExpression.SelfCall(arguments),
            representation
          ) =>
        typing.self
          .filter((_, filter) => filter == representation)
          .flatMap(_ =>
            Option.when(
              arguments.zipWithIndex.forall((argument, position) =>
                kindOf(argument).exists(found =>
                  typing.selfArgumentKinds
                    .lift(position)
                    .flatten
                    .forall(GroupCompilation.agrees(found, _))
                )
              )
            )(GroupCompilation.filteredKind(representation))
          )
      // An array list's filter reads a list: on a value of another kind (a truth
      // value is nil by its term) the block is not compiled, and the general
      // reading reads the term.
      case GroupExpression.Filtered(
            value,
            GroupRepresentation.ListOf(element)
          ) =>
        kindOf(value)
          .filter(GroupCompilation.agrees(_, GroupResult.List(element)))
          .map(_ => GroupResult.List(element))
      // Any other filter reads a value of its own kind: on a value of another
      // kind (a list under the booleans' criterion, nil being true's term)
      // the block is not compiled, rather than dropping the row.
      case GroupExpression.Filtered(value, representation) =>
        kindOf(value)
          .filter(
            GroupCompilation
              .agrees(_, GroupCompilation.filteredKind(representation))
          )
          .map(_ => GroupCompilation.filteredKind(representation))
      case GroupExpression.Branch(
            scrutinee,
            zero,
            evenHalf,
            even,
            oddHalf,
            odd
          ) =>
        Option
          .when(kindOf(scrutinee).contains(GroupResult.Natural))(())
          .flatMap(_ =>
            agreed(
              Vector(
                kindOf(zero),
                resultOf(
                  even,
                  typing.copy(binders =
                    typing.binders.updated(evenHalf, GroupResult.Natural)
                  )
                ),
                resultOf(
                  odd,
                  typing.copy(binders =
                    typing.binders.updated(oddHalf, GroupResult.Natural)
                  )
                )
              )
            )
          )
      case GroupExpression.Select(scrutinee, whenTrue, whenFalse) =>
        Option
          .when(kindOf(scrutinee).contains(GroupResult.Truth))(())
          .flatMap(_ => agreed(Vector(kindOf(whenTrue), kindOf(whenFalse))))
      case GroupExpression.Let(binder, value, body) =>
        kindOf(value).flatMap(kind =>
          resultOf(
            body,
            typing.copy(binders = typing.binders.updated(binder, kind))
          )
        )
      case GroupExpression.Choice(left, right) =>
        agreed(Vector(kindOf(left), kindOf(right)))
      case GroupExpression.ListBranch(scrutinee, nil, head, tail, cons) =>
        kindOf(scrutinee) match
          case Some(list @ GroupResult.List(element)) =>
            val item = GroupCompilation.filteredKind(element)
            agreed(
              Vector(
                kindOf(nil),
                resultOf(
                  cons,
                  typing.copy(binders =
                    typing.binders.updated(head, item).updated(tail, list)
                  )
                )
              )
            )
          case _ => None
      case GroupExpression.ListConstructed(constructor, fields, element) =>
        val list = GroupResult.List(element)
        val position = listConstructors.indexWhere(found =>
          Configured.same(found, constructor)
        )
        Option.when(fields match
          case Vector() =>
            position == gezi.weakhead.ListCodec.position(
              gezi.weakhead.ListConstructor.Nil
            )
          case Vector(item, rest) =>
            position == gezi.weakhead.ListCodec
              .position(gezi.weakhead.ListConstructor.Cons) &&
            kindOf(item).contains(
              GroupCompilation.filteredKind(element)
            ) && kindOf(rest).contains(list)
          case _ => false)(list)
      case GroupExpression.Constructed(
            family,
            constructor,
            _,
            filter,
            fields
          ) =>
        if all(fields, GroupResult.Natural) && fieldsCanonical(
            family,
            constructor,
            fields.size
          )
        then declaredFilter(family).map(GroupResult.Constructed(family, _))
        else None
      // A recursion's call or a self call is of a kind only under the filter
      // that gives it (the cases above); a closed function's call is no block.
      case GroupExpression.SelfCall(_) | GroupExpression.RecursionCall(_, _) |
          GroupExpression.Call(_, _) |
          GroupExpression.PartialApplication(_, _) |
          GroupExpression.ClosedCode(_, _) =>
        None

  /** The kind of `fixpoint G a1 … an ∥ S`, the kind S gives, when every kind
    * the recursion needs comes from a filter written in the term: each
    * parameter's, either from the same filter T written on its argument at this
    * call and at every self call of G's body, or from the same filter T on its
    * every occurrence in G's body; and G's every self call written under S
    * itself. G's body is then of a kind under those parameters' kinds, the kind
    * S keeps (`agrees`); a parameter whose kind comes from its occurrences is
    * given, at this call and at every self call, arguments of that kind, so
    * that no filter of the body meets a value of another kind (an array list's
    * filter relabels a list and reads nothing else). None otherwise, and for a
    * recursion met again while its own body is read, so that no kind is assumed
    * of a recursion before it is read.
    */
  private def recursionResult(
      recursion: Configured[C],
      arguments: Vector[GroupExpression[Configured[C]]],
      representation: GroupRepresentation,
      typing: Typing[C]
  ): Option[GroupResult] =
    typing.recursions
      .get(recursion)
      .filter(found =>
        found.parameters == arguments.size && !typing.reading
          .contains(recursion)
      )
      .flatMap { found =>
        val selfCalls = GroupCompilation.selfCalls(found.body)
        val parameterKinds = (0 until found.parameters).toVector.map(position =>
          val binder = position + 1
          val atCalls = (arguments(position) +: selfCalls
            .map((callArguments, _) => callArguments(position))).map {
            case GroupExpression.Filtered(_, filter) => Some(filter)
            case _                                   => None
          }
          val atOccurrences =
            GroupCompilation.occurrenceFilters(found.body, binder)
          def same(
              filters: Vector[Option[GroupRepresentation]]
          ): Option[GroupRepresentation] =
            filters.headOption.flatten
              .filter(first => filters.forall(_.contains(first)))
          same(atCalls)
            .map(filter => (GroupCompilation.filteredKind(filter), true))
            .orElse(
              Option
                .when(atOccurrences.nonEmpty)(same(atOccurrences))
                .flatten
                .map(filter => (GroupCompilation.filteredKind(filter), false))
            )
        )
        val argumentKinds = arguments.map(resultOf(_, typing))
        // A parameter typed by its occurrences takes arguments of its kind, at
        // this call here and at every self call where the call is read.
        val required =
          parameterKinds.map(_.collect { case (kind, false) => kind })
        Option
          .when(
            parameterKinds.forall(_.isDefined) &&
              argumentKinds.forall(_.isDefined) &&
              argumentKinds
                .lazyZip(required)
                .forall((found, kind) =>
                  kind.forall(wanted =>
                    found.exists(GroupCompilation.agrees(_, wanted))
                  )
                ) &&
              selfCalls.forall((_, filter) => filter.contains(representation))
          )(())
          .flatMap(_ =>
            resultOf(
              found.body,
              Typing[C](
                parameterKinds.flatten.zipWithIndex.map {
                  case ((kind, _), position) => (position + 1) -> kind
                }.toMap,
                typing.recursions,
                Some((recursion, representation)),
                typing.reading + recursion,
                required
              )
            )
          )
          .filter(
            GroupCompilation
              .agrees(_, GroupCompilation.filteredKind(representation))
          )
          .map(_ => GroupCompilation.filteredKind(representation))
      }

  /** Whether the backend declares the family with a constructor at the position
    * of that many fields, each of the canonical naturals' representation at the
    * family's parameters, every one the canonical naturals' criterion as the
    * grammar reads the filter: the representation `data_fields` gives each
    * field at those parameters, a backend fact.
    */
  private def fieldsCanonical(
      family: FamilyIdentity,
      constructor: Int,
      fields: Int
  ): Boolean =
    natives
      .family(family)
      .exists(declared =>
        declared
          .constructors(None)
          .lift(constructor)
          .exists(found =>
            found.fields.size == fields && found.fields.forall(field =>
              field.representation(
                Some(
                  CriterionParameters(
                    Vector.fill(declared.criterionArity)(
                      BinaryNaturalNatives.canonical
                    )
                  )
                )
              ) ==
                BinaryNaturalNatives.canonical
            )
          )
      )

  /** The representation of the family's values whose parameters are the
    * canonical naturals' criterion, which is the criterion `F c1 … ck` the
    * grammar read at the block's root (`GroupGrammar`, `DeclaredCriterion`:
    * each parameter `binary_set true`): the storage of a value of it is the
    * value's unique spelling under that filter.
    */
  private def declaredFilter(
      family: FamilyIdentity
  ): Option[Representation[Nothing]] =
    natives
      .family(family)
      .map(declared =>
        Representation.Data(
          family,
          Some(
            CriterionParameters(
              Vector
                .fill(declared.criterionArity)(BinaryNaturalNatives.canonical)
            )
          )
        )
      )

  /** Whether the encoding makes the array lists of the element, those a block
    * holds its lists of under `array_list E`.
    */
  private def listMade(element: GroupRepresentation): Boolean =
    operations.converts(GroupBlockMechanism.listRepresentation(element))

  /** The static method of the native on that many operands whose result the
    * block can hold.
    */
  private def staticMethod(
      name: NativeName,
      operands: Int
  ): Option[GroupMethod] =
    natives.natives
      .get(name)
      .filter(_.parameters.size == operands)
      .flatMap(native =>
        native.implementation match
          case method: StaticBlockMethod
              if GroupCompilation.resultHeld(native, method, natives) =>
            val places = native.parameters.map {
              case NativePlace.NaturalList(_) => Some(GroupPlace.NaturalList)
              case place
                  if GroupCompilation.intPlace(place, natives).isDefined =>
                Some(GroupPlace.IntBits)
              case place =>
                Option.when(GroupCompilation.naturalPlace(place))(
                  GroupPlace.Natural
                )
            }
            // A list result is held as an array list of the declared element,
            // which the encoding must make.
            val resultList = native.result match
              case NativePlace.NaturalList(element) =>
                Option.when(
                  operations.converts(Representation.ArrayListOf(element))
                )(
                  Some(
                    GroupListKind(
                      operations,
                      Representation.ArrayListOf(element)
                    )
                  )
                )
              case _ => Some(None)
            Option
              .when(places.forall(_.isDefined))(())
              .flatMap(_ =>
                resultList.map(
                  GroupMethod(
                    name,
                    method,
                    places.flatten,
                    GroupCompilation.intPlace(native.result, natives),
                    _
                  )
                )
              )
          case _ => None
      )

  /** Every call of a native in the expression, with its operands. */
  private def nativeCalls(
      expression: GroupExpression[Configured[C]]
  ): Vector[(NativeName, Vector[GroupExpression[Configured[C]]])] =
    @scala.annotation.tailrec
    def walked(
        pending: List[GroupExpression[Configured[C]]],
        found: Vector[(NativeName, Vector[GroupExpression[Configured[C]]])]
    ): Vector[(NativeName, Vector[GroupExpression[Configured[C]]])] =
      pending match
        case Nil             => found
        case current :: rest =>
          current match
            case GroupExpression.Native(name, arguments) =>
              walked(arguments.toList ::: rest, found :+ (name, arguments))
            case other => walked(GroupCompilation.parts(other) ::: rest, found)
    walked(List(expression), Vector.empty)

  /** The closed terms the expression reads as values. */
  private def closedTerms(
      expression: GroupExpression[Configured[C]]
  ): Vector[Configured[C]] =
    @scala.annotation.tailrec
    def walked(
        pending: List[GroupExpression[Configured[C]]],
        found: Vector[Configured[C]]
    ): Vector[Configured[C]] = pending match
      case Nil                                     => found
      case GroupExpression.Literal(closed) :: rest =>
        walked(rest, found :+ closed)
      case GroupExpression.Value(closed) :: rest =>
        walked(rest, found :+ closed)
      case current :: rest =>
        walked(GroupCompilation.parts(current) ::: rest, found)
    walked(List(expression), Vector.empty)

  /** Whether the expression calls a closed function or reads a closed code,
    * which no group block runs; a recursion's call is read as a recursion.
    */
  private def callsClosedFunction(
      expression: GroupExpression[Configured[C]]
  ): Boolean =
    @scala.annotation.tailrec
    def walked(pending: List[GroupExpression[Configured[C]]]): Boolean =
      pending match
        case Nil => false
        case (GroupExpression.Call(_, _) |
            GroupExpression.PartialApplication(_, _) |
            GroupExpression.ClosedCode(_, _)) :: _ =>
          true
        case current :: rest => walked(GroupCompilation.parts(current) ::: rest)
    walked(List(expression))

/** What `resultOf` reads an expression under: the kinds of its binders, the
  * block's recursions, the recursion whose body it is with the filter its self
  * calls are written under, the kind each of its self calls' arguments must
  * have (`selfArgumentKinds`) where the parameter's kind comes from its
  * occurrences (none for a parameter whose kind comes from the filters at the
  * calls), and the recursions whose bodies are being read.
  */
private final case class Typing[C <: NativeSpecializer & Singleton](
    binders: Map[Int, GroupResult],
    recursions: Map[Configured[C], GroupRecursion[C]],
    self: Option[(Configured[C], GroupRepresentation)],
    reading: Set[Configured[C]],
    selfArgumentKinds: Vector[Option[GroupResult]] = Vector.empty
)

/** The parts and the decoding a group block shares with its run. */
object GroupCompilation:

  /** The element representations of the array lists the expression filters or
    * constructs, at every depth.
    */
  def listElements[Closed](
      expression: GroupExpression[Closed]
  ): List[GroupRepresentation] =
    @scala.annotation.tailrec
    def walked(
        pending: List[GroupExpression[Closed]],
        found: List[GroupRepresentation]
    ): List[GroupRepresentation] = pending match
      case Nil             => found
      case current :: rest =>
        val here = current match
          case GroupExpression.Filtered(
                _,
                GroupRepresentation.ListOf(element)
              ) =>
            List(element)
          case GroupExpression.ListConstructed(_, _, element) => List(element)
          case _                                              => Nil
        walked(parts(current) ::: rest, here ::: found)
    walked(List(expression), Nil)

  /** The immediate subexpressions of an expression. */
  def parts[Closed](
      expression: GroupExpression[Closed]
  ): List[GroupExpression[Closed]] = expression match
    case GroupExpression.Native(_, arguments)             => arguments.toList
    case GroupExpression.PartialApplication(_, arguments) => arguments.toList
    case GroupExpression.Call(_, arguments)               => arguments.toList
    case GroupExpression.SelfCall(arguments)              => arguments.toList
    case GroupExpression.RecursionCall(_, arguments)      => arguments.toList
    case GroupExpression.Branch(scrutinee, zero, _, even, _, odd) =>
      List(scrutinee, zero, even, odd)
    case GroupExpression.Let(_, value, body) => List(value, body)
    case GroupExpression.Filtered(value, _)  => List(value)
    case GroupExpression.Select(scrutinee, whenTrue, whenFalse) =>
      List(scrutinee, whenTrue, whenFalse)
    case GroupExpression.Choice(left, right)             => List(left, right)
    case GroupExpression.Constructed(_, _, _, _, fields) => fields.toList
    case GroupExpression.ListBranch(scrutinee, nil, _, _, cons) =>
      List(scrutinee, nil, cons)
    case GroupExpression.ListConstructed(_, fields, _) => fields.toList
    case GroupExpression.Literal(_) | GroupExpression.ClosedCode(_, _) |
        GroupExpression.Value(_) | GroupExpression.Variable(_) =>
      Nil

  /** Whether a group block holds the native's result as the static method
    * returns it: what every narrow block holds
    * (`StaticBlockMethod.resultHeld`), or a natural at a place of binary
    * naturals that the method may answer is ≃_O `top`
    * (`StaticBlockResult.NaturalOrNoAnswer`). A row on which it so answers
    * stops the block (`GroupProgram`): the application has no normal form, but
    * a context consuming it can have an answer, which a dropped row would lose.
    * A method whose result is a declared family's value
    * (`StaticBlockResult.Constructed`) is not held: a group block builds such a
    * value only by the declared family production, and calls no native that
    * returns one. Nor is a method whose result is a term over naturals
    * (`StaticBlockResult.Lattice`), which no row can hold as one value.
    */
  def resultHeld(
      native: gezi.jit.Native,
      method: StaticBlockMethod,
      natives: NativeBackend
  ): Boolean =
    intHeld(native, method, natives) ||
      StaticBlockMethod.resultHeld(
        native,
        method
      ) || (method.operands == gezi.jit.StaticBlockOperands.Naturals && ((
        native.result,
        method.result
      ) match
        case (
              NativePlace.Fixed(representation),
              gezi.jit.StaticBlockResult.NaturalOrNoAnswer
            ) =>
          representation == StaticBlockMethod.blockNatural || representation == BinaryNaturalNatives.positive
        case (
              NativePlace.NaturalList(element),
              gezi.jit.StaticBlockResult.NaturalList
            ) =>
          element == BinaryNaturalNatives.canonical || element == BinaryNaturalNatives.positive
        case _ => false))

  /** Whether the native is one of values held as a JVM `int` (I2): its every
    * place a family's whose codec holds it as an `int`, its method taking JVM
    * `int`s, and its result such a family's value returned as an `int`, or a
    * truth value returned as a JVM `boolean`.
    */
  private def intHeld(
      native: gezi.jit.Native,
      method: StaticBlockMethod,
      natives: NativeBackend
  ): Boolean =
    method.operands == gezi.jit.StaticBlockOperands.JvmInts &&
      native.parameters.forall(intPlace(_, natives).isDefined) &&
      ((native.result, method.result) match
        case (result, gezi.jit.StaticBlockResult.JvmInt) =>
          intPlace(result, natives).isDefined
        case (
              NativePlace.Fixed(Representation.Truth),
              gezi.jit.StaticBlockResult.Truth
            ) =>
          true
        case _ => false)

  /** The family of a place of a family whose codec holds its values as a JVM
    * `int` and takes no parameter, the JVM type read from the codec
    * (`gezi.jit.DataFamily.jvmPrimitive`); none for any other place.
    */
  def intPlace(
      place: NativePlace,
      natives: NativeBackend
  ): Option[FamilyIdentity] = place match
    case NativePlace.Fixed(Representation.Data(family, None))
        if natives
          .family(family)
          .exists(_.jvmPrimitive.contains(gezi.jit.JvmPrimitive.Int)) =>
      Some(family)
    case _ => None

  /** Whether a value of the kind is one a filter of the other kind reads: the
    * same kind, or two lists of elements of one family, which the filter
    * relabels. Lists of two families (words under the naturals' array lists) do
    * not agree: the block is not compiled or not entered, and the reading reads
    * the term, rather than the block dropping the row.
    */
  def agrees(kind: GroupResult, filtered: GroupResult): Boolean =
    (kind, filtered) match
      case (GroupResult.List(element), GroupResult.List(other)) =>
        elementFamily(element) == elementFamily(other)
      case _ => kind == filtered

  /** The family of an array list's element representation. */
  private def elementFamily(element: GroupRepresentation): FamilyIdentity =
    element match
      case GroupRepresentation.Natural | GroupRepresentation.Positive =>
        BinaryNaturalFamily.identity
      case GroupRepresentation.IntOf(family) => family
      case other                             =>
        throw IllegalStateException(s"no array list's element of $other")

  /** The kind of the values a filter keeps. */
  def filteredKind(representation: GroupRepresentation): GroupResult =
    representation match
      case GroupRepresentation.Natural | GroupRepresentation.Positive =>
        GroupResult.Natural
      case GroupRepresentation.Truth           => GroupResult.Truth
      case GroupRepresentation.ListOf(element) => GroupResult.List(element)
      case GroupRepresentation.IntOf(family)   => GroupResult.IntOf(family)

  /** The bodies of the recursions the expression calls, `fixpoint G a⃗`, by
    * their G.
    */
  def recursionCalls[Closed](
      expression: GroupExpression[Closed]
  ): List[Closed] =
    @scala.annotation.tailrec
    def walked(
        pending: List[GroupExpression[Closed]],
        found: List[Closed]
    ): List[Closed] = pending match
      case Nil => found.reverse
      case GroupExpression.RecursionCall(body, arguments) :: rest =>
        walked(arguments.toList ::: rest, body :: found)
      case current :: rest => walked(parts(current) ::: rest, found)
    walked(List(expression), Nil)

  /** The self calls of a recursion's body, each with its arguments and the
    * filter it is written directly under, none when it is under none.
    */
  def selfCalls[Closed](
      body: GroupExpression[Closed]
  ): Vector[(Vector[GroupExpression[Closed]], Option[GroupRepresentation])] =
    @scala.annotation.tailrec
    def walked(
        pending: List[GroupExpression[Closed]],
        found: Vector[
          (Vector[GroupExpression[Closed]], Option[GroupRepresentation])
        ]
    ): Vector[(Vector[GroupExpression[Closed]], Option[GroupRepresentation])] =
      pending match
        case Nil => found
        case GroupExpression.Filtered(
              GroupExpression.SelfCall(arguments),
              filter
            ) :: rest =>
          walked(arguments.toList ::: rest, found :+ (arguments, Some(filter)))
        case GroupExpression.SelfCall(arguments) :: rest =>
          walked(arguments.toList ::: rest, found :+ (arguments, None))
        case current :: rest => walked(parts(current) ::: rest, found)
    walked(List(body), Vector.empty)

  /** The representation a block's parameter is decoded in at the block's entry:
    * the filter every occurrence of it is written under, when it is one filter,
    * and the parameter is read on every path of the body (`readOnEveryPath`),
    * so that decoding it at the entry is the work the general reading does
    * where it first reads it; none otherwise, and the thunk is no block.
    */
  def entryFilter[Closed](
      body: GroupExpression[Closed],
      binder: Int
  ): Option[GroupRepresentation] =
    val filters = occurrenceFilters(body, binder)
    filters.headOption.flatten.filter(first =>
      filters.forall(_.contains(first)) && readOnEveryPath(body, binder)
    )

  /** Whether every evaluation of the expression reads the binder: an
    * occurrence; an operation, a choice, a let or a call any of whose parts
    * does, every part being evaluated; a branch whose scrutinee does or all of
    * whose cases do.
    */
  def readOnEveryPath[Closed](
      expression: GroupExpression[Closed],
      binder: Int
  ): Boolean =
    def reads(of: GroupExpression[Closed]): Boolean =
      readOnEveryPath(of, binder)
    expression match
      case GroupExpression.Variable(found) => found == binder
      case GroupExpression.Branch(scrutinee, zero, _, even, _, odd) =>
        reads(scrutinee) || (reads(zero) && reads(even) && reads(odd))
      case GroupExpression.Select(scrutinee, whenTrue, whenFalse) =>
        reads(scrutinee) || (reads(whenTrue) && reads(whenFalse))
      case GroupExpression.ListBranch(scrutinee, nil, _, _, cons) =>
        reads(scrutinee) || (reads(nil) && reads(cons))
      case other => parts(other).exists(reads)

  /** The filter each occurrence of the binder in the expression is written
    * directly under, none for an occurrence under none.
    */
  def occurrenceFilters[Closed](
      expression: GroupExpression[Closed],
      binder: Int
  ): Vector[Option[GroupRepresentation]] =
    @scala.annotation.tailrec
    def walked(
        pending: List[GroupExpression[Closed]],
        found: Vector[Option[GroupRepresentation]]
    ): Vector[Option[GroupRepresentation]] =
      pending match
        case Nil => found
        case GroupExpression.Filtered(
              GroupExpression.Variable(`binder`),
              filter
            ) :: rest =>
          walked(rest, found :+ Some(filter))
        case GroupExpression.Variable(`binder`) :: rest =>
          walked(rest, found :+ None)
        case current :: rest => walked(parts(current) ::: rest, found)
    walked(List(expression), Vector.empty)

  /** Whether a native's place is one a group block fills: of the canonical or
    * the positive naturals, the only operands a block's backend calls a static
    * method with (`GroupBackend.called`).
    */
  def naturalPlace(place: NativePlace): Boolean = place match
    case NativePlace.Fixed(representation) =>
      representation == BinaryNaturalNatives.canonical || representation == BinaryNaturalNatives.positive
    case _ => false

  /** Whether an operand of the kind fills the native's place: a natural a place
    * of naturals (a positive one licensed by `licensedBlock`), a list of the
    * canonical naturals' `array_list N` a place `NaturalList` of theirs, and a
    * list of the positive naturals' either such place, every positive natural
    * being a canonical one.
    */
  def placeTakes(place: NativePlace, kind: GroupResult): Boolean =
    (place, kind) match
      case (NativePlace.NaturalList(element), GroupResult.List(listed)) =>
        (element == BinaryNaturalNatives.canonical && (listed == GroupRepresentation.Natural || listed == GroupRepresentation.Positive)) ||
        (element == BinaryNaturalNatives.positive && listed == GroupRepresentation.Positive)
      case (_, GroupResult.Natural) => naturalPlace(place)
      case (
            NativePlace.Fixed(Representation.Data(placeFamily, None)),
            GroupResult.IntOf(family)
          ) =>
        placeFamily == family
      case _ => false

  /** What a native's result is: a natural at a place of naturals, a truth value
    * at one of truth values, a list of naturals at a place `NaturalList` of the
    * canonical or the positive naturals; none for any other result.
    */
  def resultKind(
      place: NativePlace,
      natives: NativeBackend
  ): Option[GroupResult] = place match
    case NativePlace.NaturalList(element)
        if element == BinaryNaturalNatives.canonical =>
      Some(GroupResult.List(GroupRepresentation.Natural))
    case NativePlace.NaturalList(element)
        if element == BinaryNaturalNatives.positive =>
      Some(GroupResult.List(GroupRepresentation.Positive))
    case _ if intPlace(place, natives).isDefined =>
      intPlace(place, natives).map(GroupResult.IntOf(_))
    case _ =>
      if naturalPlace(place) then Some(GroupResult.Natural)
      else
        Option.when(place == NativePlace.Fixed(Representation.Truth))(
          GroupResult.Truth
        )

  /** The value a closed term written in the block is, a storage read by its
    * value: a binary natural's, or one held as a JVM `int` (`IntStorage`, the
    * 32-bit words of `jvm_int` among them), whose every row is the storage
    * itself (I3); the representation the storage's criterion names, and the
    * value. None for any other term: a block reads its constants from storages,
    * the spelling the converting construction gives a filtered value, and never
    * runs a native to make one.
    */
  def constant[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  ): Option[(Representation[Nothing], GroupValue)] =
    (instruction.representation: AnyRef) match
      case storage: BinaryNaturalStorage =>
        Some(
          (
            storage.representation,
            GroupValue.Natural(storage.natural.bigInteger)
          )
        )
      case storage: gezi.jit.IntStorage =>
        storage.representation match
          case Representation.Data(family, None) =>
            Some(
              (storage.representation, GroupValue.IntBits(family, storage.bits))
            )
          case _ => None
      case _ => None

  /** The kind of a constant's value. */
  def constantKind(value: GroupValue): GroupResult = value match
    case GroupValue.Natural(_)         => GroupResult.Natural
    case GroupValue.IntBits(family, _) => GroupResult.IntOf(family)
    case other                         =>
      throw IllegalStateException(
        s"a block's constant is a natural or a value held as an int, not $other"
      )

  /** Whether a natural of the representation may stand at a place of positive
    * naturals: the representation is the positive one, the one a criterion that
    * admits no zero names. A canonical natural, which may be zero, never may,
    * whatever its value: the licence is the criterion's, read per place, never
    * per row.
    */
  def positiveLicensed(representation: Representation[Nothing]): Boolean =
    representation == BinaryNaturalNatives.positive

  /** The binary naturals' constructor natives, which a block reads by their
    * structure and calls no static method of.
    */
  val constructors: Set[NativeName] = Set(
    BinaryNaturalFamily.zeroNative,
    BinaryNaturalFamily.evenNative,
    BinaryNaturalFamily.oddNative
  )

/** A group block's run on a group program backend: its arguments' groups bound
  * to its parameters, its body run as a group program (`GroupProgram`) as the
  * group grammar's guarantees say (`GroupGrammar`), the steps charged as the
  * rows each operation makes, the run stopped with no value before they pass
  * the allowance, at a stop asked for, at a cycle, or on a rejected row
  * (`GroupEnd`).
  */
object GroupRun:

  /** Whether the block may be entered with the arguments, each a group of
    * values read from written storages: one group of one or more values for
    * each parameter, every value of the kind the parameter's filter reads
    * (`GroupCompilation.agrees`). Which of those values a parameter's
    * occurrences keep is the filters' in the block's term
    * (`GroupExpression.Filtered`); a value of another kind (a truth value where
    * the filter reads a list, nil being true's term) is not dropped by the
    * block, which is not entered, the reading reading the term.
    */
  def admitted[C <: NativeSpecializer & Singleton](
      block: GroupBlock[C],
      arguments: Vector[Vector[GroupValue]]
  ): Boolean =
    arguments.size == block.parameters && arguments.forall(_.nonEmpty) &&
      arguments
        .lazyZip(block.entries)
        .forall((group, entry) =>
          group.forall(value =>
            GroupRun
              .kindOf(block, value)
              .exists(
                GroupCompilation.agrees(_, GroupCompilation.filteredKind(entry))
              )
          )
        )

  /** The kind of a value an argument holds, a list's by its elements'
    * representation; none for a list of another encoding than the block's, for
    * a value of a declared family and for a row number, which no parameter's
    * filter reads.
    */
  private def kindOf[C <: NativeSpecializer & Singleton](
      block: GroupBlock[C],
      value: GroupValue
  ): Option[GroupResult] = value match
    case GroupValue.Natural(_)         => Some(GroupResult.Natural)
    case GroupValue.Truth(_)           => Some(GroupResult.Truth)
    case GroupValue.IntBits(family, _) => Some(GroupResult.IntOf(family))
    case GroupValue.List(listed)       =>
      // A list entered through the JIT's decode point under the configuration the block is run in, whose encoding is
      // the block's: the elements hold no configuration to compare.
      Option(listed.elements.representation).collect {
        case Representation.ArrayListOf(element)
            if element == BinaryNaturalNatives.canonical =>
          GroupResult.List(GroupRepresentation.Natural)
        case Representation.ArrayListOf(element)
            if element == BinaryNaturalNatives.positive =>
          GroupResult.List(GroupRepresentation.Positive)
        case Representation.ArrayListOf(Representation.Data(family, None)) =>
          GroupResult.List(GroupRepresentation.IntOf(family))
      }
    case GroupValue.Constructed(_) | GroupValue.Row(_) => None

  /** The group of the block's results on the arguments, deduplicated, or no
    * value once the steps would pass the allowance, `stop` asks to stop, the
    * calls cycle or a row is rejected (`GroupEnd`); the steps spent either way.
    * A production's rows are counted before they are made, and `stop` is read
    * at the start of each production, so that a block never makes more rows
    * than its allowance. The run's finished calls are kept as `memo` says,
    * which changes how a call is found and never the results.
    */
  def run[C <: NativeSpecializer & Singleton](
      block: GroupBlock[C],
      arguments: Vector[Vector[GroupValue]],
      backend: GroupBackend,
      allowance: Long,
      stop: StopSignal,
      memo: GroupMemoOption = GroupMemoOption.Mapped
  ): GroupOutcome =
    require(admitted(block, arguments), "a block is run on arguments it admits")
    GroupProgram(block, backend, memo, allowance, stop).run(arguments)
