package gezi.narrowblocks.groups

import java.math.BigInteger
import gezi.ir.Value
import gezi.jit.ArrayListStorage
import gezi.jit.BackendFacts
import gezi.jit.BudgetShare
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.BinaryNaturalStorage
import gezi.jit.GroupBlockArtifact
import gezi.jit.GroupBlockResult
import gezi.jit.GroupBlocks
import gezi.jit.GroupStorage
import gezi.jit.StorageEncodingOperations
import gezi.jit.StorageOf
import gezi.jit.IntStorage
import gezi.jit.JitValue
import gezi.jit.JvmBits
import gezi.jit.NativeName
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.TruthStorage
import gezi.saturation.StopSignal
import gezi.ir.{Configured, NativeSpecializer}

/** A compiled group block, as the JIT keeps it: the block with the backend and
  * the memo option it runs on, typed by the configuration it was compiled for,
  * which runs itself on the arguments the JIT decoded.
  */
final case class CompiledGroupBlock[C <: NativeSpecializer & Singleton](
    block: GroupBlock[C],
    backend: GroupBackend,
    memo: GroupMemoOption,
    specializer: C
) extends GroupBlockArtifact[C]:

  def entryRepresentations: Vector[Representation[JitValue[C]]] =
    block.entries.map(GroupBlockMechanism.representation)

  def run(
      arguments: Vector[JitValue[C]],
      allowance: Long,
      stop: StopSignal
  ): Option[GroupBlockResult[C]] =
    given C = specializer
    val groups = arguments.map(argument => GroupBlockMechanism.group(argument))
    Option
      .when(groups.forall(_.isDefined))(groups.flatten)
      .filter(GroupRun.admitted(block, _))
      .map(admitted =>
        val outcome =
          GroupRun.run(block, admitted, backend, allowance, stop, memo)
        outcome.ended match
          case GroupEnd.Finished(results) =>
            GroupBlockResult.Gave(
              JitValue.Choice(results.map(value(block.result, _))),
              outcome.steps
            )
          case GroupEnd.Stopped  => GroupBlockResult.Stopped(outcome.steps)
          case GroupEnd.Rejected => GroupBlockResult.Rejected(outcome.steps)
      )

  /** The JIT's value of one of a block's results, of the kind the block's
    * syntax says its values are, built by the encoding's operations the block
    * was compiled with.
    */
  private def value(result: GroupResult, found: GroupValue): JitValue[C] =
    val operations = block.operations
    (result, found) match
      case (GroupResult.Natural, GroupValue.Natural(number)) =>
        operations.storageOf(
          BinaryNaturalNatives.canonical,
          BinaryNatural(BigInt(number))
        )
      case (GroupResult.Truth, GroupValue.Truth(truth)) =>
        operations.storageOf(Representation.Truth, NativeValue.Truth(truth))
      case (GroupResult.IntOf(family), GroupValue.IntBits(valueFamily, bits))
          if valueFamily == family =>
        operations.storageOf(
          Representation.Data(family, None),
          JvmBits(32, Integer.toUnsignedLong(bits))
        )
      case (
            GroupResult.Constructed(family, filter),
            GroupValue.Constructed(constructed)
          ) =>
        // The value of the declared family at the block's filter: its storage, the unique spelling of
        // `constructor fields ∥ filter`.
        operations.storageOf(
          filter,
          NativeValue.Constructed(
            family,
            constructed.constructor,
            constructed.fields.map(field => BinaryNatural(BigInt(field)))
          )
        )
      case (GroupResult.List(element), GroupValue.List(list)) =>
        // The list leaves as it is, its storage the one it entered as when it entered unchanged: a result column's
        // every list is of the result's representation (`GroupListKind.consed`).
        val representation = GroupBlockMechanism.listRepresentation(element)
        require(
          list.elements.representation == representation,
          s"a block of lists of $representation gave a list of ${list.elements.representation}"
        )
        operations.storageOf(representation, list)
      case _ =>
        throw IllegalStateException(
          s"a group block of values $result gave $found"
        )

/** The JIT's group block mechanism (`gezi.jit.GroupBlocks`) over a group
  * compilation and a group program backend: a written thunk's block is its
  * group compilation (`GroupCompilation.compiled`), which compiles a block only
  * when the facts store the array lists of every list kind it has; the block
  * runs on its arguments when each is written as a storage of a binary natural
  * or of an array list, a group storage of them, or a choice of these
  * (`GroupBlockMechanism.group`), an array list entering as its elements,
  * shared, never copied, its filters keeping the values of the representations
  * they name, and its results, a group of one or more values (`GroupProgram`
  * requires it), come back as the choice of their values: a natural as a
  * storage of the canonical naturals' representation, a truth value as a
  * storage of the truth values', a declared family's value as its constructor
  * applied to its fields' storages and filtered by the family's filter as the
  * block writes it (`GroupResult.Constructed`), the parallel made by the native
  * specializer of the JIT's facts (`NativeSpecializer.parallelOfValues`), which
  * converts it to the family's storage, and a list as the array list's storage
  * of its elements: the very suffix of the storage it entered as, when it is
  * one, else the storage of a new vector, one object either way
  * (`StorageEncoding.storageOf`). The JIT decodes each argument at the block's
  * entry through the decode point of the criterion the block filters that
  * parameter by (`entryRepresentations`), the steps the blocks of a reading
  * waste at most the mechanism's share of its budget (`share`), and asks only
  * when no argument is a neutral value (`runnable`); the block itself evaluates
  * no term.
  *
  * The steps the block spends are the rows its productions make (`GroupRun`),
  * counted before each production makes them; `stop` is read at the start of
  * each production. A block that stops gives its steps and no value.
  */
final case class GroupBlockMechanism(
    compilation: GroupCompilation,
    facts: BackendFacts,
    backend: GroupBackend,
    share: BudgetShare = GroupBlockMechanism.defaultShare,
    memo: GroupMemoOption = GroupMemoOption.Mapped
) extends GroupBlocks:
  require(
    compilation.facts == facts,
    "the blocks are compiled under the JIT's own facts, whose array lists they make"
  )

  /** No argument is a neutral value: the JIT decodes the others at the block's
    * entry.
    */
  def runnable[C <: NativeSpecializer & Singleton](
      arguments: Vector[JitValue[C]]
  )(using C): Boolean = arguments.forall {
    case JitValue.Neutral(_, _) => false
    case _                      => true
  }

  def allowance(steps: Long): Long = share.of(steps)

  def compiled[C <: NativeSpecializer & Singleton](
      thunk: Configured[C],
      operations: StorageEncodingOperations[C]
  )(using C): Option[GroupBlockArtifact[C]] =
    compilation
      .compiled(thunk, operations)
      .map(CompiledGroupBlock(_, backend, memo, summon[C]))

/** How a group block reads its arguments. */
object GroupBlockMechanism:

  /** Half a reading's budget: the blocks of a reading waste at most half of its
    * steps, and the machine keeps the other half.
    */
  val defaultShare: BudgetShare = BudgetShare(1, 2)

  /** The storages' representation of the values a filter keeps. */
  def representation(filter: GroupRepresentation): Representation[Nothing] =
    filter match
      case GroupRepresentation.Natural         => BinaryNaturalNatives.canonical
      case GroupRepresentation.Positive        => BinaryNaturalNatives.positive
      case GroupRepresentation.Truth           => Representation.Truth
      case GroupRepresentation.ListOf(element) => listRepresentation(element)
      case GroupRepresentation.IntOf(family)   =>
        Representation.Data(family, None)

  /** The representation of the array lists of a block's list result. */
  def listRepresentation(
      element: GroupRepresentation
  ): Representation[Nothing] =
    Representation.ArrayListOf(representation(element))

  /** The group of values an argument written as a storage of a binary natural,
    * of a truth value or of an array list, a group storage of them (the native
    * specializer's spelling of `(m1 + … + mk) ∥ T`), or a choice of these, is,
    * an array list as its elements, shared; none for an argument of any other
    * spelling. Which of them a parameter's occurrences keep is the filters' in
    * the block's term.
    */
  def group[C <: NativeSpecializer & Singleton](argument: JitValue[C])(using
      C
  ): Option[Vector[GroupValue]] =
    @scala.annotation.tailrec
    def gathered(
        pending: List[JitValue[C]],
        found: Vector[GroupValue]
    ): Option[Vector[GroupValue]] =
      pending match
        case Nil             => Some(found)
        case current :: rest =>
          (current.representation: AnyRef) match
            case natural: BinaryNaturalStorage =>
              gathered(
                rest,
                found :+ GroupValue.Natural(natural.natural.bigInteger)
              )
            case list: ArrayListStorage =>
              gathered(rest, found :+ GroupValue.List(list.listed))
            case truth: TruthStorage =>
              gathered(rest, found :+ GroupValue.Truth(truth.truth))
            case word: IntStorage =>
              word.representation match
                case Representation.Data(family, None) =>
                  gathered(rest, found :+ GroupValue.IntBits(family, word.bits))
                case _ => None
            case _: GroupStorage[?] =>
              // The members of a group storage, each its own storage.
              Value.closed(current).flatMap(StorageOf.group[C]) match
                case Some(group) =>
                  gathered(
                    group.members
                      .map(member => StorageOf.value(member))
                      .toList ::: rest,
                    found
                  )
                case None => None
            case _ =>
              current match
                case JitValue.Choice(members) if members.nonEmpty =>
                  gathered(members.toList ::: rest, found)
                case _ => None
    gathered(List(argument), Vector.empty)
