package com.yang_bo.gezi.jit

import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** A group block compiled from a written thunk, kept by the reading's state
  * under that thunk (`JitRunState.groupBlocks`), typed by the configuration it
  * was compiled for: it holds terms and values of `C` and the encoding's
  * operations it was compiled with, and it runs itself. Each mechanism defines
  * its own immutable subtypes.
  */
trait GroupBlockArtifact[C <: NativeSpecializer & Singleton]:

  /** The representation of each of the block's parameters, in order, whose
    * criterion T its argument `a` is read through as the decode point `a ∥ T`
    * before the block runs.
    */
  def entryRepresentations: Vector[Representation[JitValue[C]]]

  /** The block run on the arguments, within `allowance` steps under `stop`: its
    * result, or none when it does not admit the arguments.
    */
  def run(
      arguments: Vector[JitValue[C]],
      allowance: Long,
      stop: StopSignal
  ): Option[GroupBlockResult[C]]

/** What a group block gave, and the steps it spent however it ended. */
enum GroupBlockResult[C <: NativeSpecializer & Singleton]:

  /** The value the machine continues from, the choice of the block's results.
    */
  case Gave(continued: JitValue[C], spent: Long)

  /** No value: the block stopped before it finished, its allowance about to run
    * out, a stop asked for, or a cycle met. The machine gives the thunk's block
    * up for the rest of the reading.
    */
  case Stopped(spent: Long)

  /** No value: the block stopped on a row it would have to drop, a value a
    * filter rejects or a native has no answer for, which has no answer itself
    * but may have one in the context consuming it, so the block does not drop
    * it. A rejection is the arguments' outcome, which another argument may not
    * meet, so the machine does not give the thunk's block up for it.
    */
  case Rejected(spent: Long)

  /** The steps the block spent, however it ended. */
  def steps: Long = this match
    case Gave(_, spent)  => spent
    case Stopped(spent)  => spent
    case Rejected(spent) => spent

  /** The value the machine continues from, when the block gave one. */
  def value: Option[JitValue[C]] = this match
    case Gave(continued, _)       => Some(continued)
    case Stopped(_) | Rejected(_) => None

/** The share of a reading's budget the group blocks of the reading may waste
  * together, in entries that give no value: `numerator / denominator` of it, so
  * that the machine keeps the rest.
  */
final case class BudgetShare(numerator: Long, denominator: Long):
  require(
    numerator >= 0 && denominator > 0 && numerator <= denominator,
    s"a share is a fraction of the whole: $numerator / $denominator"
  )

  /** The steps of a budget of `steps` the share gives. */
  def of(steps: Long): Long = BigInt(steps).*(numerator)./(denominator).toLong

/** The group block mechanism of the JIT, a replaceable component of
  * `JitConfiguration`: when an application of a closed thunk that is an
  * instruction, read as the head of an evaluation, has at least as many
  * arguments as the thunk has holes, the machine asks `compiled` for the block
  * of that thunk and, if there is one, reads each of the first arguments `a`
  * through the decode point `a ∥ T` of the representation whose criterion T the
  * block filters that parameter by at its every occurrence
  * (`entryRepresentations`), whole: every head a storage, a list's cells read
  * one by one into an array list's storage, or the reading gives no block. The
  * steps the blocks of a reading waste together, in decodings that run out or
  * read no storage and blocks that admit no argument or stop, are at most the
  * mechanism's share of the reading's budget (`allowance`), each entry within
  * what is left of it; a decoding that runs out leaves no value and no table
  * behind, its steps spent, and the machine reads the application as it reads
  * any; the JIT then gives that thunk up for the rest of the reading, as it
  * does a thunk whose block stopped other than on a rejected row
  * (`GroupBlockResult.Stopped`), so that its later applications waste no more.
  * It asks only when no argument is a neutral value (`runnable`), so that no
  * thunk the readers apply to neutral values, such as a lambda of a value's
  * normal form, is scanned.
  *
  * Whether there is a block is decided from the thunk's syntax alone, by one
  * mechanical scan of a fixed, published grammar that reads only syntax, the
  * library's `native` declarations and the backend's facts. The machine cannot
  * tell a thunk written in the program from one it built while it read, an
  * inner thunk of a code whose fillings are values read (`JitValue.IrTerm` is
  * any term of the IR's layers, whoever built it): both are closed terms, so a
  * block of either is sound, and either is asked about. Its block is kept in
  * the reading's state under the thunk (`JitRunState.groupBlocks`), under the
  * configuration's instance retention: under `Generations(size)` in two
  * generations of `size`, so that the thunks built from many values do not grow
  * the state without bound; under `NeverDropped` never dropped, growing as the
  * instance tables do. A block runs on the decoded arguments, storages or
  * choices of them, in the representations the block's filters name.
  *
  * The block's answers are among the application's under the β rule and the
  * natives' equations on single values: a refinement, which may lose answers
  * and adds none. It loses those of a choice's member the grammar does not read
  * and the cross answers a native's define would give where it reads one
  * operand more than once (a native is called on single values); it gives all
  * the application's answers when it loses none of these. Where a filter
  * rejects a value or a native has no answer for one, it drops no row: it stops
  * with no value, and the machine reads the application, which loses that
  * answer at its own decode point (a FIXME at `Jit.readingDecoded`), as the
  * entry's decode points lose an argument's member a parameter's filter
  * excludes (`Jit.entryDecoded`). The steps it spent are charged to the
  * reading's budget, whether it finished or stopped; a block that stopped gives
  * no value, and the machine reads the application itself.
  */
trait GroupBlocks:

  /** Whether a block could run on arguments of these spellings: a condition on
    * how each argument is written, never on what it is.
    */
  def runnable[C <: NativeSpecializer & Singleton](
      arguments: Vector[JitValue[C]]
  )(using C): Boolean

  /** The steps of a reading's budget of `steps` that the group blocks of the
    * reading may waste together, in entries that give no value.
    */
  def allowance(steps: Long): Long

  /** The block of the written thunk, or none when it is no block, compiled with
    * the encoding's operations of the configuration
    * (`JitConfiguration.operations`), which the block keeps.
    */
  def compiled[C <: NativeSpecializer & Singleton](
      thunk: Configured[C],
      operations: StorageEncodingOperations[C]
  )(using C): Option[GroupBlockArtifact[C]]

/** The mechanism that compiles no block, still the default of a configuration
  * that names none (`JitConfiguration`), a default that loses answers as below
  * until the defaults move to group blocks.
  *
  * DEPRECATED: without group blocks, a native call with a multi-valued argument
  * takes the product of its arguments' values at the call, outside any block
  * (`Jit.valuedCombinations`), one value per argument position before the
  * callee is entered, and a compiled block is single-valued; so a reading loses
  * answers the term has, as on `plus x (plus (x + 1) x)` at x = 0, `x + 1` the
  * choice of x and 1, read as 0 alone where the term's answers are 0 and 1.
  * Group blocks take the product inside the block and read both. No new entry
  * selects this mechanism; the entries, the tests and the defaults that select
  * it move to group blocks, and then it is deleted. FIXME:
  * https://github.com/Atry/private-overlay/issues/2221
  */
@deprecated(
  "loses answers a multi-valued argument has; select group blocks",
  "2026-11-24"
)
object NoGroupBlocks extends GroupBlocks:

  def runnable[C <: NativeSpecializer & Singleton](
      arguments: Vector[JitValue[C]]
  )(using C): Boolean = false

  def compiled[C <: NativeSpecializer & Singleton](
      thunk: Configured[C],
      operations: StorageEncodingOperations[C]
  )(using C): Option[GroupBlockArtifact[C]] = None

  def allowance(steps: Long): Long = 0L
