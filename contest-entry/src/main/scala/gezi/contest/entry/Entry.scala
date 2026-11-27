package gezi.contest.entry

import java.nio.file.Path
import gezi.frontend.DeBruijnTermOf
import gezi.hotspot.Cache
import gezi.hotspot.ExpansionSource
import gezi.hotspot.ForeignService
import gezi.saturation.StopSignal
import gezi.ir.{Closed, Configured, NativeSpecializer}

/** What a contest entry registers with `java.util.ServiceLoader`, in
  * `META-INF/services/gezi.contest.entry.EntryProvider` of its project: exactly
  * one implementation, by convention the class `<Name>EntryProvider` of the
  * package `gezi.contest.entries.<name>`, with a public constructor of no
  * parameter.
  */
trait EntryProvider:

  /** The entry before its first cell: it reads its own knowledge modules,
    * compiles its library and builds its strategies. The judge reads the wall
    * time from the start of the entry's JVM to the end of this call as the
    * setup reading.
    *
    * @param entryDirectory
    *   the entry's directory, `gezi/contest-entries-<name>/`
    * @param cache
    *   the cache service the judge built for the round, which the entry may
    *   keep as a field and read and write at every cell. The entry is given the
    *   `Cache`, never its provider: the runner announces the lifecycle events
    *   to the provider, and the entry connects to no cache service of its own
    * @param articles
    *   where the entry writes the articles of its compilation for the whole JVM
    *   (`ArticleDestination`): `Discarded` in the scored pass, a directory in
    *   the judge's article re-read
    */
  def initial(
      entryDirectory: Path,
      cache: Cache,
      articles: ArticleDestination
  ): Entry[?]

/** An entry between two cells. The runner hands the entry each cell in turn,
  * the entry a cell's run finished with running the next, and passes nothing
  * else from one cell to the next: whatever the entry keeps (the state after
  * the cells, compiled code, readings) is a field of the entry it finishes
  * with, in a shape of its own, or an entry of the cache it was given.
  */
trait Entry[C <: NativeSpecializer & Singleton]:

  /** The native specializer of the entry's configuration: the adapter builds
    * the terms it hands the entry through it (the cell's constants, the
    * judgment's candidate), so that they are terms of `C`.
    */
  def specializer: C

  /** The run of a cell: a closed `DeBruijnTermOf[Configured[C]]`
    * `State → (State, Output)` at the boundary, whose constants the adapter
    * built in `C`, before defunctionalization, which the entry runs through the
    * framework's front end to the defunctionalized IR before anything else
    * (`Cells.outputInstruction`, `Cells.nextStateInstruction`); nothing between
    * the front end and the read-back of the display holds a de Bruijn tree.
    *
    * The run finishes with the display of the cell's Output, a term with the
    * Output's Scott ADT values (the closed terms `λc1 … ck. ci v1 … vn` with
    * Output ⊑_O them), the phases of the run, and the entry after it, which
    * keeps the state after the cell (`Cells.nextState`, or any form ≃_O to it).
    * How far the Output is evaluated, and how many normal forms are shown, is
    * the entry's choice: the Scott ADT values of the Output
    * (`ScottADTChoices.of`) are the most canonical display, the Output not
    * evaluated (`Cells.output`) the simplest, which asserts nothing the Output
    * does not. The judge splits the display's top-level choice: `Values` assert
    * the set; `Mixed` asserts membership of its values; `Remainder` asserts
    * nothing; `Values` of no member asserts the empty set.
    *
    * The source is the version of the contents the URI nodes of the cell expand
    * to (`ExpansionSource`), which the adapter gives, since only it knows
    * whether its files change: the judge one for its whole run, whose files do
    * not change while it runs, the kernel one for each cell. What the entry
    * keeps from a cell read under one source (tables, the JIT's tables of
    * instances, the cache service's entries) answers no cell under another.
    *
    * The signal is the judge's cancel, Jupyter's interrupt of the cell: it asks
    * for a stop once the budget has run out. An entry that hands it to its
    * readings' budgets (`gezi.weakhead.Budget.stoppedBy`) stops at the next
    * check and returns; the cell is stopped either way, and a return within the
    * supervisor's grace keeps the JVM, and its compiled code, for the next
    * cells.
    *
    * The phases are self-reported and never scored: the wall time the judge
    * reads stays the cell's only score. Their names are the entry's own; the
    * recommended names, so that tables compare across entries, are `front_end`,
    * `recognition`, `type_check`, `extraction`, `jit_generation` and `run`, and
    * the judge enforces none of them. The phases need not sum to the cell's
    * wall time.
    */
  def run(
      cell: DeBruijnTermOf[Configured[C]],
      source: ExpansionSource,
      stop: StopSignal
  ): Interaction[C]

  /** The run of an FFI program, a Moore machine state
    * (`corpora/library/java_ffi/moore`), calling the service the adapter gives:
    * how it runs is this entry's configuration, and the adapter only provides
    * the service. None for an entry that runs no FFI program, which is every
    * entry that does not override this.
    */
  def interacted(
      state: Configured[C],
      service: ForeignService,
      source: ExpansionSource,
      stop: StopSignal
  ): Option[Interacted[C]] = None

  /** The display of one value an FFI program gave (`Interacted.answers`): the
    * value's Scott ADT values (`ScottADTChoices.of`) read by this entry's
    * reader and executor state, which the entry it returns keeps. A reading the
    * budget or the stop ends is displayed as the term it was given, unevaluated
    * (`OutputDisplay.Remainder`).
    */
  def displayed(
      value: Closed[C],
      source: ExpansionSource,
      stop: StopSignal
  ): (Entry[C], OutputDisplay[C])

/** What the run of an FFI program comes to: the answers its branches ended
  * with, the output fields they left unread, each a closed value of the entry's
  * configuration, whether it ran to its end, and the entry after it.
  */
final case class Interacted[C <: NativeSpecializer & Singleton](
    answers: Vector[Closed[C]],
    finished: Boolean,
    entry: Entry[C]
)

/** What an entry reports of a cell's run beside its display
  * (`Interaction.Finished`): a phase's seconds or a count, in the order the run
  * went through them. A name may repeat, one report for each time the run went
  * through it (each lemma round, say). The reports are self-reported and never
  * scored; the judge writes them into the pass table's phases column
  * (`PipeLines.phasesField`).
  */
sealed trait Report:
  def name: String

/** A phase of a cell's run as the entry reports it: its name, of lowercase
  * letters and underscores, and the seconds it took, finite and not negative
  * (`Interaction.Finished`). The constructor throws `IllegalArgumentException`
  * for another name or for negative or non-finite seconds.
  */
final case class Phase(name: String, seconds: Double) extends Report:
  if !Phase.namePattern.matches(name) then
    throw IllegalArgumentException(
      s"a phase's name is of lowercase letters and underscores, not $name"
    )
  if !seconds.isFinite || seconds < 0 then
    throw IllegalArgumentException(
      s"a phase's seconds are finite and not negative, not $seconds"
    )

/** A count of a cell's run as the entry reports it: its name, of lowercase
  * letters and underscores, and a value that is not negative, such as the
  * instances of a lemma round's saturation (`lemma_saturation_instances`) or
  * whether the round stopped at the framework's safety cap rather than at its
  * fixed point (`lemma_saturation_capped`, 1 or 0). The constructor throws
  * `IllegalArgumentException` for another name or a negative value.
  */
final case class Count(name: String, value: Long) extends Report:
  if !Phase.namePattern.matches(name) then
    throw IllegalArgumentException(
      s"a count's name is of lowercase letters and underscores, not $name"
    )
  if value < 0 then
    throw IllegalArgumentException(s"a count is not negative, not $value")

/** Timing a phase. */
object Phase:

  /** The names a phase may have. */
  val namePattern: scala.util.matching.Regex = "[a-z_]+".r

  /** The value of `body` and the phase of the name that took its time, read
    * with `System.nanoTime` before and after `body`.
    *
    * Timed by hand, not by JMH: the contest judge reads a point once, in one
    * pass, by its wall time, which is not a benchmark, and the phase report is
    * part of that reading, reported beside the wall time.
    */
  def timed[A](name: String)(body: => A): (A, Phase) =
    val start = System.nanoTime
    val value = body
    (value, Phase(name, (System.nanoTime - start) / 1e9))
