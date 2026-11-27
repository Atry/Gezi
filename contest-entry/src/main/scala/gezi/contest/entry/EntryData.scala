package gezi.contest.entry

import java.nio.file.Files
import java.nio.file.Path
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Literals
import gezi.ir.BuiltInRule
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Computation
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.ir.{ChoiceSpine, Configured, NoFacts}

/** An entry written as data, with no Scala of its own, its compiler written
  * with lemmas and natives: the compiler the file `entry.lambdalattice` in the
  * entry's directory writes, `compiler(rounds, backend)` of the schema, an ADT
  * that configures the rounds of the e-graph. Every name is from a list the
  * framework publishes here; no class is named and no member chooses by a
  * family or a point. There is no fuel: a round has no budget and an entry sets
  * no limit of its own.
  *
  * @param rounds
  *   the lemma rounds, in order, each run to its fixed point under the
  *   framework's safety cap before the general reading
  * @param backend
  *   the backend's knowledge, one term, a knowledge mixin whose slots
  *   `natives`, `representations`, `families`, `fields` and `jvm_types` are
  *   read as knowledge (`StandardLibrary.knowledgeSlots`)
  * @param jit
  *   the options of the framework's JIT, read off the backend's fields `jit`
  *   and `instances`
  * @param reading
  *   the options of the executor that reads the entry's programs, read off the
  *   backend's field `reading`
  * @param executor
  *   the executor that reads the entry's programs, read off the backend's field
  *   `execution`: the framework's JIT, or a module's
  * @param compilationPlace
  *   where the program is compiled by the lemma rounds, read off the backend's
  *   field `execution`
  * @param occurrenceTagging
  *   how the program is tagged as occurrences before the lemma rounds, read off
  *   the backend's field `execution`
  * @param groupBlocks
  *   the JIT's group block mechanism, read off the backend's field `execution`
  */
final case class EntryData(
    rounds: Vector[EntryRound],
    backend: Configured[NoFacts.type],
    jit: JitOptions,
    reading: ReadingOptions,
    executor: ExecutorOption,
    compilationPlace: CompilationPlaceOption,
    occurrenceTagging: OccurrenceTaggingOption,
    groupBlocks: GroupBlocksOption = GroupBlocksOption.None
):

  /** The knowledge the entry's library is compiled from, one term: the choice
    * of the backend's knowledge and the rounds', the backend's first, read as
    * one mixin. Every slot of `StandardLibrary.knowledgeSlots` is read off
    * every part: the schema says which part a slot belongs to, and this reading
    * does not refuse a slot written in another part (the library holds every
    * fact the entry writes; a round's lemmas and leaves are still the round's
    * own, `StandardLibrary.lemmas` and `leaves` of its knowledge).
    */
  def knowledge: Configured[NoFacts.type] =
    ChoiceSpine.nested[Configured[NoFacts.type]](
      (backend +: rounds.map(_.knowledge)).distinct,
      NoFacts.choice(_, _)
    )

/** A lemma round, `round(knowledge, implementations, behaviour)` of the schema:
  * its knowledge, one term, a knowledge mixin whose slots `leaves` and `lemmas`
  * are read as knowledge (`StandardLibrary.leaves`, `lemmas`); whether closures
  * are opened and their bodies written back; the built-in rules it enables
  * (`BuiltInRule`, each opt-in, δ and β included), the empty set a round with
  * no built-in rule; and the implementations its saturation and extraction use,
  * the indexer's among them, a round's and not the compiler's, each mapped by
  * `Defaults`.
  */
final case class EntryRound(
    knowledge: Configured[NoFacts.type],
    settings: RoundSettings
)

/** A round's settings, every field of the round but its knowledge. */
final case class RoundSettings(
    opening: Boolean,
    builtInRules: Set[BuiltInRule],
    indexer: IndexerImplementation,
    orientationCompiler: OrientationCompilerImplementation,
    saturator: SaturatorImplementation,
    extractor: ExtractorImplementation,
    lemmaEncoding: LemmaEncodingImplementation,
    ematching: EmatchingImplementation,
    respellings: MemoRetentionOption,
    writeBackSpellings: WriteBackSpellingsOption,
    openingCriterion: OpeningCriterionOption,
    constantStorageStop: Boolean = false
)

// THE OPTIONS AS SCOTT CONSTRUCTORS. Each published list below is a Scott
// sum: an entry writes one of its constructors, which it imports from the
// list's file under corpora/compiler/entry_options (its fields in the order
// of the enum's cases), and `EntryData` reads which alternative it is by
// structure (`KnowledgeReading.alternative`), never by a name: an option that
// cannot make a result unsound is a Scott ADT. A wrong
// constructor cannot make a result unsound: it only chooses another published
// implementation of one interface, each of which must compute the same
// answers, or fails to read; a built-in rule left out only loses merges, and a
// false negative is not unsoundness. Each list is an extension point: the
// indexer's, the round's saturator, extractor, lemma encoding and e-matching
// backend and its
// orientation compiler, below; the
// JIT's on `JitOptions`; the reading executor's on `ReadingOptions`; the
// executor's, `ExecutorOption`, whose constructor `module` opens the list to
// executors outside the framework, as the extractor's constructor `module`
// opens its list to extractions outside it.

/** The published implementations of the indexer, the interface that compiles a
  * round's orientations and codes, the constructors of
  * corpora/compiler/entry_options/indexer (an implementation that keeps the
  * interface and only improves efficiency may be one entry's alone for a
  * round). An exclusive implementation joins this list for its round beside
  * `Standard`, the framework's.
  */
enum IndexerImplementation:
  case Standard

/** The published compilers of a round's lemma orientations, the constructors of
  * corpora/compiler/entry_options/orientation_compiler: `Standard`, the
  * framework's (`gezi.orientation.StandardOrientationCompiler`).
  */
enum OrientationCompilerImplementation:
  case Standard

/** Whether a memo of a round's implementation keeps what it computed, the
  * constructors of corpora/compiler/entry_options/memo_retention
  * (`gezi.egraph.MemoRetention`): `Kept` or `NotKept`. A round chooses it for
  * its graph's respellings of thunk layers (`respellings`).
  */
enum MemoRetentionOption:
  case Kept, NotKept

/** How long the spellings a round's write-backs find are kept, the constructors
  * of corpora/compiler/entry_options/write_back_spellings
  * (`gezi.strategies.SpellingRetention`): `KeptWithinAPass`, from one body to
  * the next within a pass; `NotKept`, dropped after every body; and
  * `KeptAcrossPasses`, from one pass to the next as well, the entries of the
  * classes the graph changed since, and of those that read them, dropped.
  */
enum WriteBackSpellingsOption:
  case KeptWithinAPass, NotKept, KeptAcrossPasses

/** Which closures a round opens, the constructors of
  * corpora/compiler/entry_options/opening_criterion
  * (`gezi.saturation.OpeningCriterionChoice`): `CallsAHead`, every closure that
  * calls a name some enabled lemma's left side applies, and
  * `CallsAHeadWithMatchingArguments`, only those where some such call's
  * arguments may match one of that name's spines in a left side. It takes
  * effect when the round's `opening` is on.
  */
enum OpeningCriterionOption:
  case CallsAHead, CallsAHeadWithMatchingArguments

/** The published implementations of a round's saturation, the constructors of
  * corpora/compiler/entry_options/saturator: `HigherOrder`, the lemma
  * compilation's (`gezi.strategies.HigherOrderSaturator`, with the round's
  * closures opened when its `opening` says so). An implementation joins the
  * list once it runs on the round's shared graph as `HigherOrderSaturator` does
  * (`prepared`, `begunOn`); the baseline's `StandardSaturator` does not.
  */
enum SaturatorImplementation:
  case HigherOrder

/** The published implementations of a round's extraction, the constructors of
  * corpora/compiler/entry_options/extractor: `NarrowBlock`, the narrow blocks
  * over the entry's natives first, then the size
  * (`gezi.narrowblocks.NarrowBlockExtractor`), and `NarrowListBlock`, its
  * opt-in copy with lists and booleans, each with two fields, the bounds of how
  * it reads a thunk's jointly read fillings (`gezi.strategies.JointReading`):
  * the enumeration bound, a positive integer, and the whole fold bound, a
  * non-negative one; and `Module`, the extraction of a module registered with
  * `java.util.ServiceLoader` and the route it pairs with (`ExtractorModule`,
  * `ExtractorModules`).
  */
enum ExtractorImplementation:
  case NarrowBlock(enumerationBound: Long, wholeFoldBound: Long)

  /** The narrow blocks with lists and booleans over the entry's natives first,
    * then the size (`gezi.narrowblocks.lists.NarrowBlockExtractor`), a copy
    * that an entry opts into while `NarrowBlock` keeps the narrow blocks as
    * they were before them.
    */
  case NarrowListBlock(enumerationBound: Long, wholeFoldBound: Long)

  /** The extraction and the route of the module registered whose selector is
    * the term `selector`, built from `parameters`, a term the module reads by
    * structure itself. Both fields are read back as their author wrote them
    * (`KnowledgeReading.term`), as `ExecutorOption.Module`'s are, so that the
    * selector is the interned instruction the module's selector file gives; the
    * host compares it by identity and reads no string of it.
    */
  case Module(
      selector: Configured[NoFacts.type],
      parameters: Configured[NoFacts.type]
  )

/** The published encodings of a lemma's two closed terms into patterns, the
  * constructors of corpora/compiler/entry_options/lemma_encoding: `Baseline`,
  * `gezi.lemmaencoding.baseline.BaselineLemmaEncoding`.
  */
enum LemmaEncodingImplementation:
  case Baseline

/** The published e-matching backends that run a round's program, the
  * constructors of corpora/compiler/entry_options/ematching: `Closures`, a
  * program compiled once into Scala closures; `Interpretation`, its steps
  * walked at every call; `Bytecode`, a hidden class generated with
  * `java.lang.classfile`. All three compute the same matches
  * (backendcomparison's tests).
  */
enum EmatchingImplementation:
  case Closures, Interpretation, Bytecode

/** The published dispatch strategies of the JIT, the constructors of
  * corpora/compiler/entry_options/dispatch: the backend may drop the untyped
  * version or run it as a fallback by a generic interpreter such as the weak
  * head.
  */
enum DispatchOption:
  case Fallback

/** The published implementations of the JIT's backend, the constructors of
  * corpora/compiler/entry_options/implementation, a list that more efficient
  * backends, such as one compiling to Java bytecode, join.
  */
enum BackendOption:
  case Closure

/** The published granularities of the JIT, the constructors of
  * corpora/compiler/entry_options/granularity, so that a backend chooses among
  * strategies of generation an entry may optimise, rather than one way defined
  * for all.
  */
enum GranularityOption:
  case PredicatePerCode

/** The published policies that decide which instances the JIT's instance table
  * looks up and records (`gezi.jit.InstanceCheckpoints`), the constructors of
  * corpora/compiler/entry_options/checkpoints: `Profitable`, every instance
  * whose code's table cost is not judged unprofitable
  * (`gezi.jit.ProfitableCheckpoints`); `EverySteps`, a checkpoint once at least
  * `interval` steps were spent since the last
  * (`gezi.jit.EveryStepsCheckpoints`), its one field the interval.
  */
enum CheckpointOption:
  case Profitable
  case EverySteps(interval: Long)

/** The published ways the JIT's instance table pulls a missed instance's
  * reading beyond the heads its consumers ask for
  * (`gezi.jit.InstanceLookahead`), the constructors of
  * corpora/compiler/entry_options/lookahead: `Lazily`, each head only when
  * asked for; `WithinSteps`, the rest pulled within `steps` steps right after
  * the first head, its one field.
  */
enum LookaheadOption:
  case Lazily
  case WithinSteps(steps: Long)

/** The published ways the JIT's state keeps the instance table's complete
  * tables (`gezi.jit.InstanceRetention`), the constructors of
  * corpora/compiler/entry_options/instance_retention: `Generations`, two
  * generations of `size` entries each, its one field the size; `NeverDropped`,
  * every complete table kept for as long as the state lives.
  */
enum InstanceRetentionOption:
  case Generations(size: Int)
  case NeverDropped

/** The published native block mechanisms of the JIT
  * (`gezi.jit.NativeBlockMechanism`), the constructors of
  * corpora/compiler/entry_options/native_blocks: `None`, no instance entered as
  * a native block (`gezi.jit.NoNativeBlocks`).
  */
enum NativeBlocksOption:
  case None

/** The published ways the answers of the JIT's instance table outlive a version
  * of the contents the URI nodes expand to (`gezi.jit.InstanceReuse`), the
  * constructors of corpora/compiler/entry_options/instance_reuse:
  * `WithinVersion`, every answer dropped under a new version;
  * `VerifiedAcrossVersions`, the answers kept with what they read and verified
  * before they are used.
  */
enum InstanceReuseOption:
  case WithinVersion
  case VerifiedAcrossVersions

/** The options of the framework's JIT, `jit_options` of the schema: every one
  * is written, there is no default.
  *
  * @param budget
  *   the JIT's compilation budget (`gezi.jit.JitConfiguration.budget`)
  */
final case class JitOptions(
    dispatch: DispatchOption,
    implementation: BackendOption,
    granularity: GranularityOption,
    instanceTable: Boolean,
    instanceTableTrial: Long,
    instanceRetention: InstanceRetentionOption,
    budget: Int,
    checkpoints: CheckpointOption,
    nativeBlocks: NativeBlocksOption,
    lookahead: LookaheadOption,
    instanceReuse: InstanceReuseOption
)

/** The published ways the weak-head machines take an application apart
  * (`gezi.weakhead.ApplicationReading`), the constructors of
  * corpora/compiler/entry_options/application: `ByLayer`, one application at a
  * time; `BySpine`, a whole spine at once; `BySharedPrefix`, a whole spine from
  * its longest prefix that holds a table or where spines part.
  */
enum ApplicationOption:
  case ByLayer, BySpine, BySharedPrefix

/** The published ways the tabled weak head applies a function to a continuation
  * (`gezi.weakhead.ContinuationReading`), the constructors of
  * corpora/compiler/entry_options/continuation: `Substituted`, the β rule as it
  * is; `Packed`, a head that uses its continuation in tail position read as
  * applied to the closed pack first, its work before the continuation shared.
  */
enum ContinuationOption:
  case Substituted, Packed

/** The published ways the tabled weak head reads a parallel
  * (`gezi.weakhead.ParallelReading`), the constructors of
  * corpora/compiler/entry_options/parallel: `BothSides`, both sides read and
  * every parallel set of one paired with every parallel set of the other;
  * `HeadsMet`, each parallel set met head by head, the lambda heads of one code
  * merged by their fillings and a set of two heads that apply different binders
  * dropped.
  */
enum ParallelOption:
  case BothSides, HeadsMet

/** The published places a reading keeps the complete tables of the tabled weak
  * head (`gezi.weakhead.TableSharing`), the constructors of
  * corpora/compiler/entry_options/table_sharing: `Local`, the reading's state
  * alone; `Strong`, `SoftValues` and `WeakKeys`, the cache service of the
  * reading's dependencies, its references to them of that strength
  * (`gezi.hotspot.Retention`).
  */
enum TableSharingOption:
  case Local, Strong, SoftValues, WeakKeys

/** The published retentions of the tables an entry's reading leaves for its
  * next reading (`gezi.weakhead.TableRetention`), the constructors of
  * corpora/compiler/entry_options/table_retention: `KeptAll`, every table,
  * never dropped; `NoneKept`, none, each reading from no table;
  * `DroppedAtPercent`, every table until they reach its one field, an integer
  * from 1 to 100, percent of the table limit, then none.
  */
enum TableRetentionOption:
  case KeptAll
  case NoneKept
  case DroppedAtPercent(percent: Int)

/** The options of the executor that reads an entry's programs, written in the
  * backend's field `options` beside the JIT's: every one is written, there is
  * no default.
  */
final case class ReadingOptions(
    application: ApplicationOption,
    tableSharing: TableSharingOption,
    tableRetention: TableRetentionOption,
    continuation: ContinuationOption,
    parallel: ParallelOption
)

/** The published executors that read an entry's programs, the constructors of
  * corpora/compiler/entry_options/executor: `Jit`, the framework's, its JIT as
  * a reading executor (`Defaults.executor`); `Module`, the executor of the
  * module registered with `java.util.ServiceLoader` whose selector is the term
  * `selector` (`ExecutorModule`, `ExecutorModules`), built from `parameters`, a
  * term the module reads by structure itself. Both fields are read back as
  * their author wrote them (`KnowledgeReading.term`), so that the selector is
  * the interned instruction the module's selector file gives; the host compares
  * it by identity and reads no string of it.
  */
enum ExecutorOption:
  case Jit
  case Module(
      selector: Configured[NoFacts.type],
      parameters: Configured[NoFacts.type]
  )

/** The published units the upfront compilation compiles, the constructors of
  * corpora/compiler/entry_options/unit_selection: `WholeProgram`, the program
  * as one unit, the rounds run on each point; `LetBoundClosure`, the function a
  * program's top-level let binds (`gezi.narrowblocks.BoundFunctionUnit`),
  * compiled once per configuration into the cache service and replaced in each
  * point by its artifact (`gezi.narrowblocks.ClosureUnits`), a program with no
  * such let compiled whole.
  */
enum UnitSelectionOption:
  case WholeProgram, LetBoundClosure

/** The published places an entry's program is compiled by its lemma rounds, the
  * constructors of corpora/compiler/entry_options/compilation_place: `Upfront`,
  * the generic entry runs the rounds and hands the executor the program they
  * give, compiling the units its field selects; `ByExecutor`, the generic entry
  * runs no round and hands the executor the program uncompiled, the entry's
  * prepared compilation among the executor's inputs
  * (`ExecutorModuleInputs.compilation`), so that an executor may interpret
  * within a small budget and compile only what does not finish. The framework's
  * executor (`ExecutorOption.Jit`) reads the program it is given as it is, so
  * that under `ByExecutor` it reads the uncompiled program.
  */
enum CompilationPlaceOption:
  case Upfront(units: UnitSelectionOption)
  case ByExecutor

/** The published occurrence taggings of an entry's program before its lemma
  * rounds, the constructors of
  * corpora/compiler/entry_options/occurrence_tagging: `Untagged`, the program
  * as the cell gives it; `NamesAndClosures`, each lambda chain and each shared
  * part of the program tagged as an occurrence
  * (`gezi.frontend.ProgramOccurrences`), the library's terms left untagged
  * inside (`Defaults.occurrencesTagged`).
  */
enum OccurrenceTaggingOption:
  case Untagged, NamesAndClosures

/** The published group backends, the constructors of
  * corpora/compiler/entry_options/group_backend: `Scalar`, the JVM scalar
  * backend, the reference semantics of every backend
  * (`gezi.narrowblocks.groups.ScalarGroupBackend`); `JvmArray`, the JVM array
  * backend (`gezi.narrowblocks.groups.JvmArrayGroupBackend`).
  */
enum GroupBackendOption:
  case Scalar, JvmArray

/** The published group block mechanisms of an entry's JIT, the constructors of
  * corpora/compiler/entry_options/group_blocks: `None`, the JIT runs no group
  * block (`gezi.jit.NoGroupBlocks`); `Enabled`, a written closed thunk applied
  * to enough arguments runs as a group block when the group grammar compiles
  * it, on the group backend `backend`
  * (`gezi.narrowblocks.groups.GroupBlockMechanism`), the steps the blocks of a
  * reading waste together (entries that give no value) at most `sharePercent`
  * percent of the reading's budget, and a recursion whose arguments are all
  * lists keeping its finished calls in a dense table of at most `denseCells`
  * cells (none at 0) beside the map
  * (`gezi.narrowblocks.groups.GroupMemoOption`).
  */
enum GroupBlocksOption:
  /** DEPRECATED, as `gezi.jit.NoGroupBlocks` is: a reading under it loses
    * answers a multi-valued argument has. FIXME:
    * https://github.com/Atry/private-overlay/issues/2221
    */
  @deprecated(
    "loses answers a multi-valued argument has; select group blocks",
    "2026-11-24"
  )
  case None
  case Enabled(
      sharePercent: Int = 50,
      denseCells: Long = 65536,
      backend: GroupBackendOption = GroupBackendOption.Scalar
  )

/** Why a file `entry.lambdalattice` is not an entry: the field and what is
  * wrong with it. The file is the entry author's input, so a wrong field is
  * reported, not recovered from (CONTRIBUTING.md, offensive programming).
  */
final case class EntryDataError(reason: String)
    extends IllegalArgumentException(reason)

object EntryData:

  /** The reading of an entry's data, which is read under no facts: its terms
    * are the library's and the entry's own data, which exist before any facts
    * do.
    */
  private type Reading[Result] =
    gezi.knowledgereading.Reading[NoFacts.type, Result]

  private given NoFacts.type = NoFacts

  /** The entry of the directory's `entry.lambdalattice`, read by projection off
    * the tree whose visible subtree is the directory's parent, Gezi's directory
    * for an in-tree entry (`at`), so that its imports are written from
    * `gezi "corpora"` (the host does not mount an entry in a tree). Throws
    * `EntryDataError` for a directory with no `entry.lambdalattice` or with an
    * `entry.pl`, which is no term and cannot be read so (convert it to the
    * single entry file), and as `at` does. Read under the reading state given,
    * which it returns.
    */
  def read(
      entryDirectory: Path,
      state: ReadingState[NoFacts.type]
  ): (EntryData, ReadingState[NoFacts.type]) =
    val directory = entryDirectory.toAbsolutePath.normalize
    val file = directory.resolve("entry.lambdalattice")
    if Files.isRegularFile(directory.resolve("entry.pl")) then
      throw EntryDataError(
        s"$entryDirectory holds an entry.pl, which is no term: write its settings in entry.lambdalattice"
      )
    if !Files.isRegularFile(file) then
      throw EntryDataError(s"$entryDirectory holds no entry.lambdalattice")
    at(directory.getParent, file, state)

  /** The entry of the file at the path, reached by the projections of its
    * absolute path off the root of the tree whose visible subtree is `visible`,
    * and instantiated (`StandardLibrary.entryTerm`), its data read off the term
    * (`entryData`). Throws as `StandardLibrary.entryTerm` and `entryData` do.
    */
  def at(
      visible: Path,
      entry: Path,
      state: ReadingState[NoFacts.type]
  ): (EntryData, ReadingState[NoFacts.type]) =
    val StandardLibrary.EntryReading(term, afterEntry, _, _) =
      StandardLibrary.entryTerm(visible, entry, state)
    entryData(term, Set.empty, afterEntry)

  /** The entry a text writes that stands in no directory, so that it holds no
    * relative path: its terms are closed terms written out, read once from
    * `KnowledgeReading.startingState`. Throws as `entryData` does.
    */
  def lambdalatticeRead(text: String): EntryData =
    entryData(
      Defunctionalization.thunkInstruction[NoFacts.type](
        Lambdalattice.term(text)
      ),
      Set.empty,
      KnowledgeReading.startingState
    )._1

  /** The evaluator steps an `entry.lambdalattice` may take to read: its
    * compiler's tuple, its rounds' list, each round's tuple and options
    * coproduct, and the backend's tuple and options coproduct; the knowledge of
    * its rounds and its backend is read by the library under the library's own
    * limit. MEASURED 2026-11-21, before the slots `construction` and
    * `constant_storage_stop` were added, by a scratch munit probe in
    * contest-entry, not committed: `EntryData.read` of each in-tree entry from
    * `Defaults.entryDataState`, the spent budget of `entryData`'s one
    * `KnowledgeReading.run`, at most 3,165 steps (contest-entries-wren's, four
    * rounds); not measured again since the two slots were added. The limit is
    * about 5 times that largest reading.
    */
  private val lambdalatticeReadingLimit: Long = 16000L

  /** The entry of the term of an `entry.lambdalattice`, a tuple whose one field
    * is the compiler `compiler(rounds, backend)`
    * (`KnowledgeReading.soleField`), read under weak head (`KnowledgeReading`).
    * Every product the entry alone writes is a Scott tuple of its fields in
    * order; every knowledge is a knowledge mixin (`KnowledgeFileReading`), and
    * the options of a round and of the backend are a fixed-width mixin with no
    * self, a multi-valued Scott coproduct
    * (`KnowledgeReading.coproductGroupSlots`) of groups of slots, so that
    * several presets and the entry contribute to them by the choice and nothing
    * is read by a name, a string key being forbidden (a fixed-width mixin that
    * needs no self reference is a multi-valued Scott coproduct):
    *
    * {{{
    * compiler         λs. s rounds backend
    * rounds           a Scott list of rounds, in order
    * round            λs. s knowledge options
    *   options          groups implementations behaviour
    *   implementations  slots indexer orientation_compiler saturator extractor lemma_encoding ematching
    *   behaviour        slots opening rules respellings write_back_spellings opening_criterion constant_storage_stop
    * backend          λs. s knowledge options
    *   options          groups jit instances reading execution
    *   jit              slots dispatch implementation granularity native_blocks budget trial
    *   instances        slots instance_table instance_retention checkpoints lookahead instance_reuse
    *   reading          slots application table_sharing table_retention continuation parallel
    *   execution        slots executor compilation_place occurrence_tagging group_blocks
    * }}}
    *
    * A contribution to a slot is an injection into its group and the group's
    * slot, `λ_ _ reading _. reading λ_ _ table_retention _. table_retention
    * no_tables_kept`; one contribution may write several, a choice under the
    * handlers. The bodies of `rules`, a set, are joined; every other slot takes
    * one value, its bodies read each and equal readings one.
    *
    * `opening` and `instance_table` are Scott booleans, `λt. λf. t` for true;
    * `rules` a choice of constructors of BuiltInRule's list, top for none;
    * `extractor` narrow_block or narrow_list_block applied to its enumeration
    * bound, a positive integer literal, and its whole fold bound, a
    * non-negative one, or `module` applied to a module's selector and its
    * parameters, both read back unevaluated (`ExtractorImplementation`);
    * `budget` a non-negative integer literal and `trial` a positive one;
    * `executor` `jit`, or `module` applied to a module's selector and its
    * parameters, both read back unevaluated (`ExecutorOption`); every other
    * field a constructor of its published list (THE OPTIONS AS SCOTT
    * CONSTRUCTORS, above), read by its structure, the alternative it takes of
    * its list. A round's knowledge and the backend's are read as their author
    * wrote them, the instructions of `names` kept as constants
    * (`KnowledgeReading.term`). Throws `EntryDataError` for a slot that no
    * contribution writes, a slot but `rules` whose contributions read as two
    * different values, a body that is a choice of two values, and a value of
    * another shape.
    */
  def entryData(
      entry: Configured[NoFacts.type],
      names: Set[Configured[NoFacts.type]],
      state: ReadingState[NoFacts.type]
  ): (EntryData, ReadingState[NoFacts.type]) =
    try
      KnowledgeReading.run(
        KnowledgeReading.soleField(Value.of(entry)).flatMap(compiler(_, names)),
        lambdalatticeReadingLimit,
        state
      )
    catch
      case KnowledgeReadingError(reason) =>
        throw EntryDataError(s"entry.lambdalattice: $reason")

  private def compiler(
      entry: Value[NoFacts.type],
      names: Set[Configured[NoFacts.type]]
  ): Reading[EntryData] =
    for
      compilerFields <- KnowledgeReading.fields(entry, 2)
      Vector(roundsValue, backendValue) = (compilerFields: @unchecked)
      roundValues <- once("rounds", KnowledgeReading.itemsWritten(roundsValue))
      rounds <- Computation.traversed(roundValues)(round(_, names))
      backendFields <- KnowledgeReading.fields(backendValue, 2)
      Vector(knowledge, optionsValue) = (backendFields: @unchecked)
      groups <- KnowledgeReading.coproductGroupSlots(
        optionsValue,
        backendGroupWidths
      )
      Vector(jitSlots, instanceSlots, readingSlots, executionSlots) =
        (groups: @unchecked)
      jit <- options(jitSlots, instanceSlots)
      reading <- readingOptions(readingSlots)
      Vector(
        executorBodies,
        compilationPlaceBodies,
        occurrenceTaggingBodies,
        groupBlocksBodies
      ) = (executionSlots: @unchecked)
      executor <- single("executor", executorBodies)(executor(_, names))
      compilationPlace <- single("compilation_place", compilationPlaceBodies)(
        compilationPlace
      )
      occurrenceTagging <- single(
        "occurrence_tagging",
        occurrenceTaggingBodies
      )(
        constructor(
          "occurrence_tagging",
          _,
          OccurrenceTaggingOption.values.toVector
        )
      )
      groupBlocks <- single("group_blocks", groupBlocksBodies)(groupBlocks)
    yield
      // FIXME: a closure unit's tags are numbered with the whole program's, so they change with the let's body and https://github.com/Atry/private-overlay/issues/2216
      // the cache never hits; the two options are refused together until the unit is cut before the tagging.
      if compilationPlace == CompilationPlaceOption.Upfront(
          UnitSelectionOption.LetBoundClosure
        ) &&
        occurrenceTagging == OccurrenceTaggingOption.NamesAndClosures
      then
        throw EntryDataError(
          "entry.lambdalattice: compilation_place upfront let_bound_closure with occurrence_tagging names_and_closures: a closure unit's tags change with each point, so its artifact is never read again"
        )
      EntryData(
        rounds,
        KnowledgeReading.term(knowledge, names),
        jit,
        reading,
        executor,
        compilationPlace,
        occurrenceTagging,
        groupBlocks
      )

  /** The widths of the groups of a round's options, `implementations` and
    * `behaviour`.
    */
  val roundGroupWidths: Vector[Int] = Vector(6, 6)

  /** The widths of the groups of the backend's options, `jit`, `instances`,
    * `reading` and `execution`.
    */
  val backendGroupWidths: Vector[Int] = Vector(6, 5, 5, 4)

  private def round(
      value: Value[NoFacts.type],
      names: Set[Configured[NoFacts.type]]
  ): Reading[EntryRound] =
    for
      roundFields <- KnowledgeReading.fields(value, 2)
      Vector(knowledge, optionsValue) = (roundFields: @unchecked)
      groups <- KnowledgeReading.coproductGroupSlots(
        optionsValue,
        roundGroupWidths
      )
      Vector(implementations, behaviour) = (groups: @unchecked)
      Vector(
        indexerBodies,
        orientationBodies,
        saturatorBodies,
        extractorBodies,
        encodingBodies,
        ematchingBodies
      ) = (implementations: @unchecked)
      Vector(
        openingBodies,
        rulesBodies,
        respellingsBodies,
        writeBackBodies,
        openingCriterionBodies,
        stopBodies
      ) = (behaviour: @unchecked)
      opening <- single("opening", openingBodies)(truth("opening", _))
      rules <- Computation
        .traversed(rulesBodies)(
          KnowledgeReading.alternatives(_, BuiltInRule.values.size)
        )
        .map(_.flatten)
      indexer <- single("indexer", indexerBodies)(
        constructor("indexer", _, IndexerImplementation.values.toVector)
      )
      orientationCompiler <- single("orientation_compiler", orientationBodies)(
        constructor(
          "orientation_compiler",
          _,
          OrientationCompilerImplementation.values.toVector
        )
      )
      saturator <- single("saturator", saturatorBodies)(
        constructor("saturator", _, SaturatorImplementation.values.toVector)
      )
      extractor <- single("extractor", extractorBodies)(extractor(_, names))
      lemmaEncoding <- single("lemma_encoding", encodingBodies)(
        constructor(
          "lemma_encoding",
          _,
          LemmaEncodingImplementation.values.toVector
        )
      )
      ematching <- single("ematching", ematchingBodies)(
        constructor("ematching", _, EmatchingImplementation.values.toVector)
      )
      respellings <- single("respellings", respellingsBodies)(
        constructor("respellings", _, MemoRetentionOption.values.toVector)
      )
      writeBackSpellings <- single("write_back_spellings", writeBackBodies)(
        constructor(
          "write_back_spellings",
          _,
          WriteBackSpellingsOption.values.toVector
        )
      )
      openingCriterion <- single("opening_criterion", openingCriterionBodies)(
        constructor(
          "opening_criterion",
          _,
          OpeningCriterionOption.values.toVector
        )
      )
      constantStorageStop <- single("constant_storage_stop", stopBodies)(
        truth("constant_storage_stop", _)
      )
      builtInRules = rules.map {
        case (position, Vector()) => BuiltInRule.values(position)
        case (_, other)           =>
          throw EntryDataError(
            s"entry.lambdalattice: a built-in rule has ${other.size} fields"
          )
      }.toSet
      _ =
        if constantStorageStop && builtInRules.contains(BuiltInRule.StorageView)
        then
          throw EntryDataError(
            "entry.lambdalattice: a round chooses both constant_storage_stop and the rule storage_view, whose purposes are opposite"
          )
    yield EntryRound(
      KnowledgeReading.term(knowledge, names),
      RoundSettings(
        opening,
        builtInRules,
        indexer,
        orientationCompiler,
        saturator,
        extractor,
        lemmaEncoding,
        ematching,
        respellings,
        writeBackSpellings,
        openingCriterion,
        constantStorageStop
      )
    )

  /** The JIT's options of the bodies of the slots of the groups `jit` and
    * `instances`.
    */
  private def options(
      jit: Vector[Vector[Value[NoFacts.type]]],
      instances: Vector[Vector[Value[NoFacts.type]]]
  ): Reading[JitOptions] =
    def positive(field: String, value: Value[NoFacts.type]): Reading[BigInt] =
      once(field, KnowledgeReading.integerWritten(value)).map(read =>
        if read > 0 then read
        else
          throw EntryDataError(
            s"the JIT option $field is $read, not a positive integer"
          )
      )
    def nonNegative(
        field: String,
        value: Value[NoFacts.type]
    ): Reading[BigInt] =
      once(field, KnowledgeReading.integerWritten(value)).map(read =>
        if read >= 0 then read
        else
          throw EntryDataError(
            s"the JIT option $field is $read, not a non-negative integer"
          )
      )
    val Vector(
      dispatchBodies,
      implementationBodies,
      granularityBodies,
      nativeBlocksBodies,
      budgetBodies,
      trialBodies
    ) = (jit: @unchecked)
    val Vector(
      instanceTableBodies,
      instanceRetentionBodies,
      checkpointsBodies,
      lookaheadBodies,
      instanceReuseBodies
    ) = (instances: @unchecked)
    for
      dispatch <- single("dispatch", dispatchBodies)(
        constructor("dispatch", _, DispatchOption.values.toVector)
      )
      implementation <- single("implementation", implementationBodies)(
        constructor("implementation", _, BackendOption.values.toVector)
      )
      granularity <- single("granularity", granularityBodies)(
        constructor("granularity", _, GranularityOption.values.toVector)
      )
      instanceTable <- single("instance_table", instanceTableBodies)(
        truth("instance_table", _)
      )
      trial <- single("trial", trialBodies)(positive("trial", _))
      instanceRetention <- single(
        "instance_retention",
        instanceRetentionBodies
      )(instanceRetention)
      budget <- single("budget", budgetBodies)(nonNegative("budget", _))
      checkpoints <- single("checkpoints", checkpointsBodies)(checkpoints)
      lookahead <- single("lookahead", lookaheadBodies)(lookahead)
      instanceReuse <- single("instance_reuse", instanceReuseBodies)(
        constructor("instance_reuse", _, InstanceReuseOption.values.toVector)
      )
      nativeBlocks <- single("native_blocks", nativeBlocksBodies)(
        constructor("native_blocks", _, NativeBlocksOption.values.toVector)
      )
    yield JitOptions(
      dispatch,
      implementation,
      granularity,
      instanceTable,
      if trial.isValidLong then trial.toLong
      else
        throw EntryDataError(
          s"the JIT option trial is $trial, above the largest it may be"
        )
      ,
      instanceRetention,
      if budget.isValidInt then budget.toInt
      else
        throw EntryDataError(
          s"the JIT option budget is $budget, above the largest it may be"
        )
      ,
      checkpoints,
      nativeBlocks,
      lookahead,
      instanceReuse
    )

  /** The extraction of a round's field `extractor`: `narrow_block` or
    * `narrow_list_block` with its enumeration bound, a positive integer
    * literal, and its whole fold bound, a non-negative one; or `module` with
    * its selector and its parameters, each read back to the IR unevaluated
    * (`KnowledgeReading.term`). Throws `EntryDataError` for a field that is not
    * written, is no constructor of the list, or has bounds of another shape.
    */
  private def extractor(
      value: Value[NoFacts.type],
      names: Set[Configured[NoFacts.type]]
  ): Reading[ExtractorImplementation] =
    once("extractor", KnowledgeReading.alternativeWritten(value, 3)).flatMap {
      case (position @ (0 | 1), Vector(enumeration, wholeFold)) =>
        for
          enumerationBound <- once(
            "extractor's enumeration bound",
            KnowledgeReading.integerWritten(enumeration)
          )
          wholeFoldBound <- once(
            "extractor's whole fold bound",
            KnowledgeReading.integerWritten(wholeFold)
          )
        yield
          if enumerationBound > 0 && enumerationBound.isValidLong && wholeFoldBound >= 0 && wholeFoldBound.isValidLong
          then
            if position == 0 then
              ExtractorImplementation.NarrowBlock(
                enumerationBound.toLong,
                wholeFoldBound.toLong
              )
            else
              ExtractorImplementation.NarrowListBlock(
                enumerationBound.toLong,
                wholeFoldBound.toLong
              )
          else
            throw EntryDataError(
              s"entry.lambdalattice: the extractor's bounds are $enumerationBound and $wholeFoldBound, not a positive and a non-negative integer of 64 bits"
            )
      case (2, Vector(selector, parameters)) =>
        Computation.pure(
          ExtractorImplementation.Module(
            KnowledgeReading.term(selector, names),
            KnowledgeReading.term(parameters, names)
          )
        )
      case (position, other) =>
        throw EntryDataError(
          s"entry.lambdalattice: the field extractor's alternative $position has ${other.size} fields"
        )
    }

  /** The checkpoint policy of the field `checkpoints`: `profitable`, or
    * `every_steps` with its interval, a non-negative integer literal. Throws
    * `EntryDataError` for a field that is not written, is no constructor of the
    * list, or has an interval of another shape.
    */
  private def checkpoints(
      value: Value[NoFacts.type]
  ): Reading[CheckpointOption] =
    once("checkpoints", KnowledgeReading.alternativeWritten(value, 2)).flatMap {
      case (0, Vector()) => Computation.pure(CheckpointOption.Profitable)
      case (1, Vector(interval)) =>
        once("checkpoints' interval", KnowledgeReading.integerWritten(interval))
          .map(read =>
            if read >= 0 && read.isValidLong then
              CheckpointOption.EverySteps(read.toLong)
            else
              throw EntryDataError(
                s"entry.lambdalattice: the checkpoint interval is $read, not a non-negative integer of 64 bits"
              )
          )
      case (position, other) =>
        throw EntryDataError(
          s"entry.lambdalattice: the field checkpoints' alternative $position has ${other.size} fields"
        )
    }

  /** The lookahead of the field `lookahead`: `lazily`, or `within_steps` with
    * its steps, a positive integer literal. Throws `EntryDataError` for a field
    * that is not written, is no constructor of the list, or has steps of
    * another shape.
    */
  private def lookahead(value: Value[NoFacts.type]): Reading[LookaheadOption] =
    once("lookahead", KnowledgeReading.alternativeWritten(value, 2)).flatMap {
      case (0, Vector())      => Computation.pure(LookaheadOption.Lazily)
      case (1, Vector(steps)) =>
        once("lookahead's steps", KnowledgeReading.integerWritten(steps)).map(
          read =>
            if read > 0 && read.isValidLong then
              LookaheadOption.WithinSteps(read.toLong)
            else
              throw EntryDataError(
                s"entry.lambdalattice: the lookahead's steps are $read, not a positive integer of 64 bits"
              )
        )
      case (position, other) =>
        throw EntryDataError(
          s"entry.lambdalattice: the field lookahead's alternative $position has ${other.size} fields"
        )
    }

  /** The instance retention of the field `instance_retention`: `generations`
    * with its size, a positive integer literal, or `never_dropped`. Throws
    * `EntryDataError` for a field that is not written, is no constructor of the
    * list, or has a size of another shape.
    */
  private def instanceRetention(
      value: Value[NoFacts.type]
  ): Reading[InstanceRetentionOption] =
    once("instance_retention", KnowledgeReading.alternativeWritten(value, 2))
      .flatMap {
        case (0, Vector(size)) =>
          once(
            "instance_retention's size",
            KnowledgeReading.integerWritten(size)
          ).map(read =>
            if read > 0 && read.isValidInt then
              InstanceRetentionOption.Generations(read.toInt)
            else
              throw EntryDataError(
                s"entry.lambdalattice: the generation size is $read, not a positive integer of 32 bits"
              )
          )
        case (1, Vector()) =>
          Computation.pure(InstanceRetentionOption.NeverDropped)
        case (position, other) =>
          throw EntryDataError(
            s"entry.lambdalattice: the field instance_retention's alternative $position has ${other.size} fields"
          )
      }

  /** The group blocks of the field `group_blocks`: `no_group_blocks`, or
    * `group_blocks_enabled` with its share, an integer literal from 1 to 100
    * percent, its dense cells, a natural literal of 32 bits, and its backend, a
    * constructor of entry_options/group_backend. Throws `EntryDataError` for a
    * field that is not written, is no constructor of the list, or has a field
    * of another shape.
    */
  private def groupBlocks(
      value: Value[NoFacts.type]
  ): Reading[GroupBlocksOption] =
    once("group_blocks", KnowledgeReading.alternativeWritten(value, 2))
      .flatMap {
        case (0, Vector()) => Computation.pure(GroupBlocksOption.None)
        case (1, Vector(share, cells, backend)) =>
          once("group_blocks's share", KnowledgeReading.integerWritten(share))
            .flatMap(sharePercent =>
              once(
                "group_blocks's dense cells",
                KnowledgeReading.integerWritten(cells)
              ).flatMap(denseCells =>
                once(
                  "group_blocks's backend",
                  KnowledgeReading.alternativeWritten(
                    backend,
                    GroupBackendOption.values.size
                  )
                ).map {
                  case (position, Vector()) =>
                    if sharePercent < 1 || sharePercent > 100 then
                      throw EntryDataError(
                        s"entry.lambdalattice: the group blocks' share is $sharePercent, not a percent from 1 to 100"
                      )
                    else if denseCells < 0 || !denseCells.isValidInt then
                      throw EntryDataError(
                        s"entry.lambdalattice: the group blocks' dense cells are $denseCells, not a natural of 32 bits, the cells a table holds"
                      )
                    else
                      GroupBlocksOption.Enabled(
                        sharePercent.toInt,
                        denseCells.toLong,
                        GroupBackendOption.fromOrdinal(position)
                      )
                  case (position, other) =>
                    throw EntryDataError(
                      s"entry.lambdalattice: the group blocks' backend, alternative $position, has ${other.size} fields"
                    )
                }
              )
            )
        case (position, other) =>
          throw EntryDataError(
            s"entry.lambdalattice: the field group_blocks's alternative $position has ${other.size} fields"
          )
      }

  /** The reading's options of the bodies of the slots of the group `reading`.
    */
  private def readingOptions(
      reading: Vector[Vector[Value[NoFacts.type]]]
  ): Reading[ReadingOptions] =
    val Vector(
      applicationBodies,
      tableSharingBodies,
      tableRetentionBodies,
      continuationBodies,
      parallelBodies
    ) = (reading: @unchecked)
    for
      application <- single("application", applicationBodies)(
        constructor("application", _, ApplicationOption.values.toVector)
      )
      tableSharing <- single("table_sharing", tableSharingBodies)(
        constructor("table_sharing", _, TableSharingOption.values.toVector)
      )
      tableRetention <- single("table_retention", tableRetentionBodies)(
        tableRetention
      )
      continuation <- single("continuation", continuationBodies)(
        constructor("continuation", _, ContinuationOption.values.toVector)
      )
      parallel <- single("parallel", parallelBodies)(
        constructor("parallel", _, ParallelOption.values.toVector)
      )
    yield ReadingOptions(
      application,
      tableSharing,
      tableRetention,
      continuation,
      parallel
    )

  /** The executor of the field `executor`: `jit`, or `module` with its selector
    * and its parameters, each read back to the IR unevaluated
    * (`KnowledgeReading.term`). Throws `EntryDataError` for a field that is not
    * written or is no constructor of the list.
    */
  private def executor(
      value: Value[NoFacts.type],
      names: Set[Configured[NoFacts.type]]
  ): Reading[ExecutorOption] =
    once("executor", KnowledgeReading.alternativeWritten(value, 2)).map {
      case (0, Vector())                     => ExecutorOption.Jit
      case (1, Vector(selector, parameters)) =>
        ExecutorOption.Module(
          KnowledgeReading.term(selector, names),
          KnowledgeReading.term(parameters, names)
        )
      case (position, other) =>
        throw EntryDataError(
          s"entry.lambdalattice: the field executor's alternative $position has ${other.size} fields"
        )
    }

  /** The place of the field `compilation_place`: `upfront` with the units of
    * its one field, a constructor of `unit_selection`, or `by_executor`. Throws
    * `EntryDataError` for a field that is not written, is no constructor of the
    * list, or has a field of another shape.
    */
  private def compilationPlace(
      value: Value[NoFacts.type]
  ): Reading[CompilationPlaceOption] =
    once("compilation_place", KnowledgeReading.alternativeWritten(value, 2))
      .flatMap {
        case (0, Vector(units)) =>
          constructor(
            "unit_selection",
            units,
            UnitSelectionOption.values.toVector
          ).map(CompilationPlaceOption.Upfront(_))
        case (1, Vector()) =>
          Computation.pure(CompilationPlaceOption.ByExecutor)
        case (position, other) =>
          throw EntryDataError(
            s"entry.lambdalattice: the field compilation_place's alternative $position has ${other.size} fields"
          )
      }

  /** The retention of the field `table_retention`: `kept_all`, `none_kept`, or
    * `dropped_at_percent` with its share, an integer literal from 1 to 100.
    * Throws `EntryDataError` for a field that is not written, is no constructor
    * of the list, or has a share of another shape.
    */
  private def tableRetention(
      value: Value[NoFacts.type]
  ): Reading[TableRetentionOption] =
    once("table_retention", KnowledgeReading.alternativeWritten(value, 3))
      .flatMap {
        case (0, Vector()) => Computation.pure(TableRetentionOption.KeptAll)
        case (1, Vector()) => Computation.pure(TableRetentionOption.NoneKept)
        case (2, Vector(percent)) =>
          once(
            "table_retention's share",
            KnowledgeReading.integerWritten(percent)
          ).map(read =>
            if read >= 1 && read <= 100 then
              TableRetentionOption.DroppedAtPercent(read.toInt)
            else
              throw EntryDataError(
                s"entry.lambdalattice: the table retention's share is $read, not an integer from 1 to 100"
              )
          )
        case (position, other) =>
          throw EntryDataError(
            s"entry.lambdalattice: the field table_retention's alternative $position has ${other.size} fields"
          )
      }

  /** The one value the bodies of an option's slot read as, each body read by
    * `read` and equal readings one: the contributions of several presets and of
    * the entry may write the same value. Throws `EntryDataError` for a slot
    * that no contribution writes and for one whose contributions read as
    * different values, so that a conflict between contributions is reported,
    * never settled by the order of the heads.
    */
  private def single[Read](slot: String, bodies: Vector[Value[NoFacts.type]])(
      read: Value[NoFacts.type] => Reading[Read]
  ): Reading[Read] =
    Computation
      .traversed(bodies)(read)
      .map(_.distinct match
        case Vector(value) => value
        case Vector()      =>
          throw EntryDataError(
            s"entry.lambdalattice: the option $slot is not written"
          )
        case values =>
          throw EntryDataError(
            s"entry.lambdalattice: the option $slot is written with ${values.size} different values: ${values.mkString(", ")}"
          ))

  /** What the field's reading gave. Throws `EntryDataError` for a field that is
    * not written.
    */
  private def once[Read](
      field: String,
      reading: Reading[Option[Read]]
  ): Reading[Read] =
    reading.map(
      _.getOrElse(
        throw EntryDataError(
          s"entry.lambdalattice: the field $field is not written"
        )
      )
    )

  private def truth(
      field: String,
      value: Value[NoFacts.type]
  ): Reading[Boolean] =
    once(field, KnowledgeReading.alternativeWritten(value, 2)).map {
      case (position, Vector()) => position == 0
      case (_, other)           =>
        throw EntryDataError(
          s"entry.lambdalattice: the field $field is no boolean: it has ${other.size} fields"
        )
    }

  /** The case of the published list the field's constructor takes, by the
    * position of its alternative among the list's cases. Throws
    * `EntryDataError` for a field that is not written or is no constructor of
    * no field.
    */
  private def constructor[Option](
      field: String,
      value: Value[NoFacts.type],
      published: Vector[Option]
  ): Reading[Option] =
    once(field, KnowledgeReading.alternativeWritten(value, published.size))
      .map {
        case (position, Vector()) => published(position)
        case (_, other)           =>
          throw EntryDataError(
            s"entry.lambdalattice: the field $field is no constructor: it has ${other.size} fields"
          )
      }

/** The text of an `entry.lambdalattice` as `EntryData.entryData` reads it, for
  * the code that writes one: a test's entry, or a conversion.
  */
object EntryText:

  private given NoFacts.type = NoFacts

  /** The constructor of the case's position among its list's cases, written
    * closed, `λalternative_0. … λalternative_n. alternative_position`: the term
    * the list's file under corpora/compiler/entry_options gives for it, since
    * α-equivalent terms are one term, and a text read outside the source trees
    * reaches no library.
    */
  private def constructor(position: Int, count: Int): String =
    (0 until count)
      .map(alternative => s"λalternative_$alternative. ")
      .mkString("(", "", s"alternative_$position)")

  /** The text of the library's Scott integer of the value. */
  private def integer(value: BigInt): String =
    s"(${Lambdalattice.text(Literals.integerTerm(value), Map.empty)})"

  private def truth(value: Boolean): String =
    if value then "(λt. λf. t)" else "(λt. λf. f)"

  /** The text of a round's extraction, its constructor applied to its fields; a
    * module's selector and parameters written out from their instructions
    * (`Defunctionalization.instructionTerm`), which holds for a closed term
    * with no URI node and throws as `Lambdalattice.text` does for another.
    */
  private def extractor(implementation: ExtractorImplementation): String =
    implementation match
      case ExtractorImplementation.NarrowBlock(
            enumerationBound,
            wholeFoldBound
          ) =>
        s"((λenumeration_bound. λwhole_fold_bound. λnarrow_block. λnarrow_list_block. λmodule. narrow_block enumeration_bound whole_fold_bound) ${integer(
            BigInt(enumerationBound)
          )} ${integer(BigInt(wholeFoldBound))})"
      case ExtractorImplementation.NarrowListBlock(
            enumerationBound,
            wholeFoldBound
          ) =>
        s"((λenumeration_bound. λwhole_fold_bound. λnarrow_block. λnarrow_list_block. λmodule. narrow_list_block enumeration_bound whole_fold_bound) ${integer(
            BigInt(enumerationBound)
          )} ${integer(BigInt(wholeFoldBound))})"
      case ExtractorImplementation.Module(selector, parameters) =>
        moduleExtractor(
          Lambdalattice
            .text(Defunctionalization.instructionTerm(selector), Map.empty),
          Lambdalattice.text(
            Defunctionalization.instructionTerm(parameters),
            Map.empty
          )
        )

  /** The constructor `module` of the extractors' list applied to the texts of a
    * module's selector and of its parameters, each a closed term.
    */
  def moduleExtractor(selector: String, parameters: String): String =
    s"((λselector. λparameters. λnarrow_block. λnarrow_list_block. λmodule. module selector parameters) ($selector) ($parameters))"

  /** The text of the library's Scott list of the closed items' texts, nil
    * `λn. λc. n` and a cell `λn. λc. c h t` (`Literals.textTerm`'s encoding),
    * each item in parentheses and the cells joined by the separator: a bracket
    * is a CBOR array literal and no list of terms.
    */
  def scottList(items: Seq[String], separator: String): String =
    items.foldRight("(λn. λc. n)")((item, tail) =>
      s"(λn. λc. c ($item)$separator$tail)"
    )

  /** top, the knowledge of no file and the empty set of rules. */
  private val nothing: String =
    s"(${Lambdalattice.text(Literals.top, Map.empty)})"

  /** The choice of the texts, top for none. */
  private def choice(texts: Vector[String]): String =
    if texts.isEmpty then nothing else texts.mkString("(", " + ", ")")

  /** A value's text written in an option's slot: the slot `slot` of the group
    * `group` of an options coproduct.
    */
  final case class OptionSlot(group: Int, slot: Int, value: String)

  /** One contribution to an options coproduct of groups of the widths that
    * writes each slot given with its value, a choice under the handlers,
    * `(λgroup_0 … group_g. (group_i λslot_0 … slot_n. (slot_j a + slot_k b) + …))`;
    * top for no slot. Several contributions are joined by the choice.
    */
  def contribution(
      groupWidths: Vector[Int],
      slots: Vector[OptionSlot]
  ): String =
    if slots.isEmpty then nothing
    else
      val groups = slots
        .groupBy(_.group)
        .toVector
        .sortBy(_._1)
        .map((group, written) =>
          val handlers = (0 until groupWidths(group))
            .map(slot => s"slot_$slot")
            .mkString(" ")
          s"group_$group (λ$handlers. ${written.map(found => s"slot_${found.slot} ${found.value}").mkString("(", " + ", ")")})"
        )
      s"(λ${groupWidths.indices.map(group => s"group_$group").mkString(" ")}. ${groups.mkString("(", " + ", ")")})"

  /** The slots a round's settings write, in `EntryData.roundGroupWidths`'
    * groups: `rules` one slot for each rule, none for no rule.
    */
  def roundSlots(settings: RoundSettings): Vector[OptionSlot] =
    val rules = BuiltInRule.values.toVector
      .filter(settings.builtInRules)
      .map(rule =>
        OptionSlot(1, 1, constructor(rule.ordinal, BuiltInRule.values.size))
      )
    Vector(
      OptionSlot(
        0,
        0,
        constructor(settings.indexer.ordinal, IndexerImplementation.values.size)
      ),
      OptionSlot(
        0,
        1,
        constructor(
          settings.orientationCompiler.ordinal,
          OrientationCompilerImplementation.values.size
        )
      ),
      OptionSlot(
        0,
        2,
        constructor(
          settings.saturator.ordinal,
          SaturatorImplementation.values.size
        )
      ),
      OptionSlot(0, 3, extractor(settings.extractor)),
      OptionSlot(
        0,
        4,
        constructor(
          settings.lemmaEncoding.ordinal,
          LemmaEncodingImplementation.values.size
        )
      ),
      OptionSlot(
        0,
        5,
        constructor(
          settings.ematching.ordinal,
          EmatchingImplementation.values.size
        )
      ),
      OptionSlot(1, 0, truth(settings.opening)),
      OptionSlot(
        1,
        2,
        constructor(
          settings.respellings.ordinal,
          MemoRetentionOption.values.size
        )
      ),
      OptionSlot(
        1,
        3,
        constructor(
          settings.writeBackSpellings.ordinal,
          WriteBackSpellingsOption.values.size
        )
      ),
      OptionSlot(
        1,
        4,
        constructor(
          settings.openingCriterion.ordinal,
          OpeningCriterionOption.values.size
        )
      ),
      OptionSlot(1, 5, truth(settings.constantStorageStop))
    ) ++ rules

  /** A round, `λs. s knowledge options`: its knowledge the choice of the texts
    * given, each a knowledge mixin written out or a term that gives one, and
    * its options the choice of the contributions given (`contribution` of
    * `EntryData.roundGroupWidths`), top for none.
    */
  def round(knowledge: Vector[String], options: Vector[String]): String =
    s"(λs. s ${choice(knowledge)} ${choice(options)})"

  /** The constructor `jit` of the executors' list, the framework's executor. */
  val jitExecutor: String = constructor(0, 2)

  /** The constructor `module` of the executors' list applied to the texts of a
    * module's selector and of its parameters, each a closed term.
    */
  def moduleExecutor(selector: String, parameters: String): String =
    s"((λselector. λparameters. λjit. λmodule. module selector parameters) ($selector) ($parameters))"

  /** The slots the backend's options write, in `EntryData.backendGroupWidths`'
    * groups `jit`, `instances`, `reading` and `execution`, the executor's slot
    * written with the text given (`jitExecutor`, `moduleExecutor`), the
    * compilation's place and the occurrence tagging with the constructors of
    * the options given.
    */
  def backendSlots(
      jit: JitOptions,
      reading: ReadingOptions,
      executor: String,
      compilationPlace: CompilationPlaceOption,
      occurrenceTagging: OccurrenceTaggingOption,
      groupBlocks: GroupBlocksOption = GroupBlocksOption.None
  ): Vector[OptionSlot] =
    val checkpoints = jit.checkpoints match
      case CheckpointOption.Profitable           => constructor(0, 2)
      case CheckpointOption.EverySteps(interval) =>
        s"((λinterval. λprofitable. λevery_steps. every_steps interval) ${integer(BigInt(interval))})"
    val lookahead = jit.lookahead match
      case LookaheadOption.Lazily             => constructor(0, 2)
      case LookaheadOption.WithinSteps(steps) =>
        s"((λsteps. λlazily. λwithin_steps. within_steps steps) ${integer(BigInt(steps))})"
    val instanceRetention = jit.instanceRetention match
      case InstanceRetentionOption.Generations(size) =>
        s"((λsize. λgenerations. λnever_dropped. generations size) ${integer(BigInt(size))})"
      case InstanceRetentionOption.NeverDropped => constructor(1, 2)
    val tableRetention = reading.tableRetention match
      case TableRetentionOption.KeptAll                   => constructor(0, 3)
      case TableRetentionOption.NoneKept                  => constructor(1, 3)
      case TableRetentionOption.DroppedAtPercent(percent) =>
        s"((λpercent. λkept_all. λnone_kept. λdropped_at_percent. dropped_at_percent percent) ${integer(BigInt(percent))})"
    val groupBlocksText = groupBlocks match
      case GroupBlocksOption.None => constructor(0, 2)
      case GroupBlocksOption.Enabled(sharePercent, denseCells, backend) =>
        s"((λshare_percent. λdense_cells. λbackend. λno_group_blocks. λgroup_blocks_enabled. group_blocks_enabled share_percent dense_cells backend) ${integer(BigInt(sharePercent))} ${integer(BigInt(denseCells))} ${constructor(backend.ordinal, GroupBackendOption.values.size)})"
    val place = compilationPlace match
      case CompilationPlaceOption.Upfront(units) =>
        s"((λunits. λupfront. λby_executor. upfront units) ${constructor(units.ordinal, UnitSelectionOption.values.size)})"
      case CompilationPlaceOption.ByExecutor => constructor(1, 2)
    Vector(
      OptionSlot(
        0,
        0,
        constructor(jit.dispatch.ordinal, DispatchOption.values.size)
      ),
      OptionSlot(
        0,
        1,
        constructor(jit.implementation.ordinal, BackendOption.values.size)
      ),
      OptionSlot(
        0,
        2,
        constructor(jit.granularity.ordinal, GranularityOption.values.size)
      ),
      OptionSlot(
        0,
        3,
        constructor(jit.nativeBlocks.ordinal, NativeBlocksOption.values.size)
      ),
      OptionSlot(0, 4, integer(BigInt(jit.budget))),
      OptionSlot(0, 5, integer(BigInt(jit.instanceTableTrial))),
      OptionSlot(1, 0, truth(jit.instanceTable)),
      OptionSlot(1, 1, instanceRetention),
      OptionSlot(1, 2, checkpoints),
      OptionSlot(1, 3, lookahead),
      OptionSlot(
        1,
        4,
        constructor(jit.instanceReuse.ordinal, InstanceReuseOption.values.size)
      ),
      OptionSlot(
        2,
        0,
        constructor(reading.application.ordinal, ApplicationOption.values.size)
      ),
      OptionSlot(
        2,
        1,
        constructor(
          reading.tableSharing.ordinal,
          TableSharingOption.values.size
        )
      ),
      OptionSlot(2, 2, tableRetention),
      OptionSlot(
        2,
        3,
        constructor(
          reading.continuation.ordinal,
          ContinuationOption.values.size
        )
      ),
      OptionSlot(
        2,
        4,
        constructor(reading.parallel.ordinal, ParallelOption.values.size)
      ),
      OptionSlot(3, 0, executor),
      OptionSlot(3, 1, place),
      OptionSlot(
        3,
        2,
        constructor(
          occurrenceTagging.ordinal,
          OccurrenceTaggingOption.values.size
        )
      ),
      OptionSlot(3, 3, groupBlocksText)
    )

  /** The entry of the rounds (`round`), in order, and of the backend, its
    * knowledge the choice of the texts given and its options the choice of the
    * contributions given (`contribution` of `EntryData.backendGroupWidths`): a
    * tuple of one field, the compiler `λs. s rounds backend`, as
    * `EntryData.entryData` reads it, handed to the file's binder `export`.
    */
  def entry(
      rounds: Vector[String],
      backend: Vector[String],
      options: Vector[String]
  ): String =
    s"λexport. export\n( λs. s\n  ${scottList(rounds, "\n  ")}\n  (λs. s ${choice(backend)} ${choice(options)})\n)\n"
