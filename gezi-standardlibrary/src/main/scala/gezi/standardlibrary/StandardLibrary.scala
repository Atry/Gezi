package gezi.standardlibrary

import gezi.directorysugar.DirectoryTree
import gezi.frontend.Defunctionalization
import gezi.frontend.Literals
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.weakhead.Expansions
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.ir.{Configured, NoFacts, Pure, TermConstruction}

/** A native of the knowledge as a backend checks it: the pure key of the
  * library term it binds and the native's name. A declaration knows no
  * knowledge file: the knowledge is read whole, one term.
  */
final case class BackendNative(instruction: Pure, native: String)

/** A native specialization of the knowledge as a backend checks it: the
  * representation it names, and the `data_family` declarations of the library
  * term it is declared of, in the order of the knowledge (none when the term
  * declares none). A codec's constructors are the terms at the positions of
  * such a family, never named by a name of their own.
  */
final case class BackendSpecialization(
    representation: String,
    families: Vector[Property.DataFamily]
)

/** A backend whose set of facts the compiler checks: it checks the natives and
  * the native specializations of the knowledge files when its set is enabled,
  * throwing `StandardLibraryMalformed` for a malformed one, and does nothing
  * when they are another backend's. This module names no backend; a backend's
  * module implements the trait.
  */
trait LibraryBackend:

  /** Checks the natives and the native specializations, in the order of the
    * knowledge files and of their declarations; an instruction carries its IR,
    * which a check may evaluate.
    */
  def checked(
      natives: Vector[BackendNative],
      specializations: Vector[BackendSpecialization]
  ): Unit

/** A compiled standard library: the index of its facts, whose instructions
  * carry the IR of the terms they bind; the proof metadata of each lemma the
  * knowledge declares, by the lemma's name, the constructor its knowledge file
  * writes read under weak head, which the Lean export reads.
  */
final case class StandardLibrary(
    index: StandardLibraryIndex[NoFacts.type],
    lemmaProofs: Map[String, LemmaProof]
):

  /** The framework's store under no facts: the noinline library terms'
    * instructions noinline.
    */
  def store: Store[NoFacts.type] =
    Store(index.noinline, TermConstruction(NoFacts))

  /** The lemmas a knowledge term declares in its slot `lemmas`, by identity, in
    * ascending order, each lemma the library's of its direction and its two
    * sides: a round's lemmas are those its term writes. A round's term is read
    * off the entry with the library's. Throws `StandardLibraryMalformed` for a
    * knowledge term that does not read and `IllegalArgumentException` for a
    * lemma the library does not hold. Read under the compilation's reading
    * state, which it returns (`KnowledgeReading.run`).
    */
  def lemmas(
      knowledge: Configured[NoFacts.type],
      state: ReadingState[NoFacts.type]
  ): (Vector[LemmaIdentifier], ReadingState[NoFacts.type]) =
    val identifiers = index.lemmaSides
      .map(sides => (sides.left, sides.right) -> sides.lemma)
      .toMap
    val (declarations, after) =
      StandardLibrary.slotRead(knowledge, KnowledgeSlot.Lemmas, state)
    val read = declarations
      .collect { case Declaration.ReadLemma(name, left, right, _) =>
        identifiers.getOrElse(
          (left, right),
          throw IllegalArgumentException(
            s"the lemma $name of a round's knowledge is no lemma of the library"
          )
        )
      }
      .distinct
      .sortBy(_.number)
    (read, after)

  /** The terms a knowledge term writes in its slot `leaves`: a round's leaves,
    * the library terms its e-graph does not unfold. Read under the
    * compilation's reading state, which it returns.
    */
  def leaves(
      knowledge: Configured[NoFacts.type],
      state: ReadingState[NoFacts.type]
  ): (Set[Pure], ReadingState[NoFacts.type]) =
    val (declarations, after) =
      StandardLibrary.slotRead(knowledge, KnowledgeSlot.Leaves, state)
    (
      declarations.collect {
        case Declaration.PropertyBinding(instruction, Property.Noinline) =>
          instruction
      }.toSet,
      after
    )

  // TODO: here stood `knowledgeTerm(paths)` and `lemmasOf(paths)`, which
  // made a round's knowledge of knowledge files named by paths, and `files`
  // and `filesIn`, the table from paths to library terms. The host keeps no
  // table from paths to terms (a library file is no concept of the host): a
  // round's knowledge is a term the entry writes, and a program written in
  // Scala becomes a text read in the tree's context, its names bound by
  // top-level imports. The deleted code:
  // git show cba14d687:lambda_jit/standardlibrary/src/main/scala/lambdajit/standardlibrary/StandardLibrary.scala.

  /** The proof metadata of the lemma of the name, none when the knowledge
    * declares none of the name.
    */
  def lemmaProof(name: String): Option[LemmaProof] = lemmaProofs.get(name)

/** The loader of the standard library: the library is files, reached by paths,
  * and there is no `define`. The interface it reads is the declarations `lemma`
  * and `native` and the combinator properties (`CONTRIBUTING.md`, "Interface"),
  * each binding a term a file gives, never a name.
  *
  * THE SOURCES. A compilation's entry is a source text, and its knowledge is
  * ONE term, a mixin of the fixed-width encoding (`KnowledgeFileReading`): a
  * knowledge file is such a term, and the choice of knowledge files is one. The
  * entry is a file of the source tree, read in the tree's context
  * (`entryTerm`), its knowledge files reached by top-level imports; its term is
  * what its evaluation gives, so it holds the files it imports and never the
  * tree. The host keeps no table of library files.
  *
  * READING. The knowledge is read whole by `KnowledgeFileReading` under weak
  * head (`knowledgeRead`), slot by slot; a round's term is read the same way,
  * and its lemmas and leaves are those it writes (`StandardLibrary.lemmas`,
  * `leaves`).
  *
  * IDENTIFIERS. A lemma is identified by its identifier, one for each key of
  * direction and the instructions of the sides' IR; its name is a display name
  * only (`LemmaNamed`).
  *
  * COMBINATOR PROPERTIES are checked after the facts of every lemma and native
  * are built; a constructor of a data family is identified by its position in
  * the family's constructor list; then each backend checks its set.
  */
object StandardLibrary:

  private given NoFacts.type = NoFacts

  /** The slots of a knowledge term, in the order they are read: the lemmas, the
    * natives, then the entries of `CombinatorPropertyVocabulary` in the
    * vocabulary's order (`KnowledgeSlot`). Seven are fields of the entry's
    * schema: a round's `leaves` and `lemmas`, the backend's `natives`,
    * `representations`, `families`, `fields` and `jvm_types`; the others are
    * the properties the schema leaves out, read all the same.
    */
  val knowledgeSlots: Vector[KnowledgeSlot] = Vector(
    KnowledgeSlot.Lemmas,
    KnowledgeSlot.Natives,
    KnowledgeSlot.Associative,
    KnowledgeSlot.Leaves,
    KnowledgeSlot.NameMarker,
    KnowledgeSlot.ClosureMarker,
    KnowledgeSlot.TagOrigin,
    KnowledgeSlot.TagNext,
    KnowledgeSlot.FirstOrderConstructor,
    KnowledgeSlot.Representations,
    KnowledgeSlot.TypedBranch,
    KnowledgeSlot.Repeller,
    KnowledgeSlot.Families,
    KnowledgeSlot.Fields,
    KnowledgeSlot.JvmTypes
  )

  /** The knowledge of no file: top (`Literals.top`), which writes no slot. */
  val noKnowledge: Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[NoFacts.type](Literals.top)

  /** The evaluator steps one read of a knowledge term may take, each read a
    * fresh budget (`KnowledgeReading.run`): the knowledge read whole
    * (`knowledgeRead`, in `compiled`), and a round's lemmas or leaves read by
    * their slot (`slotRead`, in `lemmas` and `leaves`). MEASURED 2026-11-20
    * (knowledge a fixed-width mixin, each slot's contributions read as one set)
    * by a scratch munit probe in contest-entry, not committed: `EntryData.read`
    * of each in-tree entry from `KnowledgeReading.compilationState`, then
    * `knowledgeRead` of its knowledge (`EntryData.knowledge`) and each round's
    * `lemmas` and `leaves` by slot, the state threaded as
    * `GenericEntryProvider.initialized` threads it; the same on a second run.
    * Steps, with the declarations read:
    *
    * {{{
    * entry                      the knowledge whole    a round's lemmas, the largest    a round's leaves, the largest
    * contest-entries-fixture    114,808 for 138        61,423 for 71                    81 for 34
    * contest-entries-solo       151,677 for 188        13,668 for 19                    98 for 46
    * contest-entries-wren       151,891 for 189         7,673 for 11                    98 for 46
    * }}}
    *
    * The same probe read the knowledge of the fixtures under
    * tests/library_fixtures, each from `KnowledgeReading.compilationState`: the
    * largest, tests/library_fixtures/fixed_width_preset.lambdalattice, 138,073
    * steps for 168 declarations; and the lemmas of each round fixture from
    * `KnowledgeReading.startingState`, as the strategies' tests read them: at
    * most 112,292 steps for 86 declarations
    * (tests/round_fixtures/fixed_width_type_check.lambdalattice). The limit is
    * about 5 times the largest reading, `contest-entries-wren`'s knowledge read
    * whole.
    */
  private val knowledgeReadingLimit: Long = 760000L

  /** The evaluator steps reading an entry's term may take (`entryTerm`) after
    * the projection of the root to the visible subtree, whose steps are limited
    * apart (`projected`). MEASURED 2026-11-23 by a scratch munit probe in
    * contest-entries-plover, not committed: each in-tree entry and the fixture
    * `tests/plover_fixtures/ordered_compositions_entry` (`compositions` below)
    * read by `entryTerm` from `Defaults.entryDataState`, the state the generic
    * entry reads under, Gezi's directory the visible subtree, the limits
    * lifted, at 7 levels (`Path.getNameCount` of the subtree's absolute path,
    * gezi itself included) with 78 members of gezi (76 tracked directories,
    * `target` and one directory left from a deleted module; no file of it is a
    * `.lambdalattice`):
    *
    * {{{
    * commit      fixture   plover    solo     wren     compositions
    * a9945efcb   71,733    138,320   91,558   87,714   135,998
    * eee2e6de1   78,165    144,689   97,895   94,051   142,367
    * }}}
    *
    * Every entry grew by 6,337 to 6,432 steps between the two commits, which
    * split `hindley_milner_unions` into four files and added six files to
    * `corpora/compiler`. Six empty files of the same names added at a9945efcb
    * account for 571 to 742 of those steps.
    *
    * Two terms of the design's cost (`gezi.directorysugar.DirectoryTree`, at
    * `keys`), measured 2026-11-13 on solo's and wren's entries: 216 steps a
    * level (solo, 3,889 over 18 levels; wren 214), and 127 steps a member of
    * Gezi's directory (solo, 6,476 over 51 members; wren 127), since every
    * import's first key, "corpora", is tested at each member.
    *
    * THE LIMIT: plover's reading, the largest, at 7 levels and 78 members
    * (144,689), plus the depth term up to a greatest checkout depth of 32
    * levels (25 × 216 = 5,400), plus the member term up to 110 members of
    * Gezi's directory (32 × 127 = 4,064), plus a margin of five more files at
    * 1,312 steps a file (solo's mean on 2026-11-13, 124,644 steps over the 95
    * files its imports reached, so 6,560), is 160,713, rounded up to the next
    * thousand. A member is a directory whose name does not start with `.`, or a
    * `.lambdalattice` file (`DirectoryTree`). A checkout with more directories
    * left from deleted modules reads higher, 127 steps each, and one not yet
    * built, without `target`, reads lower. CHECKOUTS DEEPER THAN 32 LEVELS, AND
    * A gezi DIRECTORY OF MORE THAN 110 MEMBERS, ARE NOT COVERED: each level
    * beyond adds about 216 steps and each member about 127. Adding a top-level
    * directory to gezi beyond 110 members, a new sbt project being exactly such
    * a directory, means setting the limit again from a measurement. An entry
    * that reaches more than about five files beyond plover's is a finding, and
    * the limit is set again from a measurement. The read's tables, 68,040 for
    * plover, are above a single read's table limit
    * (`ReadingState.defaultTableLimit`, 50,000), and it is made under
    * `KnowledgeReading.compilationState`.
    *
    * The steps are the look-ups' bit-by-bit tests of the keys at each member of
    * each directory on the paths, the cost of the curried partial functions of
    * the vararg literals (9db437731; before them the same imports took 79,686
    * steps), the design's cost as `KnowledgeReading.compilationTableLimit`
    * says.
    */
  private val entryReadingLimit: Long = 161000L

  /** The evaluator steps the projection of a tree's root to its visible subtree
    * may take (`projected`): `projectionBaseSteps` and `projectionStepsPerByte`
    * for each byte of the subtree's absolute path. MEASURED 2026-11-13 (a
    * scratch probe on 815c78ece, synthetic trees under the session's
    * scratchpad, the projection read as `projected` reads it): at 9 levels,
    * 6,334 steps at 110 bytes, 7,394 at 130, 8,454 at 150 and 10,574 at 190, 53
    * per byte and 504 above that; at a fixed length, about 30 steps more per
    * level (7,832 at 20 levels and 132 bytes). A level is at least two bytes,
    * so the projection takes at most 68 steps per byte and about 500 more.
    */
  private val projectionBaseSteps: Long = 1000L

  /** See `projectionBaseSteps`. */
  private val projectionStepsPerByte: Long = 100L

  /** The tables the projection of a tree's root to its visible subtree may add
    * (`projected`): `projectionBaseTables` and `projectionTablesPerByte` for
    * each byte of the subtree's absolute path. MEASURED with
    * `projectionBaseSteps`: at 9 levels, 2,798 tables at 110 bytes, 3,258 at
    * 130, 3,718 at 150 and 4,638 at 190, 23 per byte and 268 above that; at a
    * fixed length, about 15 tables more per level (3,471 at 20 levels and 132
    * bytes), so at most 31 per byte and about 270 more.
    */
  private val projectionBaseTables: Int = 500

  /** See `projectionBaseTables`. */
  private val projectionTablesPerByte: Int = 50

  /** The evaluator steps a read took and the complete tables it added to the
    * state it threads.
    */
  final case class ReadingCost(steps: Long, tables: Int)

  /** The read of an entry's term (`entryTerm`): the term, the state after it,
    * and its cost in two parts reported side by side: the projection of the
    * tree's root to the visible subtree, read first (`projected`), and the read
    * after it, which the limits count.
    */
  final case class EntryReading(
      term: Configured[NoFacts.type],
      state: ReadingState[NoFacts.type],
      projection: ReadingCost,
      read: ReadingCost
  )

  /** The term of the entry at the path: its instance, the projections of its
    * mixin path (`file`, then its absolute path's levels) off the root of the
    * tree whose visible subtree is `visible` (`DirectoryTree`, VISIBLE, a
    * configurable subtree such as the corpora directory), and one more
    * self-application (`DirectoryTree.instance`; an entry is the whole tree
    * projected along a path, several times), applied to a handler, its imports
    * read with it, and read back as the choice of the Scott tuples of its
    * fields (`KnowledgeReading.tuplesTerm`; the file's content is
    * `λexport. … export M1 … Mn`, its imports under `export`), so that the term
    * holds what the imports gave and never the tree. Throws
    * `StandardLibraryMalformed` with `KnowledgeUnread` for an entry that does
    * not read within `entryReadingLimit` after the projection to the visible
    * subtree (`projected`), and as reading a file does. Read under the
    * compilation's reading state, which it returns in the `EntryReading` with
    * the projection's cost and the read's (`KnowledgeReading.run`): the first
    * read of a compilation, which lists the directories on the entry's path
    * under the visible subtree.
    */
  def entryTerm(
      visible: java.nio.file.Path,
      entry: java.nio.file.Path,
      state: ReadingState[NoFacts.type]
  ): EntryReading =
    termRead(visible, DirectoryTree.instance(visible, entry), state)

  /** The one field of the tuple an entry's file returns, a Scott tuple or a
    * knowledge mixin, read off the entry's term (`KnowledgeReading.soleField`)
    * under the state after the entry's read, within `memberReadingLimit`, and
    * the state after it, not evaluated further. Throws
    * `StandardLibraryMalformed` with `KnowledgeUnread` for an entry whose term
    * is no tuple of one field or does not read within the limit.
    */
  def entryGroup(
      reading: EntryReading
  ): (Value[NoFacts.type], ReadingState[NoFacts.type]) =
    try
      KnowledgeReading.run(
        KnowledgeReading.soleField(Value.of(reading.term)),
        memberReadingLimit,
        reading.state
      )
    catch
      case KnowledgeReadingError(reason) =>
        malformed(
          MalformedReason.KnowledgeUnread(
            "the group of an entry's tuple",
            reason
          )
        )

  /** The one member of the entry at the path (`entryTerm`), a file that returns
    * a tuple of one field, read back to a closed instruction
    * (`KnowledgeReading.memberTerm`), with the expansions after the entry's
    * read, as `entryMembers` reads a member. Throws as `entryMembers` does.
    */
  def entryMember(
      visible: java.nio.file.Path,
      entry: java.nio.file.Path,
      expansions: Expansions[NoFacts.type]
  ): (Configured[NoFacts.type], Expansions[NoFacts.type]) =
    val EntryReading(entryInstruction, afterEntry, _, _) = entryTerm(
      visible,
      entry,
      KnowledgeReading.startingState.copy(expansions = expansions)
    )
    val member =
      try
        KnowledgeReading.run(
          KnowledgeReading.memberTerm(Value.of(entryInstruction)),
          memberReadingLimit
        )
      catch
        case KnowledgeReadingError(reason) =>
          malformed(
            MalformedReason.KnowledgeUnread(s"the member of $entry", reason)
          )
    (member, afterEntry.expansions)

  /** The members of the entry at the path (`entryTerm`), a file whose content
    * is the Scott tuple of `arity` public members (`λexport. … export M1 …
    * Mn`), in order, each read back to a closed instruction
    * (`KnowledgeReading.fields`, then `KnowledgeReading.term`, no names), with
    * the expansions after the entry's read, as `entryMember` reads the one
    * member of a file of one. For a data file of the problems' tree whose
    * members the host takes by position, never a compilation. Throws
    * `StandardLibraryMalformed` with `KnowledgeUnread` for a file whose content
    * is no tuple of `arity` fields or does not read within
    * `memberReadingLimit`.
    */
  def entryFields(
      visible: java.nio.file.Path,
      entry: java.nio.file.Path,
      expansions: Expansions[NoFacts.type],
      arity: Int
  ): (Vector[Configured[NoFacts.type]], Expansions[NoFacts.type]) =
    val EntryReading(entryInstruction, afterEntry, _, _) = entryTerm(
      visible,
      entry,
      KnowledgeReading.startingState.copy(expansions = expansions)
    )
    val members =
      try
        KnowledgeReading.run(
          KnowledgeReading
            .fields(Value.of(entryInstruction), arity)
            .map(_.map(KnowledgeReading.term(_, Set.empty))),
          memberReadingLimit
        )
      catch
        case KnowledgeReadingError(reason) =>
          malformed(
            MalformedReason.KnowledgeUnread(
              s"the $arity members of $entry",
              reason
            )
          )
    (members, afterEntry.expansions)

  /** The members of the term table's file under `visible` (`entryTerm`), a file
    * that returns a tuple of one field, the Scott tuple of the table's library
    * terms, each read back to a closed instruction
    * (`KnowledgeReading.soleField`, `KnowledgeReading.fields`, then
    * `KnowledgeReading.term`), by the name the table gives its position
    * (`TermTable`): the file names none, the host reading no string key. For
    * the tests' and the problem generators' data files, never a compilation,
    * which threads its own reading state (`KnowledgeReading.compilationState`):
    * the entry is read under a fresh state, and the members under one fresh
    * state of their own, since they read the entry's term, which holds no
    * directory. The entry is read from the caller's URI expansions
    * (`Expansions`), and the expansions after it are returned with the members,
    * so that an owner reading several entries of one tree lists each directory
    * and parses each file once. Throws `StandardLibraryMalformed` with
    * `KnowledgeUnread` for a file whose field is no tuple of that many terms or
    * does not read within `memberReadingLimit`.
    */
  def entryMembers(
      visible: java.nio.file.Path,
      table: TermTable,
      expansions: Expansions[NoFacts.type]
  ): (Map[String, Configured[NoFacts.type]], Expansions[NoFacts.type]) =
    val entry = visible.resolve(table.file)
    val names = table.names
    val EntryReading(entryInstruction, afterEntry, _, _) = entryTerm(
      visible,
      entry,
      KnowledgeReading.startingState.copy(expansions = expansions)
    )
    val terms =
      try
        KnowledgeReading.run(
          KnowledgeReading
            .soleField(Value.of(entryInstruction))
            .flatMap(group => KnowledgeReading.fields(group, names.size))
            .map(_.map(KnowledgeReading.term(_, Set.empty))),
          memberReadingLimit
        )
      catch
        case KnowledgeReadingError(reason) =>
          malformed(
            MalformedReason.KnowledgeUnread(s"the term table $entry", reason)
          )
    (names.zip(terms).toMap, afterEntry.expansions)

  /** The steps one read of a term table's fields, of an entry's one field or of
    * a library file's member may take (`entryMembers`, `entryGroup`,
    * `entryMember`). MEASURED 2026-11-20, the tables Scott tuples read by
    * position, by a scratch munit probe in contest-entry, not committed, each
    * read from the state after its file's term under
    * `KnowledgeReading.compilationState`: the term tables (`TermTables`) from
    * 22 steps (6 fields) to 64 (tests/jit_fixtures/library_terms, 27 fields),
    * about 2.4 steps a field; the pairs of the program families' configurations
    * 14; `KnowledgeReading.memberTerm` of the 49 one-field library files under
    * tests/standard_library_fixtures at most 6. Read by key, before the tables
    * became Scott tuples, a member took up to 5,294 steps, its literal taken
    * apart bit by bit against the members still alive. The limit is 5 times the
    * largest reading.
    */
  val memberReadingLimit: Long = 320L

  /** The library of the knowledge the file at the path holds as the one field
    * of its tuple: a knowledge file of one field, or a file whose field is the
    * choice of knowledge files it imports at its top, as the tests' and the
    * benchmarks' fixtures are. The file is read by projection off the tree
    * whose visible subtree is `visible` (`entryTerm`), its field taken
    * (`entryGroup`) and compiled (`compiled`), all under one compilation's
    * reading state from `KnowledgeReading.compilationState`; no text is written
    * and no path is resolved by the host. Throws as `entryTerm`, `entryGroup`
    * and `compiled` do.
    */
  def compiledAt(
      visible: java.nio.file.Path,
      file: java.nio.file.Path,
      backends: Vector[LibraryBackend]
  ): StandardLibrary =
    val (knowledge, afterEntry) = entryGroup(
      entryTerm(visible, file, KnowledgeReading.compilationState)
    )
    compiled(
      KnowledgeReading.term(knowledge, Set.empty),
      backends,
      afterEntry
    )._1

  /** The entry's term read after the projection to the visible subtree
    * (`projected`), within `entryReadingLimit`, its cost beside the
    * projection's.
    */
  private def termRead(
      visible: java.nio.file.Path,
      entry: Configured[NoFacts.type],
      state: ReadingState[NoFacts.type]
  ): EntryReading =
    val (afterProjection, projection) = projected(visible, state)
    val before = afterProjection.tables.complete.size
    val (term, after) =
      try
        KnowledgeReading.run(
          KnowledgeReading.tuplesTerm(Value.of(entry)),
          entryReadingLimit,
          afterProjection
        )
      catch
        case KnowledgeReadingError(reason) =>
          malformed(MalformedReason.KnowledgeUnread("the entry", reason))
    EntryReading(
      term,
      after,
      projection,
      ReadingCost(after.budget.spent, after.tables.complete.size - before)
    )

  /** The state after the projection of the root of the tree whose visible
    * subtree is `visible` to that subtree (`DirectoryTree.mixin` of the subtree
    * itself), and its cost. Every look-up of an entry under the subtree passes
    * through this projection, whose cost grows with the bytes of the subtree's
    * absolute path, the levels of which are keys the tree looks up byte by
    * byte, so a limit that counted it would hold under one checkout only. Read
    * first, under limits of its own proportional to the path
    * (`projectionBaseSteps`, `projectionBaseTables`), its tables are reused by
    * the reads after it, and the state's table limit is raised by the tables it
    * added, so that the limits count only what is spent after it; the
    * projection's cost is measured and reported beside the read's (steps and
    * tables), not hidden. A state that holds the projection already reads it
    * again in a few steps and no table.
    */
  private def projected(
      visible: java.nio.file.Path,
      state: ReadingState[NoFacts.type]
  ): (ReadingState[NoFacts.type], ReadingCost) =
    val bytes = visible.toAbsolutePath.normalize.toString
      .getBytes(java.nio.charset.StandardCharsets.UTF_8)
      .length
    val before = state.tables.complete.size
    val (_, after) =
      try
        KnowledgeReading.run(
          KnowledgeReading.headsTerm(
            Value.of(DirectoryTree.mixin[NoFacts.type](visible, visible))
          ),
          projectionBaseSteps + projectionStepsPerByte * bytes,
          state.copy(tableLimit =
            before + projectionBaseTables + projectionTablesPerByte * bytes
          )
        )
      catch
        case KnowledgeReadingError(reason) =>
          malformed(
            MalformedReason.KnowledgeUnread(
              s"the projection to the visible subtree $visible",
              reason
            )
          )
    val added = after.tables.complete.size - before
    (
      after.copy(tableLimit = state.tableLimit + added),
      ReadingCost(after.budget.spent, added)
    )

  /** The library of the knowledge, ONE term, the enabled modules combined by
    * `+`, so that Scala reads no list of them but one entry: a record of
    * partial functions of literals, such as the choice of the enabled knowledge
    * files, each a linked file of the sources, read key by key
    * (`knowledgeRead`), checked and indexed, with each backend's check of its
    * set. The knowledge is read whole, so a declaration knows no knowledge
    * file: a lemma is identified by its direction and its two sides and named
    * by its name alone, and a native has no label: a declaration no longer
    * knows its file, and a lemma's display name and a native's label carry no
    * file path. A declaration several parts of the knowledge write is one fact.
    * Throws `StandardLibraryMalformed` for any malformed declaration. Read
    * under the compilation's reading state, which it returns with the library.
    */
  def compiled(
      knowledge: Configured[NoFacts.type],
      backends: Vector[LibraryBackend],
      state: ReadingState[NoFacts.type]
  ): (StandardLibrary, ReadingState[NoFacts.type]) =
    val (read, afterKnowledge) = knowledgeRead(knowledge, state)
    val declarations = read.distinct
    val (_, lemmaFacts) = declarations.foldLeft(
      (
        Map.empty[
          (Configured[NoFacts.type], Configured[NoFacts.type]),
          LemmaIdentifier
        ],
        Vector.empty[(LemmaNamed, LemmaSides[NoFacts.type])]
      )
    ) {
      case ((known, gathered), Declaration.ReadLemma(name, left, right, _)) =>
        val key = (left, right)
        val identifier = known.getOrElse(key, LemmaIdentifier(known.size))
        (
          known.updated(key, identifier),
          gathered :+ ((
            LemmaNamed(identifier, name),
            LemmaSides(identifier, left, right)
          ))
        )
      case (state, _) => state
    }
    val lemmaSides = lemmaFacts.map(_._2)
    val natives = declarations.collect {
      case Declaration.NativeBinding(instruction, native) =>
        BackendNative(instruction, native)
    }
    val properties = propertyFacts(declarations, lemmaSides)
    val distinctProperties = properties.distinct
    val specializations = distinctProperties.collect {
      case CombinatorProperty(
            criterion,
            Property.NativeSpecialization(representation)
          ) =>
        BackendSpecialization(
          representation,
          distinctProperties.collect {
            case CombinatorProperty(`criterion`, family: Property.DataFamily) =>
              family
          }
        )
    }
    backends.foreach(_.checked(natives, specializations))
    val index = StandardLibraryIndex[NoFacts.type](
      NoFacts,
      lemmaFacts.map(_._1).distinct,
      lemmaSides.distinct,
      natives
        .map(native => NativeBound(native.instruction, native.native))
        .distinct,
      properties.distinct
    )
    (StandardLibrary(index, lemmaProofs(declarations)), afterKnowledge)

  /** The declarations of a knowledge term, read whole: the members of each of
    * its slots (`KnowledgeFileReading.declarations`), which for a choice of
    * knowledge files gives the union of their declarations (by (8), the choice
    * of the files read as one mixin is the choice of their readings), in the
    * order the heads are enumerated; none for top, the knowledge of no file
    * (`noKnowledge`). A declaration knows no knowledge file. Throws
    * `StandardLibraryMalformed` with `KnowledgeUnread` for a term that does not
    * read, and with `DeclaredTwice` for a name two different lemmas declare.
    */
  private[standardlibrary] def knowledgeRead(
      knowledge: Configured[NoFacts.type],
      state: ReadingState[NoFacts.type]
  ): (Vector[Declaration], ReadingState[NoFacts.type]) =
    val (declarations, after) =
      read(KnowledgeFileReading.declarations(knowledge), state)
    declarations
      .collect { case lemma: Declaration.ReadLemma => lemma }
      .distinct
      .groupBy(_.name)
      .collect { case (name, found) if found.size > 1 => name }
      .toVector
      .sorted
      .headOption
      .foreach(name => malformed(MalformedReason.DeclaredTwice(name)))
    (declarations, after)

  /** The declarations of one slot of a knowledge term (`knowledgeSlots`), as
    * `knowledgeRead` reads them, the other slots not read.
    */
  private[standardlibrary] def slotRead(
      knowledge: Configured[NoFacts.type],
      slot: KnowledgeSlot,
      state: ReadingState[NoFacts.type]
  ): (Vector[Declaration], ReadingState[NoFacts.type]) =
    read(KnowledgeFileReading.slotDeclarations(knowledge, slot), state)

  private def read(
      reading: gezi.knowledgereading.Reading[NoFacts.type, Vector[Declaration]],
      state: ReadingState[NoFacts.type]
  ): (Vector[Declaration], ReadingState[NoFacts.type]) =
    try KnowledgeReading.run(reading, knowledgeReadingLimit, state)
    catch
      case KnowledgeReadingError(reason) =>
        malformed(MalformedReason.KnowledgeUnread("the knowledge", reason))

  /** The proof metadata of each lemma of the declarations, by its name. */
  private def lemmaProofs(
      declarations: Vector[Declaration]
  ): Map[String, LemmaProof] =
    declarations.collect { case Declaration.ReadLemma(name, _, _, proof) =>
      name -> proof
    }.toMap

  /** Whether two pure keys are one term: one object, since every term is
    * interned.
    */
  private def samePure(left: Pure, right: Pure): Boolean =
    Configured.same(
      Configured.fromPure(NoFacts)(left),
      Configured.fromPure(NoFacts)(right)
    )

  private def malformed(reason: MalformedReason): Nothing =
    throw StandardLibraryMalformed(reason)

  // ---- combinator properties ----

  /** The facts of the combinator properties of the knowledge, in the order of
    * its declarations: a `data_fields` with its constructor's position in its
    * criterion's `data_family`, and an `associative` checked against the
    * lemmas. A property stated again of one term, by another knowledge file or
    * of an α-equivalent file, is the same fact, held once by the index:
    * α-equivalent files are one term and share their bindings.
    */
  private def propertyFacts(
      declarations: Vector[Declaration],
      lemmaSides: Vector[LemmaSides[NoFacts.type]]
  ): Vector[CombinatorProperty] =
    val families = declarations.collect {
      case Declaration.PropertyBinding(
            criterion,
            Property.DataFamily(_, constructors)
          ) =>
        (criterion, constructors)
    }
    val facts = declarations.collect {
      case Declaration.PropertyBinding(instruction, property) =>
        CombinatorProperty(instruction, property)
      case Declaration.FieldsBinding(criterion, constructor, fields) =>
        val position = families
          .filter((family, _) => samePure(family, criterion))
          .distinct match
          case Vector((_, constructors))
              if constructors.count(samePure(_, constructor)) == 1 =>
            constructors.indexWhere(samePure(_, constructor))
          case _ =>
            malformed(
              MalformedReason.CombinatorPropertyMalformed(
                "data_fields",
                s"data_fields($constructor, $fields)",
                PropertyProblem.NoConstructor
              )
            )
        CombinatorProperty(criterion, Property.DataFields(position, fields))
    }
    facts.foreach(fact => justified(slotOf(fact.property), fact, lemmaSides))
    facts

  /** The slot a property is declared in. */
  private def slotOf(property: Property): String = property match
    case Property.Associative             => "associative"
    case Property.Noinline                => "noinline"
    case Property.NameMarker              => "name_marker"
    case Property.ClosureMarker           => "closure_marker"
    case Property.TagOrigin               => "tag_origin"
    case Property.TagNext                 => "tag_next"
    case Property.FirstOrderConstructor   => "first_order_constructor"
    case Property.NativeSpecialization(_) => "native_specialization"
    case Property.TypedBranch             => "typed_branch"
    case Property.Repeller                => "repeller"
    case Property.DataFamily(_, _)        => "data_family"
    case Property.DataFields(_, _)        => "data_fields"
    case Property.JvmType(_)              => "jvm_type"

  /** Checks that a lemma of the knowledge files has the two sides, in either
    * order, the vocabulary gives for the property of the term.
    */
  private def justified(
      slot: String,
      fact: CombinatorProperty,
      lemmaSides: Vector[LemmaSides[NoFacts.type]]
  ): Unit =
    CombinatorPropertyVocabulary.justification(fact.property) match
      case Justification.Lemma(left, right) =>
        def side(term: Configured[NoFacts.type]): Configured[NoFacts.type] =
          CombinatorPropertyVocabulary.side(
            term,
            Configured.fromPure(NoFacts)(fact.instruction)
          )
        val (leftSide, rightSide) = (side(left), side(right))
        if !lemmaSides.exists(sides =>
            (Configured.same(sides.left, leftSide) && Configured
              .same(sides.right, rightSide)) ||
              (Configured.same(sides.left, rightSide) && Configured
                .same(sides.right, leftSide))
          )
        then
          malformed(
            MalformedReason.CombinatorPropertyMalformed(
              slot,
              fact.toString,
              PropertyProblem.NoJustifyingLemma
            )
          )
      case Justification.Matching | Justification.FrontEnd |
          Justification.Backend =>
        ()
