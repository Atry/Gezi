package gezi.strategies

import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.OccurrenceMarkers
import gezi.frontend.Occurrences
import gezi.frontend.TermOf
import gezi.ir.NoFacts
import gezi.knowledgereading.KnowledgeReading
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.Value

/** The helpers the strategies' tests share (`tests/saturation_runs.pl` and the
  * helpers of the Prolog tests): libraries compiled from the standard library,
  * programs written in the HOAS put through the front end with the occurrence
  * tagging, and the readings of the ordering modules' fold states.
  */
object StrategyTesting:

  /** A HOAS term of the tests: its constants are closed terms under no facts,
    * the library's terms read by projection.
    */
  type ProgramTerm = TermOf[Configured[NoFacts.type]]

  /** The library of the knowledge file at the path relative to Gezi's root,
    * extension included, the one field of its tuple, with no backend's checks
    * (`LibraryFiles.compiled`).
    */
  def compiled(file: String): StandardLibrary =
    LibraryFiles.compiled(file, Vector.empty)

  // TODO: compiledWith and programNames stood here. Their purpose: a library compiled with the library files of
  // directories declared, and the map from the names of its library files to their instructions. They named library terms
  // by LibraryFiles.programNames, LibraryFiles.compiledDeclaring and LibraryFiles.directoryFiles, a table of library
  // files deleted when the library became files reached by paths, with no replacement: a
  // program holds the library terms it needs as closed instructions (`Term.Closed`) read off a fixture file by
  // projection (`StandardLibrary.entryMembers`). The deleted code:
  // git show 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/StrategyTesting.scala.

  /** The closed program through the front end, its occurrences tagged when the
    * library declares the occurrence roles, defunctionalized and interned
    * (`program_instruction/2`). The program names nothing: the library terms it
    * holds are closed instructions (`Term.Closed`).
    */
  def programInput(
      library: StandardLibrary,
      program: ProgramTerm
  ): Configured[NoFacts.type] =
    programInputIn[NoFacts.type](library, program)(using NoFacts)

  /** `programInput` in the configuration in scope: the program's constants are
    * terms of that configuration, and the library's occurrence markers, pure
    * keys, enter it by `Configured.fromPure`.
    */
  def programInputIn[C <: NativeSpecializer & Singleton](
      library: StandardLibrary,
      program: TermOf[Configured[C]]
  )(using C): Configured[C] =
    val term = program.deBruijnTerm(Map.empty)
    val tagged = occurrenceMarkers(library) match
      case None          => term
      case Some(markers) => Occurrences.tagged(term, markers)
    Defunctionalization.thunkInstruction[C](tagged)

  /** The de Bruijn term of the closed program, its occurrences tagged when the
    * library declares the occurrence roles (`program_term/2`).
    */
  def taggedTerm(
      library: StandardLibrary,
      program: ProgramTerm
  ): DeBruijnTermOf[Configured[NoFacts.type]] =
    val term = program.deBruijnTerm(Map.empty)
    occurrenceMarkers(library) match
      case None          => term
      case Some(markers) => Occurrences.tagged(term, markers)(using NoFacts)

  /** The fixture entry of the tests' round of the key under Gezi's directory,
    * one file a round: its member of the key is the round's knowledge, the
    * choice of the knowledge files it imports, a term of the entry and not
    * assembled by the host from paths. An entry's read evaluates all of its
    * top-level imports, so one file of every round's imports exceeded a read's
    * tables: MEASURED 2026-11-12, the seven imports of the five rounds took
    * 148,513 steps and 63,131 tables, above `ReadingState.defaultTableLimit`
    * (50,000), each member 500 to 700 tables after it.
    */
  def roundFile(key: String): String =
    s"tests/round_fixtures/$key.lambdalattice"

  /** The steps the round's member may take after the entry's term: MEASURED
    * 2026-11-12, 1,176 (occurrence_erasure) to 1,567
    * (prolog_backend_type_check) of the combined file's members.
    */
  private val roundMemberLimit: Long = 20000

  /** The knowledge term of the round of the key, read off `roundFile` by
    * projection, as a compilation reads its rounds' knowledge: the entry's term
    * under the compilation's state (`KnowledgeReading.compilationState`), whose
    * table limit covers a knowledge read's look-ups, then the member threaded
    * after it. MEASURED 2026-11-12, the entry's read of fixed_width_type_check,
    * whose three imports reach native_types, hindley_milner_unions and
    * fixed_width_unions, takes 51,709 tables, above a single read's 50,000; the
    * mechanism is the look-ups' bit-by-bit test of a key at each member (the
    * design's cost, as `KnowledgeReading.compilationTableLimit` says).
    */
  def round(key: String): Configured[NoFacts.type] =
    val root = LibraryFiles.buildRoot
    val StandardLibrary.EntryReading(entry, afterEntry, _, _) =
      StandardLibrary.entryTerm(
        root,
        root.resolve(roundFile(key)),
        KnowledgeReading.compilationState
      )
    KnowledgeReading
      .run(
        KnowledgeReading.memberTerm(Value.of(entry)(using NoFacts)),
        roundMemberLimit,
        afterEntry
      )(using NoFacts)
      ._1

  /** The occurrence markers the library declares, checked against its erasure
    * lemmas (`StandardLibraryIndex.occurrenceMarkers`); nothing when it
    * declares none.
    */
  def occurrenceMarkers(library: StandardLibrary): Option[OccurrenceMarkers] =
    library.index.occurrenceMarkers

  // TODO: namedInput stood here. Its purpose: a HOAS program through the front end without the tagging, its
  // library names resolved (`named_instruction/2`). It named library terms by Term.define and
  // LibraryFiles.programNames, a free variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
  // Its replacement reads the library terms it needs
  // as members of a fixture file under tests/ by projection and composes them with the HOAS case of a closed
  // instruction. The deleted code:
  // git show 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/StrategyTesting.scala.

  /** The value of the fold state of the whole term at the module
    * (`module_value/3`).
    */
  def moduleValue(
      module: NormalityModule[NoFacts.type],
      reading: TermReading[NoFacts.type],
      term: OrderTerm[NoFacts.type]
  ): OrderValue =
    module.value(module.folded(term, reading))

  /** The rank of the fold state of the whole term at the module (`term_ranks/3`
    * at one module).
    */
  def moduleRank(
      module: NormalityModule[NoFacts.type],
      reading: TermReading[NoFacts.type],
      term: OrderTerm[NoFacts.type]
  ): OrderValue =
    module.rank(module.folded(term, reading))

  /** The fold state of the term computed one layer at a time, each child a leaf
    * of its own state (`term_folded/3`).
    */
  def termFolded(
      module: NormalityModule[NoFacts.type],
      reading: TermReading[NoFacts.type],
      term: OrderTerm[NoFacts.type]
  ): FoldState =
    def folded(child: OrderTerm[NoFacts.type]): OrderTerm[NoFacts.type] =
      OrderTerm.Folded[NoFacts.type](
        termFolded(module, reading, child),
        TermReading.identityContract(child)
      )
    val layer = term match
      case OrderTerm.Apply(function, argument) =>
        OrderTerm.Apply(folded(function), folded(argument))
      case OrderTerm.Parallel(left, right, range) =>
        OrderTerm.Parallel(folded(left), folded(right), range)
      case OrderTerm.Choice(members) => OrderTerm.Choice(members.map(folded))
      case OrderTerm.Thunk(code, holes, fillings) =>
        OrderTerm.Thunk(code, holes, fillings.map(folded))
      case leaf => leaf
    module.folded(layer, reading)

  /** The value of the fold state computed one layer at a time
    * (`term_folded_values/3` at one module).
    */
  def foldedValue(
      module: NormalityModule[NoFacts.type],
      reading: TermReading[NoFacts.type],
      term: OrderTerm[NoFacts.type]
  ): OrderValue =
    module.value(termFolded(module, reading, term))

  /** The rank of the fold state computed one layer at a time
    * (`term_folded_ranks/3` at one module).
    */
  def foldedRank(
      module: NormalityModule[NoFacts.type],
      reading: TermReading[NoFacts.type],
      term: OrderTerm[NoFacts.type]
  ): OrderValue =
    module.rank(termFolded(module, reading, term))
