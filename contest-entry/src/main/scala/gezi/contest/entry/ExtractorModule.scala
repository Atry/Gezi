package gezi.contest.entry

import java.nio.file.Path
import gezi.jit.NativeBackend
import gezi.narrowblocks.NarrowBlockRoute
import gezi.strategies.Extractor
import gezi.ir.{Configured, NativeSpecializer, NoFacts}
import gezi.weakhead.ReadingConfiguration

/** A round's extraction outside the framework, with the narrow blocks' route it
  * pairs with, that an entry's data chooses by the constructor `module` of the
  * extractors' list (`ExtractorImplementation.Module`): what a module registers
  * with `java.util.ServiceLoader`, in
  * `META-INF/services/gezi.contest.entry.ExtractorModule` of its project, a
  * class with a public constructor of no parameter, as an executor module
  * registers itself (`ExecutorModule`).
  *
  * A module's identity is a term, its selector: the one field of the tuple its
  * selector file returns, a closed term told apart from every other module's by
  * a synthetic label, `(λ"$name". M) "$name"`, which the host never reads. An
  * entry imports the same file and writes the term it gives as the selector, so
  * that the entry's selector and the module's are one interned term; the
  * framework finds the module by that identity alone (`ExtractorModules`),
  * never by a name or a string of the entry's data.
  */
trait ExtractorModule:

  /** The path of the module's selector file, relative to the root of the tree
    * the entry's data is read from, Gezi's directory for an in-tree entry
    * (`EntryData.read`), conventionally `corpora/modules/<name>.lambdalattice`.
    * The file is read through the same front end and directory tree as the
    * entry's data (`StandardLibrary.entryMember`): the path loads a file and
    * decides nothing.
    */
  def selectorFile: Path

  /** The module's extraction of a round, built from the parameters the entry
    * wrote, a closed term the module reads by structure itself
    * (`KnowledgeReading`; a term the module cannot read throws
    * `EntryDataError`), and from the framework's inputs
    * (`ExtractorModuleInputs`).
    */
  def extractor[C <: NativeSpecializer & Singleton](
      parameters: Configured[NoFacts.type],
      inputs: ExtractorModuleInputs[C]
  ): Extractor[C]

  /** The narrow blocks' route the module's extraction pairs with
    * (`Defaults.route`): the modules that spell the round's write-backs, and
    * the route of the lemma rounds, whose last round's extraction has its
    * blocks compiled and run. A module that changes only the extraction returns
    * the framework's, `gezi.narrowblocks.LemmaRoute`.
    */
  def route(parameters: Configured[NoFacts.type]): NarrowBlockRoute

/** What the framework hands an extractor module beside the parameters the entry
  * wrote (`ExtractorModule.extractor`, `ExtractorModule.route`): what the
  * framework's own extraction and route are built from, the entry's natives and
  * the configuration its readings run under (`Defaults.extractor`). One value,
  * so that an input is added as a field without changing the factories'
  * signatures.
  *
  * @param natives
  *   the entry's natives, which the framework's narrow blocks read first
  * @param configuration
  *   the configuration of the entry's readings, whose native specializer builds
  *   the terms the extraction spells
  */
final case class ExtractorModuleInputs[C <: NativeSpecializer & Singleton](
    natives: NativeBackend,
    configuration: ReadingConfiguration[C]
)

/** The extractor modules registered, by the interned term of each one's
  * selector. The host compares a selector by identity only: two modules whose
  * selector files give one term are refused when the table is made, and a
  * selector no module gives is refused when it is looked up.
  */
final case class ExtractorModules(
    bySelector: Map[Configured[NoFacts.type], ExtractorModule]
):

  /** The module whose selector is the term given. Throws `EntryDataError` for a
    * term no registered module gives as its selector.
    */
  def chosen(selector: Configured[NoFacts.type]): ExtractorModule =
    ModuleSelectors.chosen("extractor", bySelector, selector)

object ExtractorModules:

  /** The modules registered with `java.util.ServiceLoader` on the class path of
    * this class's loader, in the order the loader finds them.
    */
  def loaded: Vector[ExtractorModule] =
    ModuleSelectors.loaded(classOf[ExtractorModule])

  /** The table of the modules registered with `java.util.ServiceLoader`
    * (`loaded`), their selector files read off the tree whose visible subtree
    * is `visible`. Throws as the other `registered` does.
    */
  def registered(visible: Path): ExtractorModules = registered(visible, loaded)

  /** The table of the modules registered with `java.util.ServiceLoader`, read
    * off the tree `EntryData.read` reads the entry of the directory off, whose
    * visible subtree is the directory's parent. Throws as `registered` does.
    */
  def registeredFor(entryDirectory: Path): ExtractorModules =
    registered(entryDirectory.toAbsolutePath.normalize.getParent)

  /** The table of the modules given, each one's selector the one member of its
    * selector file (`ExtractorModule.selectorFile`) under `visible`, read as
    * the entry's data reads an imported file's member
    * (`StandardLibrary.entryMember`), one URI expansion of the tree shared by
    * the files. Throws `EntryDataError` for two modules whose selectors are one
    * term, and as `StandardLibrary.entryMember` does for a selector file that
    * does not read.
    */
  def registered(
      visible: Path,
      modules: Vector[ExtractorModule]
  ): ExtractorModules =
    ExtractorModules(
      ModuleSelectors.bySelector("extractor", visible, modules, _.selectorFile)
    )
