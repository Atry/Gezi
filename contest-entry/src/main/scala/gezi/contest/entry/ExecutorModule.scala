package gezi.contest.entry

import java.nio.file.Path
import gezi.hotspot.Executor
import gezi.jit.Jit
import gezi.narrowblocks.ProgramCompilation
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** An executor outside the framework that an entry's data chooses by the
  * constructor `module` of the executors' list (`ExecutorOption.Module`):
  * what a module
  * registers with `java.util.ServiceLoader`, in
  * `META-INF/services/gezi.contest.entry.ExecutorModule` of its project, as
  * an entry registers its `EntryProvider`, a class with a public constructor
  * of no parameter.
  *
  * A module's identity is a term, its selector: the one field of the tuple
  * its selector file returns, a closed term told apart from every other
  * module's by a synthetic label, `(λ"$name". M) "$name"`, which the host
  * never reads. An entry imports the same file and writes the term it gives
  * as the selector, so that the entry's selector and the module's are one
  * interned term; the framework finds the module by that identity
  * alone (`ExecutorModules`), never by a name or a string of the entry's
  * data.
  */
trait ExecutorModule:

  /** The path of the module's selector file, relative to the root of the
    * tree the entry's data is read from, Gezi's directory for an in-tree
    * entry (`EntryData.read`), conventionally
    * `corpora/modules/<name>.lambdalattice`. The file is read through the
    * same front end and directory tree as the entry's data
    * (`StandardLibrary.entryMember`): the path loads a file and decides
    * nothing.
    */
  def selectorFile: Path

  /** The module's executor for the configuration `C` of the inputs' JIT, built from the parameters the entry
    * wrote, a closed term of the entry's data (read under no facts, like the rest of it) that the module reads by
    * structure itself (`KnowledgeReading`; a term the module cannot read throws `EntryDataError`), and from the
    * framework's inputs (`ExecutorModuleInputs`). The factory is polymorphic in `C`: a module is registered once
    * and serves every configuration. Its suspensions are the module's own type; the generic entry runs it as any
    * `Executor`, whatever that type.
    */
  def executor[C <: NativeSpecializer & Singleton](parameters: Configured[NoFacts.type], inputs: ExecutorModuleInputs[C]): Executor[C, ?]

/** What the framework hands an executor module beside the parameters the
  * entry wrote (`ExecutorModule.executor`): what the framework's own
  * executor is built from, the entry's JIT and its reading options
  * (`Defaults.executor`), and the entry's prepared compilation. One value,
  * so that an input is added as a field without changing the factory's
  * signature: the extension point for what a module may need later.
  *
  * @param jit
  *   the entry's JIT, built from its options over the backend facts
  *   (`Defaults.jit`)
  * @param reading
  *   the entry's reading options
  * @param compilation
  *   the entry's prepared compilation, its library's index, its lemma rounds
  *   prepared once at the entry's setup and its natives: the configuration
  *   of the program unit's compiler (`gezi.narrowblocks.ProgramCompiler`),
  *   the same value whatever the entry's data says of where its programs are
  *   compiled (`CompilationPlaceOption`). Under `ByExecutor` the programs the
  *   module reads are uncompiled, and the module may compile any of them by
  *   this configuration; under `Upfront` the
  *   rounds have already run on the programs it reads
  */
final case class ExecutorModuleInputs[C <: NativeSpecializer & Singleton](jit: Jit[C], reading: ReadingOptions, compilation: ProgramCompilation[C])

/** The executor modules registered, by the interned term of each
  * one's selector.
  * The host compares a selector by identity only: two modules whose
  * selector files give one term are refused when the table is made, and a
  * selector no module gives is refused when it is looked up.
  */
final case class ExecutorModules(bySelector: Map[Configured[NoFacts.type], ExecutorModule]):

  /** The module whose selector is the term given. Throws `EntryDataError`
    * for a term no registered module gives as its selector.
    */
  def chosen(selector: Configured[NoFacts.type]): ExecutorModule = ModuleSelectors.chosen("executor", bySelector, selector)

object ExecutorModules:

  /** The modules registered with `java.util.ServiceLoader` on the class
    * path of this class's loader, in the order the loader finds them.
    */
  def loaded: Vector[ExecutorModule] = ModuleSelectors.loaded(classOf[ExecutorModule])

  /** The table of the modules registered with `java.util.ServiceLoader`
    * (`loaded`), their selector files read off the tree whose visible
    * subtree is `visible`. Throws as the other `registered` does.
    */
  def registered(visible: Path): ExecutorModules = registered(visible, loaded)

  /** The table of the modules registered with `java.util.ServiceLoader`, read
    * off the tree `EntryData.read` reads the entry of the directory off,
    * whose visible subtree is the directory's parent. Throws as `registered`
    * does.
    */
  def registeredFor(entryDirectory: Path): ExecutorModules =
    registered(entryDirectory.toAbsolutePath.normalize.getParent)

  /** The table of the modules given, each one's selector the one member of
    * its selector file (`ExecutorModule.selectorFile`) under `visible`, read
    * as the entry's data reads an imported file's member
    * (`StandardLibrary.entryMember`), one URI expansion of the tree shared by
    * the files. Throws `EntryDataError` for two modules whose selectors are
    * one term, and as `StandardLibrary.entryMember` does for a selector file
    * that does not read.
    */
  def registered(visible: Path, modules: Vector[ExecutorModule]): ExecutorModules =
    ExecutorModules(ModuleSelectors.bySelector("executor", visible, modules, _.selectorFile))
