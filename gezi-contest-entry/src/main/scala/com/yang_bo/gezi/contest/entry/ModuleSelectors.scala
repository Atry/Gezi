package com.yang_bo.gezi.contest.entry

import java.nio.file.Path
import java.util.ServiceLoader
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import scala.jdk.CollectionConverters.*
import com.yang_bo.gezi.ir.{Configured, NoFacts}

/** How the tables of an interface's modules are made and looked up, the same
  * for every interface an entry's data opens to modules, the executors'
  * (`ExecutorModules`) and the extractors' (`ExtractorModules`): the modules
  * registered with `java.util.ServiceLoader`, keyed by the interned term of
  * each one's selector, the one member of its selector file, read under no
  * facts like every term of an entry's data. The `interface` given to each
  * function is the interface's name in an error's message, and decides nothing.
  */
private[entry] object ModuleSelectors:

  /** The modules of the interface registered with `java.util.ServiceLoader` on
    * the class path of the interface's loader, in the order the loader finds
    * them.
    */
  def loaded[Module](interface: Class[Module]): Vector[Module] =
    ServiceLoader.load(interface, interface.getClassLoader).asScala.toVector

  /** The modules given by their selectors, each one's selector the one member
    * of its selector file under `visible`, read as the entry's data reads an
    * imported file's member (`StandardLibrary.entryMember`), one URI expansion
    * of the tree shared by the files. Throws `EntryDataError` for two modules
    * whose selectors are one term, and as `StandardLibrary.entryMember` does
    * for a selector file that does not read.
    */
  def bySelector[Module](
      interface: String,
      visible: Path,
      modules: Vector[Module],
      selectorFile: Module => Path
  ): Map[Configured[NoFacts.type], Module] =
    val root = visible.toAbsolutePath.normalize
    val (selectors, _) =
      modules.foldLeft(
        (
          Vector.empty[(Configured[NoFacts.type], Module)],
          KnowledgeReading.startingState.expansions
        )
      ) { case ((found, expansions), module) =>
        val (selector, after) = StandardLibrary.entryMember(
          root,
          root.resolve(selectorFile(module)),
          expansions
        )
        (found :+ (selector -> module), after)
      }
    selectors
      .groupMap(_._1)(_._2)
      .collectFirst {
        case (selector, sharing) if sharing.size > 1 => (selector, sharing)
      }
      .foreach { (selector, sharing) =>
        throw EntryDataError(
          s"the $interface modules ${sharing.map(_.getClass.getName).mkString(", ")} give one selector, $selector: each module's selector file is to give a term of its own"
        )
      }
    selectors.toMap

  /** The module of the table whose selector is the term given. Throws
    * `EntryDataError` for a term no module of the table gives as its selector.
    */
  def chosen[Module](
      interface: String,
      bySelector: Map[Configured[NoFacts.type], Module],
      selector: Configured[NoFacts.type]
  ): Module =
    bySelector.getOrElse(
      selector,
      throw EntryDataError(
        s"entry.lambdalattice: the $interface's selector is the selector of no registered module (${bySelector.size} registered): $selector"
      )
    )
