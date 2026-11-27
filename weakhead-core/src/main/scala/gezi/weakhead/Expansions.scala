package gezi.weakhead

import gezi.directorysugar.DirectoryTree
import gezi.directorysugar.DirectoryTree.ReadExpansion
import gezi.ir.{Configured, NativeSpecializer}

/** The expansion of each URI node readings have expanded
  * (`gezi.directorysugar.DirectoryTree.expansion`), keyed by the node, in two
  * parts. `byNode` holds the expansions read under the version of the contents
  * being read (`gezi.hotspot.ExpansionSource`): it pins a `file:` URL's content
  * for as long as the version lasts. `earlier` holds those read under older
  * versions, which answer nothing: a node read again under a new version reads
  * its content again, and only when that content is the one an earlier
  * expansion was made from is the expansion taken instead of being built again
  * (`DirectoryTree.expansionRead`). Both are memos of a pure function, of the
  * URI and the content (`CONTRIBUTING.md`, "Tables", its second kind): emptying
  * them changes no answer while no file changes.
  *
  * A reading holds them in its state (`ReadingState.expansions`); between
  * readings they are the only part of a state that is carried, never the tables
  * nor the store, which depend on the reading's budgets: an owner that reads
  * several times starts each reading from its expansions and keeps the value
  * the reading returns, threaded from the outermost owner down.
  * `ReadingExecutor` is such an owner.
  */
final case class Expansions[C <: NativeSpecializer & Singleton](
    byNode: Map[Configured[C], ReadExpansion[C]],
    earlier: Map[Configured[C], ReadExpansion[C]]
):

  /** The expansion of the URI node, and these expansions with it remembered:
    * the expansion of this version, or else read now by the front end under the
    * reading's native specializer, so that the expansions of two configurations
    * are never shared (a reading of one configuration holds a table of its own,
    * and the cache service keys them by the specializer,
    * `CompletedTableNamespace`).
    */
  def expanded(
      node: Configured[C],
      specializer: C
  ): (Configured[C], Expansions[C]) =
    val (read, pinned) = byNode.get(node) match
      case Some(found) => (found, this)
      case None        =>
        val found = DirectoryTree.expansionRead(node, earlier.get(node))(using
          specializer
        )
        (found, copy(byNode = byNode.updated(node, found)))
    (read.expansion, pinned)

  /** These expansions for a reading under another version of the contents: none
    * pinned, and all of them available to be reused where the content read then
    * is the same.
    */
  def underAnotherVersion: Expansions[C] =
    Expansions(Map.empty, earlier ++ byNode)

  /** These expansions and the others, the pins of one version. */
  def joined(others: Expansions[C]): Expansions[C] =
    Expansions(byNode ++ others.byNode, earlier ++ others.earlier)

  /** The URIs of the nodes expanded. */
  def uris: Set[java.net.URI] = byNode.keySet.flatMap(_.uri)

object Expansions:

  /** No expansion yet: what the outermost owner starts from. */
  def none[C <: NativeSpecializer & Singleton]: Expansions[C] =
    Expansions(Map.empty, Map.empty)
