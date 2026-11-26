package gezi.weakhead

import gezi.ir.Instruction

/** The expansion of each URI node readings have expanded
  * (`gezi.directorysugar.DirectoryTree.expansion`), keyed by the node,
  * which holds every input of the expansion: a memo of a pure function of
  * syntax (`CONTRIBUTING.md`, "Tables", its second kind), emptying it
  * changing no answer while no file changes. A reading holds it in its state
  * (`ReadingState.expansions`); between readings it is the only part of a
  * state that is carried, never the tables nor the store, which depend on
  * the reading's budgets: an owner that reads several times starts each
  * reading from its expansions and keeps the value the reading returns: it carries only the URI expansions, never tables or
  * store, since tables depend on budgets, and it is threaded from the
  * outermost owner down. It pins a `file:` URL's content for as long as the
  * value lives, by memoization.
  */
final case class Expansions(byNode: Map[Instruction, Instruction]):

  /** The expansion of the node, if one was made. */
  def get(node: Instruction): Option[Instruction] = byNode.get(node)

  /** These expansions and the node's. */
  def updated(node: Instruction, expansion: Instruction): Expansions = Expansions(byNode.updated(node, expansion))

  /** The URIs of the nodes expanded. */
  def uris: Set[java.net.URI] = byNode.keySet.flatMap(_.uri)

object Expansions:

  /** No expansion yet: what the outermost owner starts from. */
  val none: Expansions = Expansions(Map.empty)
