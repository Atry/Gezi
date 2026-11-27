package gezi.frontend

import gezi.locations.BinderOrigin
import gezi.locations.Location

/** The source map of a de Bruijn term, in the term's shape
  * (`Defunctionalization.locatedInstructionTerm`): each node's locations, and
  * an abstraction's binder origins; `Unknown` for a part no map locates. The
  * printer names each binder from it, and `Defunctionalization.relocatedMap`
  * reads it back onto another spelling of the term. A thunk's place locates the
  * first abstraction of its chain; the others have no locations of their own.
  */
enum TermMap:
  case Unknown
  case Abstraction(
      locations: Set[Location],
      origins: Set[BinderOrigin],
      body: TermMap
  )
  case Pair(locations: Set[Location], left: TermMap, right: TermMap)
  case Leaf(locations: Set[Location])

  /** The node's locations, none for `Unknown`. */
  def nodeLocations: Set[Location] = this match
    case Unknown                      => Set.empty
    case Abstraction(locations, _, _) => locations
    case Pair(locations, _, _)        => locations
    case Leaf(locations)              => locations

  /** The binder origins of the node when it is an abstraction, none for another
    * node.
    */
  def nodeOrigins: Set[BinderOrigin] = this match
    case Abstraction(_, origins, _) => origins
    case _                          => Set.empty

  /** The map of the node below this one at the step, a child position of
    * `DeBruijnTerm` (`Lambda` 0, the other nodes 0 and 1); `Unknown` where the
    * map does not reach it.
    */
  def below(step: Int): TermMap = (this, step) match
    case (Abstraction(_, _, body), 0) => body
    case (Pair(_, left, _), 0)        => left
    case (Pair(_, _, right), 1)       => right
    case _                            => Unknown
