package com.yang_bo.gezi.orientation

import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.Pattern

/** A usable orientation of an enabled lemma: its matched side is found in the
  * graph and its added side is built and united with it.
  *
  * @param index
  *   its number in the set, the order in which its seeds are tried
  * @param arity
  *   the number of the lemma's metavariables, numbered from 0
  * @param functions
  *   the function metavariables, ascending: those an eta-shaped lambda of
  *   either side mentions, and those at the head of an application's spine on
  *   the matched side; an application an added side builds with one of them at
  *   the head of its spine is read by the β rule
  * @param essential
  *   the metavariables the added side mentions outside `shared`, ascending
  * @param shared
  *   the largest compound subterms of the added side that are subpatterns of
  *   the matched side as well, in the order an instance key lists them
  */
final case class Orientation[C <: NativeSpecializer & Singleton](
    index: Int,
    lemma: LemmaIdentifier,
    direction: Direction,
    arity: Int,
    matched: Pattern[C],
    added: Pattern[C],
    functions: Vector[Int],
    essential: Vector[Int],
    shared: Vector[Pattern[C]]
)
