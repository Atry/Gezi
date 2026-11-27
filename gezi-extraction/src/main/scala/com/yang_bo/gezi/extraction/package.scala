package com.yang_bo.gezi

/** The greedy extraction of a graph's best entries by a [[CostModel]], and
  * their spellings. [[Extraction]] reads the graph's productions, a live node's
  * layer or a name, and computes each class's [[ClassEntries]] to a greedy
  * fixed point; [[PairingHeap]] is the persistent heap it reads its pending
  * productions off, in the order of SWI-Prolog's `library(heaps)`.
  *
  * The module depends on `egraph`; `strategies` depends on it.
  */
package object extraction
