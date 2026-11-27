package com.yang_bo.gezi

/** The orientations of lemmas and what is computed from them alone. An
  * [[Orientation]] is a usable direction of an enabled lemma: its matched side
  * is found in the graph and its added side is built and united with it.
  * [[OrientationCompilation]] compiles the [[LemmaSides]] of the enabled lemmas
  * into [[CompiledOrientations]]; [[Orientations]] computes what the baseline
  * computes when it files them, and [[StandardOrder]] writes a term out for the
  * standard order of terms the baseline sorted orientations by.
  *
  * The module depends on `ir`; `ematching-indexing` depends on it.
  */
package object orientation
