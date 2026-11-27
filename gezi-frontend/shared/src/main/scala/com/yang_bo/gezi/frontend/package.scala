package com.yang_bo.gezi

/** The front end: the object language as written, to the defunctionalized IR of
  * the module `ir`. The written forms are the Scala higher-order abstract
  * syntax [[Term]] and lambdalattice text ([[Lambdalattice]]); each is
  * translated to a [[DeBruijnTerm]], which [[Defunctionalization]] translates
  * to the thunk IR, canonical instructions and codes (`com.yang_bo.gezi.ir.Configured`, the
  * terms of one configuration) built as it converts. Nothing after the front
  * end sees a de Bruijn term. [[ExchangeText]] writes a closed instruction as
  * one line of lambda-lattice text at the size of its graph and reads it back:
  * the form of the problem corpora's references and of the judge's points file
  * and pipe.
  *
  * The module depends on `ir` and `locations`; every module of this build
  * outside the framework but `locations`, `warts` and `conventions` depends on
  * it, directly or through `standardlibrary` (`provenance` in its tests only).
  */
package object frontend
