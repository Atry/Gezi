package gezi

/** The compile-time boundary of the specialized spelling, checked from outside the package `gezi.ir`:
  * [[irboundary.ConfigurationBoundaryTest]] records, as a snapshot of compile errors, that code outside `gezi.ir`
  * cannot hand one configuration's term to another's native specializer, put a storage into the pool except through a
  * native specializer, read a storage's view without the capability, build a parallel of terms except through a
  * native specializer, or use a storage's view as a node. The package is not `gezi.ir`, so that its snippets see only what
  * every other module sees.
  */
package object irboundary
