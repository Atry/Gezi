package gezi.ematching

/** The compiler of orientations and codes into a program: [[Indexing]] builds
  * the inverted index of seeds, filed by kind and key, and the buildings of the
  * added sides, the shared subterms and the code bodies. The seeds of one
  * orientation, one for every compound and lambda position of its matched side,
  * are written by the private object `Seeding`.
  *
  * The module depends on `ematching` and `orientation`; `backendcomparison`
  * depends on it.
  */
package object indexing
