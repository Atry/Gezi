package gezi

/** Migrations of lambdalattice texts, each checked by reading the text it
  * makes, on the source locations `gezi.locations` gives:
  *
  *   - `SpellingMigration` changes the text and keeps its term, on the spans
  *     the reader gives (`gezi.frontend.SyntaxSpans`);
  *   - `TermMigration` replaces the instances of a lemma's left side by its
  *     right side's, found by the e-graph's matching on the nodes the text
  *     locates (`gezi.provenance`), and checks the new text against the
  *     old one in the e-graph.
  *
  * Outside the framework; the source locations it reads are for the
  * migration only, and no choice of the framework reads one.
  */
package object migration
