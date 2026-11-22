package gezi

/** The checks, read off the sources of every module of this build, tests
  * included: [[WartSuppressionTest]] that every WartRemover suppression
  * carries the user's words, [[PackageDocumentationTest]] that every package
  * has one documented package object, and [[EntrySourcesTest]] that no file
  * of a contest entry names the problem corpora or the judge.
  * [[ScalaSources]] finds the sources the first two scan.
  * [[MarkdownLinksTest]] checks that every relative link of Gezi's Markdown
  * files resolves inside Gezi ([[MarkdownLinks]]). The module has tests only, depends on no
  * other module and reads the other modules' sources as text.
  */
package object conventions
