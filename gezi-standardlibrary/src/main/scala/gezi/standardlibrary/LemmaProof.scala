package gezi.standardlibrary

/** Where a lemma's proof is, the fifth field of its tuple in a knowledge
  * file: the Scott tuple `λ_c. _c "kind" "content"` of two string literals,
  * the kind naming the format of the content, which is a citation in that
  * format's own syntax: for a property a test proves, a string a test
  * framework such as munit or JUnit runs; for a document, a Markdown or a
  * TeX citation. It is metadata: the index
  * does not hold it and the compiler does not read it; the Lean export
  * writes it into its docstrings (`LeanStatements`), a test replays the
  * lemmas whose suite it names (`StandardLibraryLemmasTest`), and
  * `ProofCitations.citationsChecked` checks its Markdown links.
  */
enum LemmaProof:

  /** Kind `munit`: the full name of a munit suite that checks the lemma,
    * which `sbt testOnly <suite>` runs.
    */
  case Munit(suite: String)

  /** Kind `md`: a Markdown link `[text](path)` or `[text](path#anchor)`,
    * the path relative to the repository's root, to the document that
    * proves the lemma, with the anchor of the heading of the proof's section
    * when the section is a heading.
    */
  case Markdown(link: String)

  /** Kind `tex`: a TeX citation, such as `\cite{key}`. */
  case Tex(citation: String)

  /** The kind, the first field of the constructor. */
  def kind: String = this match
    case Munit(_)    => "munit"
    case Markdown(_) => "md"
    case Tex(_)      => "tex"

  /** The content, the second field of the constructor. */
  def content: String = this match
    case Munit(suite)   => suite
    case Markdown(link) => link
    case Tex(citation)  => citation

object LemmaProof:

  /** The proof of the alternative of the published list
    * `corpora/compiler/backend_vocabulary/proof_kinds` (`munit`, `md`, `tex`,
    * in the order of the cases) with the content; none for a position beyond
    * the list.
    */
  def ofAlternative(position: Int, content: String): Option[LemmaProof] = position match
    case 0 => Some(Munit(content))
    case 1 => Some(Markdown(content))
    case 2 => Some(Tex(content))
    case _ => None
