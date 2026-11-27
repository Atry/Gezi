package gezi.contest.corpora.merges

import gezi.frontend.Term

/** The text the snapshots of this package record of a family's programs and
  * claims: one line per program, `key<TAB>form`, and one per claim fact, each
  * list ordered so that the snapshot is reproducible.
  */
object GeneratedProgramLines:

  /** The lines `key<TAB>form` of the programs, ordered by key, each form
    * `MergeTesting.form` of the program the generator builds. Throws when two
    * programs have one key.
    */
  def programs(programs: Vector[(String, () => Term)]): String =
    val keys = programs.map(_._1)
    if keys.distinct.length != keys.length then
      throw IllegalArgumentException(
        s"a key names two programs: ${keys.diff(keys.distinct).distinct}"
      )
    programs
      .sortBy(_._1)
      .map((key, program) => s"$key\t${MergeTesting.form(program())}")
      .mkString("", "\n", "\n")

  /** The lines of the claim facts, ordered as text. */
  def claims(claims: Vector[ClaimFact]): String =
    claims.map(_.line).sorted.mkString("", "\n", "\n")
