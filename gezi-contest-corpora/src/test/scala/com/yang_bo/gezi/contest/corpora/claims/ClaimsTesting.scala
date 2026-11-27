package com.yang_bo.gezi.contest.corpora.claims

import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.frontend.Term
import java.nio.file.Path
import java.nio.file.Paths
import java.security.MessageDigest

/** The claims group, read from Gezi's directory once for the test JVM, and the
  * forms the tests write programs in.
  */
object ClaimsTesting:

  /** The root of Gezi's build, which the build passes to the forked test JVM.
    */
  val buildRoot: Path = Paths.get(
    sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalStateException(
        "the build passes gezi.buildRoot to the forked test JVM"
      )
    )
  )

  lazy val problems: ProblemFamilies = ProblemFamilies(
    buildRoot,
    Expansions.none,
    com.yang_bo.gezi.hotspot.baselines.BaselineCaches.provider()
  )

  val group: Claims = Claims(buildRoot, problems, Vector.empty)

  export group.{claims, attractors, contestAnswers}

  /** The form of the HOAS term, a closed term with no library name: the
    * lambdalattice text of its tree, as `MergeTesting.form` writes it.
    */
  def form(term: Term): String =
    Lambdalattice.textWithLiterals(term.deBruijnTerm(Map.empty), Map.empty)

  /** `sha256:<hex>:<length>` of the form. */
  def digest(form: String): String =
    val hash = MessageDigest
      .getInstance("SHA-256")
      .digest(form.getBytes("UTF-8"))
      .map(byte => f"${byte & 0xff}%02x")
      .mkString
    s"sha256:$hash:${form.length}"
