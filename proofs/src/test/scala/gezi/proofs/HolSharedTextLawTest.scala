package gezi.proofs

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** Law: the shared text of a HOL term (`HolTermText.sharedText`) expands to
  * its text (`HolTermText.text`), and writes each subterm object once. The
  * terms are generated as graphs: leaves, then applications of nodes made
  * before, so that a node is shared by the applications that use it more
  * than once. Its purpose is to catch a shared text that drops, repeats or
  * misnumbers a node, which would make the judge's manifest
  * (`ArticleManifest`, its field `encoded`) stand for another term.
  */
class HolSharedTextLawTest extends GeneratedProperties:

  private val termType: HolTypeTerm = HolTypeTerm(Vector("LambdaJit", "term"), Vector.empty)

  private val leaves: Gen[HolTerm] =
    for
      name <- Gen.elementUnsafe(List("a", "b", "c"))
      constant <- Gen.boolean
    yield if constant then HolTerm.Constant(Vector("LambdaJit", name), termType) else HolTerm.Variable(Vector(name), termType)

  /** A graph of terms: each node a leaf or an application of two nodes made
    * before it; the term is the last node.
    */
  private val graphs: Gen[HolTerm] =
    for
      initial <- leaves.list(Range.linear(1, 3))
      steps <- Gen.int(Range.linear(0, 12))
      choices <- Gen.int(Range.linear(0, 1000)).list(Range.singleton(steps * 2))
    yield
      val nodes = choices.grouped(2).foldLeft(initial.toVector) { (made, pair) =>
        val (function, argument) = pair match
          case List(first, second) => (first, second)
          case other               => throw IllegalStateException(s"a step takes two choices, not $other")
        made :+ HolTerm.Application(made(function % made.size), made(argument % made.size))
      }
      nodes.lastOption.getOrElse(throw IllegalStateException("a graph has a node"))

  /** The text the numbered nodes of a shared text stand for. */
  private def expanded(shared: String): String =
    val nodes = shared.stripPrefix("shared(").stripSuffix(")").split(";", -1).toVector
    val reference = "#([0-9]+)".r
    val texts = nodes.foldLeft(Vector.empty[String])((written, node) =>
      written :+ reference.replaceAllIn(node, found => scala.util.matching.Regex.quoteReplacement(written(found.group(1).toInt)))
    )
    texts.lastOption.getOrElse(throw IllegalStateException("a shared text has a node"))

  /** The subterm objects of the term, each once. */
  private def objects(term: HolTerm): Int =
    @scala.annotation.tailrec
    def counted(pending: List[HolTerm], seen: List[HolTerm]): Int = pending match
      case Nil => seen.size
      case current :: rest if seen.exists(_ eq current) => counted(rest, seen)
      case (application: HolTerm.Application) :: rest => counted(application.function :: application.argument :: rest, application :: seen)
      case leaf :: rest => counted(rest, leaf :: seen)
    counted(List(term), Nil)

  property("the shared text expands to the text, and writes each subterm object once") {
    for term <- graphs.forAll
    yield
      val shared = HolTermText.sharedText(term)
      Result.all(
        List(
          Result.diff(expanded(shared), HolTermText.text(term))(_ == _),
          Result.diff(shared.stripPrefix("shared(").stripSuffix(")").split(";", -1).length, objects(term))(_ == _)
        )
      )
  }
