package gezi.proofs

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** Law: the shared text of a HOL term (`HolTermText.sharedText`) expands to
  * its text (`HolTermText.text`), and writes each subterm object once and
  * each type once. The
  * terms are generated as graphs: leaves, then applications of nodes made
  * before, so that a node is shared by the applications that use it more
  * than once. Its purpose is to catch a shared text that drops, repeats or
  * misnumbers a node, which would make the judge's manifest
  * (`ArticleManifest`, its fields `encoded` and `definition`) stand for
  * another term. The leaves' types are drawn from a pool of nested function
  * types, so that a type node, its `#a` references and a type shared between
  * leaves are checked too.
  */
class HolSharedTextLawTest extends GeneratedProperties:

  /** A small pool of types: base types, then function types of types made
    * before, so that types nest and leaves drawn from the pool share types
    * and parts of types.
    */
  private val typePools: Gen[Vector[HolTypeTerm]] =
    for
      bases <- Gen.elementUnsafe(List("term", "code", "holes")).list(Range.linear(1, 2))
      steps <- Gen.int(Range.linear(0, 4))
      choices <- Gen.int(Range.linear(0, 1000)).list(Range.singleton(steps * 2))
    yield choices.grouped(2).foldLeft(bases.toVector.map(base => HolTypeTerm(Vector("LambdaJit", base), Vector.empty))) { (made, pair) =>
      val (domain, codomain) = pair match
        case List(first, second) => (first, second)
        case other               => throw IllegalStateException(s"a step takes two choices, not $other")
      made :+ HolTypeTerm(Vector("->"), Vector(made(domain % made.size), made(codomain % made.size)))
    }

  private def leaves(types: Vector[HolTypeTerm]): Gen[HolTerm] =
    for
      name <- Gen.elementUnsafe(List("a", "b", "c"))
      constant <- Gen.boolean
      typeTerm <- Gen.elementUnsafe(types.toList)
    yield if constant then HolTerm.Constant(Vector("LambdaJit", name), typeTerm) else HolTerm.Variable(Vector(name), typeTerm)

  /** A graph of terms: each node a leaf or an application of two nodes made
    * before it; the term is the last node.
    */
  private val graphs: Gen[HolTerm] =
    for
      types <- typePools
      initial <- leaves(types).list(Range.linear(1, 3))
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

  /** The types of the term's leaves and their parts, each once by
    * structure.
    */
  private def types(term: HolTerm): Int =
    @scala.annotation.tailrec
    def leafTypes(pending: List[HolTerm], seen: List[HolTerm], found: List[HolTypeTerm]): List[HolTypeTerm] = pending match
      case Nil => found
      case current :: rest if seen.exists(_ eq current) => leafTypes(rest, seen, found)
      case (application: HolTerm.Application) :: rest =>
        leafTypes(application.function :: application.argument :: rest, application :: seen, found)
      case (leaf @ HolTerm.Constant(_, typeTerm)) :: rest => leafTypes(rest, leaf :: seen, typeTerm :: found)
      case (leaf @ HolTerm.Variable(_, typeTerm)) :: rest => leafTypes(rest, leaf :: seen, typeTerm :: found)
    @scala.annotation.tailrec
    def parts(pending: List[HolTypeTerm], found: Set[HolTypeTerm]): Set[HolTypeTerm] = pending match
      case Nil                                  => found
      case current :: rest if found(current)    => parts(rest, found)
      case current :: rest                      => parts(current.arguments.toList ::: rest, found + current)
    parts(leafTypes(List(term), Nil, Nil), Set.empty).size

  property("the shared text expands to the text, and writes each subterm object once and each type once") {
    for term <- graphs.forAll
    yield
      val shared = HolTermText.sharedText(term)
      Result.all(
        List(
          Result.diff(expanded(shared), HolTermText.text(term))(_ == _),
          Result.diff(shared.stripPrefix("shared(").stripSuffix(")").split(";", -1).length, objects(term) + types(term))(_ == _)
        )
      )
  }
