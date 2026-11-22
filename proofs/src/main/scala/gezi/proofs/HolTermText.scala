package gezi.proofs

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A HOL term of the writer as text, in the syntax of the Lean program's
  * `termText` (`OpentheoryArticleFixpointRunsTest`): `constant(Name,Type)`,
  * `variable(Name,Type)`, `application(Function,Argument)`, a type
  * `type(Name,[Type,...])`, a name the list of its components in double
  * quotes, a double quote or a backslash in a component escaped by a
  * backslash. The text is self-contained: it holds every name and type of
  * the term, with no dictionary. The judge writes a point's IR so into the
  * point's manifest, and the
  * fixpoint runs' test compares it with Lean's `Encoding.encode`.
  */
object HolTermText:

  /** The term's text, built as a trampoline: the judge writes the encoding
    * of a whole program, as deep as the program.
    */
  def text(term: HolTerm): String = termText(term).result

  /** The term's text with each subterm the term holds as one object written
    * once: `shared(N0;N1;…;Nk)`, the nodes in post-order, the last the
    * term, each a `constant(Name,Type)` or a `variable(Name,Type)` as `text`
    * writes them, or `application(#i,#j)` of the nodes numbered i and j,
    * counted from 0. Replacing each `#i` by node i's own text, recursively,
    * and taking the last node gives `text(term)`. The text is as large as
    * the term as a graph of objects: a program's encoding
    * (`OpentheoryArticle.termEncoded`) shares the encoding of each key, and
    * its tree, which `text` writes, can be exponentially larger. Objects are told
    * apart by identity, never by structure, whose hash code walks the tree.
    */
  def sharedText(term: HolTerm): String =
    val nodes = sharedNodes(List(SharedStep.Visit(term)), Map.empty, Vector.empty)
    nodes.mkString("shared(", ";", ")")

  /** A subterm told apart by identity. */
  private final class Identified(val term: HolTerm):
    override def equals(other: Any): Boolean = other match
      case that: Identified => that.term eq term
      case _                => false
    override def hashCode: Int = System.identityHashCode(term)

  /** A step of `sharedText`'s post-order walk: a subterm to visit, or an
    * application whose two parts were visited, to write.
    */
  private enum SharedStep:
    case Visit(term: HolTerm)
    case Written(application: HolTerm.Application)

  /** The nodes written so far, numbered by their position, each subterm
    * object once (`numbers`).
    */
  @scala.annotation.tailrec
  private def sharedNodes(steps: List[SharedStep], numbers: Map[Identified, Int], nodes: Vector[String]): Vector[String] =
    steps match
      case Nil => nodes
      case SharedStep.Visit(term) :: rest if numbers.contains(Identified(term)) => sharedNodes(rest, numbers, nodes)
      case SharedStep.Visit(application: HolTerm.Application) :: rest =>
        sharedNodes(
          SharedStep.Visit(application.function) :: SharedStep.Visit(application.argument) :: SharedStep.Written(application) :: rest,
          numbers,
          nodes
        )
      case SharedStep.Visit(leaf) :: rest =>
        sharedNodes(rest, numbers.updated(Identified(leaf), nodes.size), nodes :+ termText(leaf).result)
      case SharedStep.Written(application) :: rest if numbers.contains(Identified(application)) => sharedNodes(rest, numbers, nodes)
      case SharedStep.Written(application) :: rest =>
        def number(part: HolTerm): Int =
          numbers.getOrElse(Identified(part), throw IllegalStateException("a part of an application is written after it"))
        val node = s"application(#${number(application.function)},#${number(application.argument)})"
        sharedNodes(rest, numbers.updated(Identified(application), nodes.size), nodes :+ node)

  private def termText(term: HolTerm): TailRec[String] = term match
    case HolTerm.Constant(name, typeTerm) => done(s"constant(${nameText(name)},${typeText(typeTerm)})")
    case HolTerm.Variable(name, typeTerm) => done(s"variable(${nameText(name)},${typeText(typeTerm)})")
    case HolTerm.Application(function, argument) =>
      for
        functionText <- tailcall(termText(function))
        argumentText <- tailcall(termText(argument))
      yield s"application($functionText,$argumentText)"

  /** A type's text, built as a trampoline: a thunk constant's type nests
    * one function type per filling.
    */
  private def typeText(typeTerm: HolTypeTerm): String = typeTextBuilt(typeTerm).result

  private def typeTextBuilt(typeTerm: HolTypeTerm): TailRec[String] =
    ArticleStore
      .traversed(typeTerm.arguments)(argument => tailcall(typeTextBuilt(argument)))
      .map(arguments => s"type(${nameText(typeTerm.name)},[${arguments.mkString(",")}])")

  private def nameText(components: Vector[String]): String =
    components
      .map(component =>
        "\"" + component.flatMap(character =>
          if character == '"' || character == '\\' then s"\\$character" else character.toString
        ) + "\""
      )
      .mkString("[", ",", "]")
