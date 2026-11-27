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
    * once, and each type once: `shared(N0;N1;…;Nk)`, the nodes in post-order,
    * the last the term, each a type `type(Name,[#a,…])` of the type nodes
    * numbered a, …, a `constant(Name,#t)` or a `variable(Name,#t)` of the
    * type node numbered t, or `application(#i,#j)` of the nodes numbered i
    * and j, counted from 0. Replacing each `#i` by node i's own text,
    * recursively, and taking the last node gives `text(term)`. The text is as
    * large as the term as a graph of objects with its types as values: a
    * program's encoding (`OpentheoryArticle.termEncoded`) shares the encoding
    * of each key, and its tree, which `text` writes, can be exponentially
    * larger; and a thunk constant's type nests one function type per filling,
    * which a defining term (`OpentheoryArticle.definingTermEncoded`) writes at
    * every constant and variable of its code (measured 2026-11-22 on the
    * defining terms of one of the judge's points: up to 67,675,565
    * characters each with each type written in place, which ran the
    * manifests' JVM out of a 3 GB heap).
    * Terms are told apart by identity, never by structure, whose hash code
    * walks the tree; types by structure, their hash codes computed when they
    * are made (`HolTypeTerm`).
    */
  def sharedText(term: HolTerm): String =
    val nodes = sharedNodes(List(SharedStep.Visit(term)), Map.empty, Map.empty, Vector.empty)
    nodes.mkString("shared(", ";", ")")

  /** A subterm told apart by identity. */
  private final class Identified(val term: HolTerm):
    override def equals(other: Any): Boolean = other match
      case that: Identified => that.term eq term
      case _                => false
    override def hashCode: Int = System.identityHashCode(term)

  /** A step of `sharedText`'s post-order walk: a subterm to visit, a leaf or
    * an application whose parts were visited, to write, or the same of a
    * type.
    */
  private enum SharedStep:
    case Visit(term: HolTerm)
    case Written(term: HolTerm)
    case VisitType(typeTerm: HolTypeTerm)
    case WrittenType(typeTerm: HolTypeTerm)

  /** The nodes written so far, numbered by their position, each subterm
    * object once (`numbers`) and each type once (`typeNumbers`).
    */
  @scala.annotation.tailrec
  private def sharedNodes(
      steps: List[SharedStep],
      numbers: Map[Identified, Int],
      typeNumbers: Map[HolTypeTerm, Int],
      nodes: Vector[String]
  ): Vector[String] =
    def number(part: HolTerm): Int =
      numbers.getOrElse(Identified(part), throw IllegalStateException("a part of a term is written after it"))
    def typeNumber(part: HolTypeTerm): Int =
      typeNumbers.getOrElse(part, throw IllegalStateException("a part of a type is written after it"))
    steps match
      case Nil => nodes
      case SharedStep.Visit(term) :: rest if numbers.contains(Identified(term)) => sharedNodes(rest, numbers, typeNumbers, nodes)
      case SharedStep.Visit(application: HolTerm.Application) :: rest =>
        sharedNodes(
          SharedStep.Visit(application.function) :: SharedStep.Visit(application.argument) :: SharedStep.Written(application) :: rest,
          numbers,
          typeNumbers,
          nodes
        )
      case SharedStep.Visit(leaf @ HolTerm.Constant(_, typeTerm)) :: rest =>
        sharedNodes(SharedStep.VisitType(typeTerm) :: SharedStep.Written(leaf) :: rest, numbers, typeNumbers, nodes)
      case SharedStep.Visit(leaf @ HolTerm.Variable(_, typeTerm)) :: rest =>
        sharedNodes(SharedStep.VisitType(typeTerm) :: SharedStep.Written(leaf) :: rest, numbers, typeNumbers, nodes)
      case SharedStep.Written(term) :: rest if numbers.contains(Identified(term)) => sharedNodes(rest, numbers, typeNumbers, nodes)
      case SharedStep.Written(term) :: rest =>
        val node = term match
          case HolTerm.Constant(name, typeTerm)        => s"constant(${nameText(name)},#${typeNumber(typeTerm)})"
          case HolTerm.Variable(name, typeTerm)        => s"variable(${nameText(name)},#${typeNumber(typeTerm)})"
          case HolTerm.Application(function, argument) => s"application(#${number(function)},#${number(argument)})"
        sharedNodes(rest, numbers.updated(Identified(term), nodes.size), typeNumbers, nodes :+ node)
      case SharedStep.VisitType(typeTerm) :: rest if typeNumbers.contains(typeTerm) => sharedNodes(rest, numbers, typeNumbers, nodes)
      case SharedStep.VisitType(typeTerm) :: rest =>
        sharedNodes(
          typeTerm.arguments.toList.map(SharedStep.VisitType(_)) ::: SharedStep.WrittenType(typeTerm) :: rest,
          numbers,
          typeNumbers,
          nodes
        )
      case SharedStep.WrittenType(typeTerm) :: rest if typeNumbers.contains(typeTerm) => sharedNodes(rest, numbers, typeNumbers, nodes)
      case SharedStep.WrittenType(typeTerm) :: rest =>
        val node = s"type(${nameText(typeTerm.name)},[${typeTerm.arguments.map(argument => s"#${typeNumber(argument)}").mkString(",")}])"
        sharedNodes(rest, numbers, typeNumbers.updated(typeTerm, nodes.size), nodes :+ node)

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
