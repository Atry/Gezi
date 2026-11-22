// The migration of the weak-head evaluator's values to interned terms: an
// instruction is a value as it is (gezi.weakhead.Value is
// Interned[WeakHeadLayer], which the IR's layers are among), so the old
// wrapper `Value.Reference(instruction)` is the instruction. A syntactic rule
// for scalafix 0.14.9's Scala 2.13 runner, run from source:
//
//   cs launch -M scalafix.cli.Cli ch.epfl.scala:scalafix-cli_2.13.18:0.14.9 -- \
//     --scala-version 3.10.0 --rules=file:scalafix/InternedValues.scala \
//     --config=scalafix/interned-constructors.conf <directories>
//
// It rewrites a construction `Value.Reference(argument)` of one argument
// that is not a placeholder to `argument`, parenthesised when the argument
// is not a simple name or selection. A pattern `case Value.Reference(...)`,
// whose meaning changed (every value has a layer now), and a
// `Value.Reference(_)` or `Value.Reference` passed as a function are left for
// a hand edit, which the compiler points at.

import scalafix.v1._
import scala.meta._

class InternedValues extends SyntacticRule("InternedValues") {

  private def isReference(function: Term): Boolean = function match {
    case Term.Select(Term.Name("Value"), Term.Name("Reference")) => true
    case Term.Select(Term.Select(_, Term.Name("Value")), Term.Name("Reference")) => true
    case _ => false
  }

  private def simple(argument: Term): Boolean = argument match {
    case _: Term.Name | _: Term.Select | _: Term.Apply | _: Term.ApplyType => true
    case _                                                                 => false
  }

  override def fix(implicit document: SyntacticDocument): Patch =
    document.tree.collect {
      case application: Term.Apply
          if isReference(application.fun) && application.argClause.values.size == 1 &&
            !application.argClause.values.head.isInstanceOf[Term.Placeholder] =>
        val argument = application.argClause.values.head
        val text = if (simple(argument)) argument.syntax else s"(${argument.syntax})"
        Patch.replaceTree(application, text)
    }.asPatch
}
