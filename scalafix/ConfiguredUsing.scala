// Step 2 of the migration of https://github.com/Atry/private-overlay/issues/2261 (section 9), its mechanical part: the
// environment of a reading, an e-graph or a compilation is the entry's native specializer `c: C` in scope (#2261,
// section 2), so a method with the configuration's type parameter `C` (what ConfiguredTypeParameters added) takes it
// as a context parameter, `(using C)`, through which the typed constructions (`Value.Apply(f, a)` and the others)
// find it. A syntactic rule, run from source as ConfiguredTypeParameters.scala is:
//
//   cs launch -M scalafix.cli.Cli ch.epfl.scala:scalafix-cli_2.13.18:0.14.9 -- \
//     --scala-version 3.10.0 --rules=file:scalafix/ConfiguredUsing.scala \
//     --config=scalafix/configured-type-parameters.conf <directories>
//
// It adds the clause after the method's last parameter clause, to a method whose own type parameters declare `C`
// bounded by `NativeSpecializer & Singleton` and whose clauses take no `C` yet. A caller with no `C` in scope, the
// compiler reports at step 3, where the given is supplied from the reading's state or the entry.

import scalafix.v1._
import scala.meta._

class ConfiguredUsing extends SyntacticRule("ConfiguredUsing") {

  private def declaresConfiguration(parameters: List[Type.Param]): Boolean =
    parameters.exists(parameter =>
      parameter.name.value == "C" && parameter.tbounds.hi.exists(
        _.syntax.contains("NativeSpecializer")
      )
    )

  private def takesConfiguration(
      parameterLists: List[List[Term.Param]]
  ): Boolean =
    parameterLists.flatten.exists(_.decltpe.exists(_.syntax == "C"))

  override def fix(implicit document: SyntacticDocument): Patch =
    document.tree.collect {
      case definition: Defn.Def
          if declaresConfiguration(definition.tparams) && !takesConfiguration(
            definition.paramss
          ) =>
        clauseAdded(definition.name, definition.tparams, definition.paramss)
      case declaration: Decl.Def
          if declaresConfiguration(declaration.tparams) && !takesConfiguration(
            declaration.paramss
          ) =>
        clauseAdded(declaration.name, declaration.tparams, declaration.paramss)
    }.asPatch

  // After the closing parenthesis of the last parameter clause, or after the type parameters of a method with none.
  private def clauseAdded(
      name: Tree,
      typeParameters: List[Type.Param],
      parameterLists: List[List[Term.Param]]
  )(implicit
      document: SyntacticDocument
  ): Patch = {
    val tokens = document.tree.tokens
    parameterLists.lastOption.flatMap(_.lastOption) match {
      case Some(parameter) =>
        val closing = tokens.find(token =>
          token.start >= parameter.pos.end && token.is[Token.RightParen]
        )
        closing.fold(Patch.empty)(token => Patch.addRight(token, "(using C)"))
      case None =>
        val closing = typeParameters.lastOption.flatMap(last =>
          tokens.find(token =>
            token.start >= last.pos.end && token.is[Token.RightBracket]
          )
        )
        closing.fold(Patch.empty)(token => Patch.addRight(token, "(using C)"))
    }
  }
}
