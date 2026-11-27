// Step 2 of the migration of https://github.com/Atry/private-overlay/issues/2261 (section 9), its mechanical part: a
// type of section 4 written with no type argument, where the configuration's type parameter `C` is in scope, gets
// `[C]`. A syntactic rule, run from source as ConfiguredTypeParameters.scala is:
//
//   cs launch -M scalafix.cli.Cli ch.epfl.scala:scalafix-cli_2.13.18:0.14.9 -- \
//     --scala-version 3.10.0 --rules=file:scalafix/ConfiguredTypeArguments.scala \
//     --config=scalafix/configured-type-parameters.conf <directories>
//
// "In scope" is syntactic: an enclosing class, trait, enum, method or type alias declares a type parameter named `C`
// bounded by `NativeSpecializer & Singleton` (what ConfiguredTypeParameters added). It rewrites type positions only
// (a `Type.Name`), never a term (`ReadingState.fresh`), an import or a type already applied. A type it should not have
// applied (a name of another type, a type whose `C` is another), the compiler reports at step 3.

import scalafix.v1._
import scala.meta._

class ConfiguredTypeArguments extends SyntacticRule("ConfiguredTypeArguments") {

  private val applied: Set[String] = Set(
    "ReadingState",
    "ReadingConfiguration",
    "ParallelSet",
    "ParallelView",
    "Head",
    "ReadingExecutor",
    "ExecutorModule",
    "ExtractorModule",
    "Entry",
    "Interacted",
    "Interaction",
    "OutputDisplay",
    "GenericEntry",
    "JitConfiguration",
    "JitRunState",
    "EGraph",
    "Store",
    "TermConstruction",
    "StandardLibraryIndex",
    "Value",
    "JitValue",
    "Closed",
    "Open"
  )

  private def declaresConfiguration(parameters: List[Type.Param]): Boolean =
    parameters.exists(parameter =>
      parameter.name.value == "C" && parameter.tbounds.hi.exists(
        _.syntax.contains("NativeSpecializer")
      )
    )

  private def inScope(tree: Tree): Boolean = tree.parent match {
    case None         => false
    case Some(parent) =>
      val here = parent match {
        case definition: Defn.Class => declaresConfiguration(definition.tparams)
        case definition: Defn.Trait => declaresConfiguration(definition.tparams)
        case definition: Defn.Enum  => declaresConfiguration(definition.tparams)
        case definition: Defn.Def   => declaresConfiguration(definition.tparams)
        case declaration: Decl.Def => declaresConfiguration(declaration.tparams)
        case definition: Defn.Type => declaresConfiguration(definition.tparams)
        case _                     => false
      }
      here || inScope(parent)
  }

  // A type parameter of that name in scope (`Computation[State, Value]`) shadows the type of the list.
  private def shadowed(name: String, tree: Tree): Boolean = tree.parent match {
    case None         => false
    case Some(parent) =>
      val parameters = parent match {
        case definition: Defn.Class => definition.tparams
        case definition: Defn.Trait => definition.tparams
        case definition: Defn.Enum  => definition.tparams
        case definition: Defn.Def   => definition.tparams
        case declaration: Decl.Def  => declaration.tparams
        case definition: Defn.Type  => definition.tparams
        case _                      => Nil
      }
      parameters.exists(_.name.value == name) || shadowed(name, parent)
  }

  private def isApplied(name: Type.Name): Boolean = name.parent.exists {
    case Type.Apply(function, _) => function eq name
    case _                       => false
  }

  // The name a class, trait, enum or type alias declares, which is no use of the type.
  private def declaredName(name: Type.Name): Boolean = name.parent.exists {
    case definition: Defn.Class => definition.name eq name
    case definition: Defn.Trait => definition.name eq name
    case definition: Defn.Enum  => definition.name eq name
    case definition: Defn.Type  => definition.name eq name
    case _                      => false
  }

  private def insideImport(tree: Tree): Boolean = tree.parent match {
    case None                          => false
    case Some(_: Import | _: Importer) => true
    case Some(parent)                  => insideImport(parent)
  }

  override def fix(implicit document: SyntacticDocument): Patch =
    document.tree.collect {
      case name @ Type.Name(value)
          if applied.contains(value) && !isApplied(name) && !name.parent.exists(
            _.isInstanceOf[Type.Select]
          ) &&
            !declaredName(name) && !insideImport(name) && !shadowed(
              value,
              name
            ) && inScope(name) =>
        Patch.addRight(name, "[C]")
      case selected @ Type.Select(_, Type.Name(value))
          if applied.contains(value) && !selected.parent.exists {
            case Type.Apply(function, _) => function eq selected
            case _                       => false
          } && !insideImport(selected) && inScope(selected) =>
        Patch.addRight(selected, "[C]")
    }.asPatch
}
