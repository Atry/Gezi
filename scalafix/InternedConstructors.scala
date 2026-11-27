// The migration of the IR's layers to one class per constructor (the user,
// 2026-11-14: "能不能定义一套新类，然后用scalafix 批量迁移"). A syntactic rule,
// written for scalafix 0.14.9's Scala 2.13 runner and run from source:
//
//   cs launch -M scalafix.cli.Cli ch.epfl.scala:scalafix-cli_2.13.18:0.14.9 -- \
//     --scala-version 3.10.0 --rules=file:scalafix/InternedConstructors.scala \
//     --config=scalafix/interned-constructors.conf <directories>
//
// It recognises the old constructors by their spelling, `Layer.X` and
// `CodeLayer.X` with the object's name last in the qualifier, and rewrites:
//   - `Layer.Apply`, `Layer.Parallel`, `Layer.Choice`, `Layer.Thunk` and
//     `CodeLayer.<the same>` to the class of the constructor, `Layer.Leaf` to
//     `NoinlineLeaf` and `CodeLayer.Slot` to `Slot`, in terms, patterns and
//     types;
//   - the type `CodeLayer` written without arguments to `CodeLayer[Code]`;
//   - `Layer[?]` to `Layer[Any]`, since a type lambda's alias takes no
//     wildcard argument;
//   - outside the package `com.yang_bo.gezi.ir`, adds one import of the classes the
//     file now names, and of `Code` where `CodeLayer[Code]` was written into
//     a file that does not import it; a file with a wildcard import instead
//     names them `ir.Apply` and imports the package, so that no wildcard
//     import's `Apply` becomes ambiguous.
// What it cannot see (a name the file already binds otherwise, a match that
// the wider union makes inexhaustive) the compiler reports.

import scalafix.v1._
import scala.meta._

class InternedConstructors extends SyntacticRule("InternedConstructors") {

  private val renamed: Map[String, Map[String, String]] = Map(
    "Layer" -> Map(
      "Apply" -> "Apply",
      "Parallel" -> "Parallel",
      "Choice" -> "Choice",
      "Thunk" -> "Thunk",
      "Leaf" -> "NoinlineLeaf"
    ),
    "CodeLayer" -> Map(
      "Slot" -> "Slot",
      "Apply" -> "Apply",
      "Parallel" -> "Parallel",
      "Choice" -> "Choice",
      "Thunk" -> "Thunk"
    )
  )

  private def lastName(qualifier: Term): Option[String] = qualifier match {
    case Term.Name(name)                 => Some(name)
    case Term.Select(_, Term.Name(name)) => Some(name)
    case _                               => None
  }

  private def renaming(qualifier: Term, name: String): Option[String] =
    lastName(qualifier).flatMap(renamed.get).flatMap(_.get(name))

  private def insidePackage(tree: Tree, packageName: String): Boolean =
    tree
      .collect { case Pkg(reference, _) => reference.syntax }
      .contains(packageName)

  private def wildcard(argument: Type): Boolean = argument match {
    case _: Type.Wildcard | _: Type.AnonymousParam => true
    case _                                         => false
  }

  override def fix(implicit document: SyntacticDocument): Patch = {
    val inside = insidePackage(document.tree, "com.yang_bo.gezi.ir")
    // A wildcard import (`import DeBruijnTerm.*`) may bring another `Apply`
    // into scope, which an explicit import of the class would make ambiguous:
    // such a file names the classes through the package, `ir.Apply`.
    // So does a file that defines a member of one of the classes' names (an
    // enum case `View.Apply`), which shadows an import in its own scope.
    val classNames = renamed.values.flatMap(_.values).toSet
    val qualified = !inside && (document.tree
      .collect {
        case Importer(reference, importees) if reference.syntax != "com.yang_bo.gezi.ir" =>
          importees.exists(_.isInstanceOf[Importee.Wildcard])
      }
      .contains(true) || document.tree.collect {
      case definition: Defn.Class
          if classNames.contains(definition.name.value) =>
        true
      case definition: Defn.Object
          if classNames.contains(definition.name.value) =>
        true
      case definition: Defn.EnumCase
          if classNames.contains(definition.name.value) =>
        true
    }.nonEmpty)
    val alreadyImported: Set[String] = document.tree
      .collect {
        case Importer(reference, importees) if reference.syntax == "com.yang_bo.gezi.ir" =>
          importees.collect { case Importee.Name(Name(name)) => name }
      }
      .flatten
      .toSet
    val importsPackage = document.tree
      .collect { case Importer(Term.Name("gezi"), importees) =>
        importees.exists {
          case Importee.Name(Name("ir")) => true; case _ => false
        }
      }
      .contains(true)
    def spelled(name: String): String = if (qualified) s"ir.$name" else name
    val rewrites: List[(Patch, Option[String])] = document.tree.collect {
      case selected @ Term.Select(qualifier, Term.Name(name))
          if renaming(qualifier, name).isDefined =>
        val target = renaming(qualifier, name).get
        (Patch.replaceTree(selected, spelled(target)), Some(target))
      case selected @ Type.Select(qualifier, Type.Name(name))
          if renaming(qualifier, name).isDefined =>
        val target = renaming(qualifier, name).get
        (Patch.replaceTree(selected, spelled(target)), Some(target))
      // Not inside the package com.yang_bo.gezi.ir, whose CodeLayer is the new
      // alias, defined and used there unapplied (`Interned[CodeLayer]`), so
      // that the rule can run again on a tree it has run on.
      case named @ Type.Name("CodeLayer") if !inside && !named.parent.exists {
            case Type.Apply(function, _) => function eq named
            case _: Importee             => true
            case _                       => false
          } && !named.parent.exists(_.isInstanceOf[Importer]) =>
        (
          Patch.replaceTree(named, s"CodeLayer[${spelled("Code")}]"),
          Some("Code")
        )
      // `Layer` becomes a type lambda's alias, which a wildcard argument cannot
      // apply; the alias is covariant, so `Layer[Any]` is the supertype of
      // every layer that `Layer[?]` was.
      case Type.Apply(Type.Name("Layer"), arguments)
          if arguments.exists(wildcard) =>
        (
          arguments
            .filter(wildcard)
            .map(argument => Patch.replaceTree(argument, "Any"))
            .asPatch,
          None
        )
    }
    val names = rewrites.flatMap(_._2).distinct.sorted
    val imports =
      if (names.isEmpty || inside) Patch.empty
      else if (qualified) {
        if (importsPackage) Patch.empty
        else
          Patch.addGlobalImport(
            Importer(
              Term.Name("gezi"),
              List(Importee.Name(Name.Indeterminate("ir")))
            )
          )
      } else {
        val missing = names.filterNot(alreadyImported.contains)
        if (missing.isEmpty) Patch.empty
        else {
          val importees =
            missing.map(name => Importee.Name(Name.Indeterminate(name)))
          Patch.addGlobalImport(
            Importer(Term.Select(Term.Name("gezi"), Term.Name("ir")), importees)
          )
        }
      }
    rewrites.map(_._1).asPatch + imports
  }
}
