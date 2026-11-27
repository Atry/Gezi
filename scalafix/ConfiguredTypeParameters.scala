// Step 0 of the migration of https://github.com/Atry/private-overlay/issues/2261 (section 9): every structure
// that is threaded, copied or holds terms gets the type parameter of its entry's configuration. A syntactic rule,
// written for scalafix 0.14.9's Scala 2.13 runner and run from source, as InternedConstructors.scala is:
//
//   cs launch -M scalafix.cli.Cli ch.epfl.scala:scalafix-cli_2.13.18:0.14.9 -- \
//     --scala-version 3.10.0 --rules=file:scalafix/ConfiguredTypeParameters.scala \
//     --config=scalafix/configured-type-parameters.conf <directories>
//
// It does three things and nothing else:
//   - a declaration of one of the classes, traits, enums or type aliases named in `parameterised` gets the type
//     parameter `C <: NativeSpecializer & Singleton`, first among its type parameters;
//   - in the signatures of those declarations' own members (primary constructor parameters, enum case parameters,
//     the parameter and result types of methods, the types of values), `Instruction` becomes `Configured[C]`,
//     `Value` becomes `Value[C]` and `JitValue` becomes `JitValue[C]`;
//   - outside the front end and the IR, a method of an object, or a top-level method, whose signature names one of
//     those three types gets the same type parameter, first, and the same rewriting of its signature.
// A file it changes outside the package gezi.ir gets one import of `Configured` and `NativeSpecializer` it lacks.
// It recognises the names by their spelling; a name it takes for another type of the same name, the compiler
// reports at step 3. Method bodies, where terms are built, are the hand migration's (step 2).

import scalafix.v1._
import scala.meta._

class ConfiguredTypeParameters extends SyntacticRule("ConfiguredTypeParameters") {

  private val parameter = "C <: NativeSpecializer & Singleton"

  // The declarations of section 4, by name; `Program` only in the ematching sources, whose `Program` it is.
  private val parameterised: Set[String] = Set(
    "ReadingState",
    "ReadingConfiguration",
    "ParallelSet",
    "Head",
    "ReadingExecutor",
    "Executor",
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
    "StandardLibraryIndex"
  )

  private val rewritten: Map[String, String] = Map(
    "Instruction" -> "Configured[C]",
    "Value" -> "Value[C]",
    "JitValue" -> "JitValue[C]"
  )

  private def path(document: SyntacticDocument): String = document.input match {
    case file: Input.VirtualFile => file.path
    case file: Input.File        => file.path.toString
    case other                   => other.toString
  }

  private def declared(name: String, filePath: String): Boolean =
    parameterised.contains(name) || (name == "Program" && filePath.contains("/ematching/src/main/"))

  // The type parameter added to a declaration or a method: first, before the ones it has.
  private def typeParameterAdded(name: Tree, typeParameters: List[Type.Param]): Patch = typeParameters match {
    case Nil          => Patch.addRight(name, s"[$parameter]")
    case first :: _   => Patch.addLeft(first, s"$parameter, ")
  }

  // The three types where they stand in a signature, unapplied; a qualified one (`gezi.ir.Instruction`) whole.
  private def signatureRewrites(signature: Tree): List[Patch] = signature.collect {
    case selected @ Type.Select(_, Type.Name(name)) if rewritten.contains(name) && !applied(selected) =>
      Patch.replaceTree(selected, rewritten(name))
    case named @ Type.Name(name)
        if rewritten.contains(name) && !applied(named) && !named.parent.exists(_.isInstanceOf[Type.Select]) =>
      Patch.replaceTree(named, rewritten(name))
  }

  private def applied(tree: Type): Boolean = tree.parent.exists {
    case Type.Apply(function, _) => function eq tree
    case _                       => false
  }

  private def parameterTypes(parameterLists: List[List[Term.Param]]): List[Tree] =
    parameterLists.flatten.flatMap(_.decltpe.toList)

  private def methodSignature(definition: Defn.Def): List[Tree] =
    parameterTypes(definition.paramss) ++ definition.decltpe.toList

  private def declarationSignature(declaration: Decl.Def): List[Tree] =
    parameterTypes(declaration.paramss) ++ List(declaration.decltpe)

  // The signatures of a declaration's own members, not of members of declarations nested in it.
  private def memberSignatures(statements: List[Stat]): List[Tree] = statements.flatMap {
    case definition: Defn.Def      => methodSignature(definition)
    case declaration: Decl.Def     => declarationSignature(declaration)
    case value: Defn.Val           => value.decltpe.toList
    case variable: Defn.Var        => variable.decltpe.toList
    case declaration: Decl.Val     => List(declaration.decltpe)
    case enumCase: Defn.EnumCase   => parameterTypes(enumCase.ctor.paramss)
    case _                         => Nil
  }

  private def mentions(signature: List[Tree]): Boolean =
    signature.exists(_.collect { case Type.Name(name) if rewritten.contains(name) => true }.nonEmpty)

  private def outsideFrontEndAndIr(filePath: String): Boolean =
    !filePath.contains("/frontend/src/") && !filePath.contains("/ir/src/")

  // Methods of objects and top-level methods: an object's own statements (an object nested in it is found on its own).
  private def objectMethods(statements: List[Stat]): List[Patch] = statements.flatMap {
    case definition: Defn.Def if mentions(methodSignature(definition)) =>
      typeParameterAdded(definition.name, definition.tparams) :: methodSignature(definition).flatMap(signatureRewrites)
    case declaration: Decl.Def if mentions(declarationSignature(declaration)) =>
      typeParameterAdded(declaration.name, declaration.tparams) :: declarationSignature(declaration).flatMap(signatureRewrites)
    case _ => Nil
  }

  override def fix(implicit document: SyntacticDocument): Patch = {
    val filePath = path(document)
    val declarations: List[Patch] = document.tree.collect {
      case definition: Defn.Class if declared(definition.name.value, filePath) =>
        typeParameterAdded(definition.name, definition.tparams) ::
          (parameterTypes(definition.ctor.paramss) ++ memberSignatures(definition.templ.stats)).flatMap(signatureRewrites)
      case definition: Defn.Trait if declared(definition.name.value, filePath) =>
        typeParameterAdded(definition.name, definition.tparams) :: memberSignatures(definition.templ.stats).flatMap(signatureRewrites)
      case definition: Defn.Enum if declared(definition.name.value, filePath) =>
        typeParameterAdded(definition.name, definition.tparams) ::
          (parameterTypes(definition.ctor.paramss) ++ memberSignatures(definition.templ.stats)).flatMap(signatureRewrites)
      case definition: Defn.Type if declared(definition.name.value, filePath) =>
        typeParameterAdded(definition.name, definition.tparams) :: signatureRewrites(definition.body)
    }.flatten
    val methods: List[Patch] =
      if (!outsideFrontEndAndIr(filePath)) Nil
      else
        document.tree.collect {
          case objectDefinition: Defn.Object => objectMethods(objectDefinition.templ.stats)
          case source: Pkg                   => source.stats.collect { case definition: Defn.Def => definition }.flatMap(definition => objectMethods(List(definition)))
        }.flatten
    val changes = declarations ++ methods
    val insideIr = document.tree.collect { case Pkg(reference, _) => reference.syntax }.contains("gezi.ir")
    val imported: Set[String] = document.tree.collect {
      case Importer(reference, importees) if reference.syntax == "gezi.ir" =>
        importees.collect {
          case Importee.Name(Name(name)) => name
          case _: Importee.Wildcard      => "*"
        }
    }.flatten.toSet
    val missing = List("Configured", "NativeSpecializer").filterNot(name => imported.contains(name) || imported.contains("*"))
    val imports =
      if (changes.isEmpty || insideIr || missing.isEmpty) Patch.empty
      else
        Patch.addGlobalImport(
          Importer(Term.Select(Term.Name("gezi"), Term.Name("ir")), missing.map(name => Importee.Name(Name.Indeterminate(name))))
        )
    changes.asPatch + imports
  }
}
