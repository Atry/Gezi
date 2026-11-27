// Step 2 of the migration of https://github.com/Atry/private-overlay/issues/2261 (section 3): the JIT's types of
// native data are covariant in the type of the terms they hold (`NativeValue[+Term]`, `Representation[+Term]`,
// `NativeArgument[+Term]`, `FamilyParameter[+Term]`); where the configuration's `C` is in scope, a use written with no
// argument gets `[JitValue[C]]`. The same syntactic rule as ConfiguredTypeArguments.scala, with another list.
import scalafix.v1._
import scala.meta._

class TermTypeArguments extends SyntacticRule("TermTypeArguments") {

  private val applied: Set[String] = Set("NativeValue", "Representation", "NativeArgument", "FamilyParameter")

  private def declaresConfiguration(parameters: List[Type.Param]): Boolean =
    parameters.exists(parameter => parameter.name.value == "C" && parameter.tbounds.hi.exists(_.syntax.contains("NativeSpecializer")))

  private def inScope(tree: Tree): Boolean = tree.parent match {
    case None => false
    case Some(parent) =>
      val here = parent match {
        case definition: Defn.Class => declaresConfiguration(definition.tparams)
        case definition: Defn.Trait => declaresConfiguration(definition.tparams)
        case definition: Defn.Enum  => declaresConfiguration(definition.tparams)
        case definition: Defn.Def   => declaresConfiguration(definition.tparams)
        case declaration: Decl.Def  => declaresConfiguration(declaration.tparams)
        case definition: Defn.Type  => declaresConfiguration(definition.tparams)
        case _                      => false
      }
      here || inScope(parent)
  }

  // A type parameter of that name in scope (`Computation[State, Value]`) shadows the type of the list.
  private def shadowed(name: String, tree: Tree): Boolean = tree.parent match {
    case None => false
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
          if applied.contains(value) && !isApplied(name) && !name.parent.exists(_.isInstanceOf[Type.Select]) &&
            !declaredName(name) && !insideImport(name) && !shadowed(value, name) && inScope(name) =>
        Patch.addRight(name, "[JitValue[C]]")
      case selected @ Type.Select(_, Type.Name(value))
          if applied.contains(value) && !selected.parent.exists {
            case Type.Apply(function, _) => function eq selected
            case _                       => false
          } && !insideImport(selected) && inScope(selected) =>
        Patch.addRight(selected, "[JitValue[C]]")
    }.asPatch
}
