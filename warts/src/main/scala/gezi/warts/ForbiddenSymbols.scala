package gezi.warts

import org.wartremover.WartTraverser
import org.wartremover.WartUniverse

/** A wart that forbids the symbols a predicate selects: a type tree whose type
  * mentions one, and a reference (an identifier or a selection) to one. An
  * import is skipped, since an import cannot carry `@SuppressWarnings`, and the
  * tree of a declaration annotated with the wart's name is skipped whole
  * (WartRemover's `hasWartAnnotation`).
  */
abstract class ForbiddenSymbols extends WartTraverser:

  /** What the error says. */
  protected def message: String

  /** Whether the symbol with this full name (a module's trailing `$` removed)
    * and this simple name is forbidden.
    */
  protected def isForbidden(fullName: String, simpleName: String): Boolean

  override def apply(u: WartUniverse): u.Traverser =
    new u.Traverser(this):
      import q.reflect.*

      private def forbiddenSymbol(symbol: Symbol): Boolean =
        !symbol.isNoSymbol && isForbidden(
          symbol.fullName.stripSuffix("$"),
          symbol.name.stripSuffix("$")
        )

      private def mentionsForbidden(representation: TypeRepr): Boolean =
        representation match
          case AppliedType(constructor, arguments) =>
            mentionsForbidden(constructor) || arguments.exists(
              mentionsForbidden
            )
          case AndType(left, right) =>
            mentionsForbidden(left) || mentionsForbidden(right)
          case OrType(left, right) =>
            mentionsForbidden(left) || mentionsForbidden(right)
          case ByNameType(underlying)       => mentionsForbidden(underlying)
          case AnnotatedType(underlying, _) => mentionsForbidden(underlying)
          case TypeBounds(low, high)        =>
            mentionsForbidden(low) || mentionsForbidden(high)
          case reference: TypeRef => forbiddenSymbol(reference.typeSymbol)
          case _                  => false

      /** The members the compiler writes for an `enum` (`values`, `valueOf`,
        * `fromOrdinal` and the array `$values`), which return or hold an
        * `Array` that no source declares.
        */
      private def generatedByEnum(definition: Definition): Boolean =
        definition.symbol.flags.is(Flags.Synthetic) &&
          Set("$values", "values", "valueOf", "fromOrdinal")(
            definition.symbol.name
          )

      override def traverseTree(tree: Tree)(owner: Symbol): Unit =
        tree match
          case annotated if hasWartAnnotation(annotated)           =>
          case _: Import                                           =>
          case _: Export                                           =>
          case generated: Definition if generatedByEnum(generated) =>
          case typeTree: TypeTree                                  =>
            if mentionsForbidden(typeTree.tpe) then error(typeTree.pos, message)
          case reference: Ident =>
            if forbiddenSymbol(reference.symbol) then
              error(reference.pos, message)
          case selection: Select =>
            if forbiddenSymbol(selection.symbol) then
              error(selectNamePosition(selection), message)
            else super.traverseTree(tree)(owner)
          case _ => super.traverseTree(tree)(owner)
