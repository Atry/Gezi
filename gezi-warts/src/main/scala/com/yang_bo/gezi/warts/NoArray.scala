package com.yang_bo.gezi.warts

import org.wartremover.WartTraverser
import org.wartremover.WartUniverse

/** Forbids making or writing an array in source (`CONTRIBUTING.md`, "The code
  * is 100% immutable": no `Array`, an immutable array being `IArray`): the
  * construction `Array(...)`, `new Array`, and `Array.ofDim`, `fill`,
  * `tabulate`, `empty`, `range`, `iterate`, `concat`, `copyOf` and `copyAs`;
  * the write `update`, which `a(i) = x` also reaches; `System.arraycopy` and
  * `java.util.Arrays.fill`, `setAll`, `sort` and `parallelSort`; and `toArray`
  * on a collection.
  *
  * It does not forbid a type that mentions `Array`, reading an array (`apply`,
  * `length`, `toVector`, `IArray.unsafeFromArray`), an array that a JDK call
  * returned, or the `Array[String]` parameter that the compiler generates for a
  * `@main` method: none of these uses an array as mutable state that the source
  * writes.
  */
object NoArray extends WartTraverser:

  private val message: String =
    "making or writing an array is disabled, use IArray"

  private val constructors: Set[String] =
    Set(
      "apply",
      "ofDim",
      "fill",
      "tabulate",
      "empty",
      "range",
      "iterate",
      "concat",
      "copyOf",
      "copyAs"
    )

  private val arraysWrites: Set[String] =
    Set("fill", "setAll", "sort", "parallelSort")

  override def apply(u: WartUniverse): u.Traverser =
    new u.Traverser(this):
      import q.reflect.*

      private def forbiddenSymbol(symbol: Symbol): Boolean =
        !symbol.isNoSymbol && {
          val ownerName = symbol.owner.fullName
          val name = symbol.name
          (ownerName == "scala.Array$" && constructors(name)) ||
          (ownerName == "scala.Array" && (name == "update" || name == "<init>")) ||
          (ownerName.stripSuffix(
            "$"
          ) == "java.lang.System" && name == "arraycopy") ||
          (ownerName.stripSuffix("$") == "java.util.Arrays" && arraysWrites(
            name
          )) ||
          name == "toArray"
        }

      /** The members the compiler writes for an `enum` (`values`, `valueOf`,
        * `fromOrdinal` and the array `$values`), which make an `Array` that no
        * source writes.
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
          case reference: Ident                                    =>
            if forbiddenSymbol(reference.symbol) then
              error(reference.pos, message)
          case selection: Select =>
            if forbiddenSymbol(selection.symbol) then
              error(selectNamePosition(selection), message)
            super.traverseTree(tree)(owner)
          case _ => super.traverseTree(tree)(owner)
