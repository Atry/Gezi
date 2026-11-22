package gezi.warts

import org.wartremover.WartTraverser
import org.wartremover.WartUniverse

/** Forbids a definition annotated `@volatile`. */
object NoVolatile extends WartTraverser:

  override def apply(u: WartUniverse): u.Traverser =
    new u.Traverser(this):
      import q.reflect.*

      private val volatileSymbol: Symbol = TypeRepr.of[scala.volatile].typeSymbol

      override def traverseTree(tree: Tree)(owner: Symbol): Unit =
        tree match
          case annotated if hasWartAnnotation(annotated) =>
          case definition: ValDef if definition.symbol.hasAnnotation(volatileSymbol) =>
            error(definition.pos, "@volatile is disabled")
          case _ => super.traverseTree(tree)(owner)
