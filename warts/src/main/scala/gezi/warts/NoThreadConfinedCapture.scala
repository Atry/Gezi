package gezi.warts

import org.wartremover.WartTraverser
import org.wartremover.WartUniverse

/** Forbids capturing a value of a `gezi.hotspot.ThreadConfined` type in a
  * closure: a lambda, a partial application or an eta-expansion (each an
  * anonymous function), an anonymous class, or a by-name argument. Such a value
  * belongs to the thread that made it (`CONTRIBUTING.md`, "Tables": the cache
  * service's guard is thread-unsafe), and a closure may run later or on another
  * thread. A reference inside a closure to a value of such a type defined
  * outside it is reported; a value the closure itself defines or takes as a
  * parameter is not, so a body handed the guard as its parameter
  * (`Cache.locked(namespace) { guard => … }`) may use it, but not hand it on in
  * a closure of its own. An argument of an inline method, a lambda or a by-name
  * argument, is inlined at the call and is no closure at run time, so it may
  * use the value (`CONTRIBUTING.md`, "Tables").
  *
  * The type is recognised by the full name of a base class, not by a class
  * symbol, so that a project without `gezi.hotspot` on its classpath compiles
  * under the wart.
  */
object NoThreadConfinedCapture extends WartTraverser:

  private val confinedName: String = "gezi.hotspot.ThreadConfined"

  private val message: String =
    "a ThreadConfined value is captured in a closure"

  override def apply(u: WartUniverse): u.Traverser =
    new u.Traverser(this):
      import q.reflect.*

      private def confined(symbol: Symbol): Boolean =
        symbol.isTerm && !symbol.isNoSymbol && (symbol.isValDef || symbol.flags
          .is(Flags.Param)) &&
          symbol.termRef.widen.baseClasses.exists(_.fullName == confinedName)

      private def closureDefinition(tree: Tree): Boolean = tree match
        case definition: DefDef   => definition.symbol.isAnonymousFunction
        case definition: ClassDef => definition.symbol.isAnonymousClass
        case _                    => false

      /** The symbols the tree defines anywhere within it, its parameters
        * included.
        */
      private def defined(tree: Tree, owner: Symbol): Set[Symbol] =
        new TreeAccumulator[Set[Symbol]]:
          def foldTree(found: Set[Symbol], tree: Tree)(
              owner: Symbol
          ): Set[Symbol] =
            val here = tree match
              case definition: Definition => found + definition.symbol
              case _                      => found
            foldOverTree(here, tree)(owner)
        .foldTree(Set.empty, tree)(owner)

      /** Reports each reference within the closure to a confined value it does
        * not define. A closure nested in it is checked on its own, so that a
        * capture is reported once, at the innermost closure.
        */
      private def checked(closure: Tree, owner: Symbol): Unit =
        val inside = defined(closure, owner)
        new TreeTraverser:
          override def traverseTree(tree: Tree)(owner: Symbol): Unit =
            tree match
              case nested if (nested ne closure) && closureDefinition(nested) =>
              case reference: Ident
                  if confined(reference.symbol) && !inside.contains(
                    reference.symbol
                  ) =>
                error(reference.pos, message)
              case _ => super.traverseTree(tree)(owner)
        .traverseTree(closure)(owner)

      /** The arguments of the application passed to by-name parameters. */
      private def byNameArguments(application: Apply): List[Term] =
        application.fun.tpe.widen match
          case method: MethodType =>
            application.args.zip(method.paramTypes).collect {
              case (argument, ByNameType(_)) => argument
            }
          case _ => Nil

      /** Whether the application calls an inline method, whose arguments are
        * inlined at the call and are no closure at run time.
        */
      private def inlineCall(application: Apply): Boolean =
        val called = application.fun.symbol
        !called.isNoSymbol && called.flags.is(Flags.Inline)

      override def traverseTree(tree: Tree)(owner: Symbol): Unit =
        tree match
          case annotated if hasWartAnnotation(annotated) =>
          case closure if closureDefinition(closure)     =>
            checked(closure, owner)
            super.traverseTree(tree)(owner)
          case application: Apply if inlineCall(application) =>
            traverseTree(application.fun)(owner)
            application.args.foreach {
              case Block(List(function: DefDef), _: Closure)
                  if function.symbol.isAnonymousFunction =>
                function.rhs.foreach(body =>
                  traverseTree(body)(function.symbol)
                )
              case argument => traverseTree(argument)(owner)
            }
          case application: Apply =>
            byNameArguments(application).foreach(argument =>
              checked(argument, owner)
            )
            super.traverseTree(tree)(owner)
          case _ => super.traverseTree(tree)(owner)
