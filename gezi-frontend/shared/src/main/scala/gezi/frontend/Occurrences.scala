package gezi.frontend

import gezi.ir.{Configured, NativeSpecializer, Pure}
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The four library terms the tagging uses, those the library declares under
  * the front end entries `name_marker`, `closure_marker`, `tag_origin` and
  * `tag_next` (`gezi.standardlibrary.CombinatorPropertyVocabulary`),
  * read and checked by `gezi.standardlibrary.StandardLibraryIndex.occurrenceMarkers`: pure keys of the facts, which
  * enter a program's configuration as they are (`Configured.fromPure`).
  */
final case class OccurrenceMarkers(
    name: Pure,
    closure: Pure,
    firstTag: Pure,
    nextTag: Pure
)

object OccurrenceMarkers:

  /** The side `λt. λx. M t x` of the marker M's erasure lemma, spelled by
    * the front end as a lemma's sides are.
    */
  def erasing[C <: NativeSpecializer & Singleton](marker: Pure)(using specializer: C): Configured[C] =
    Defunctionalization.thunkInstruction[C](
      Term.λ(tag => Term.λ(bound => Term.closed(Configured.fromPure(specializer)(marker))(tag)(bound))).deBruijnTerm(Map.empty)
    )

  /** The side `λt. λx. x` of every marker's erasure lemma, spelled by the
    * front end as a lemma's sides are.
    */
  def erased[C <: NativeSpecializer & Singleton](using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](Term.λ(_ => Term.λ(bound => bound)).deBruijnTerm(Map.empty))

/** The occurrence tagging of a program (the module comment of
  * `gezi/prolog/gezi/surface.pl`, OCCURRENCES). Hash consing
  * makes equal subterms of a program one term, and a library whose lemmas
  * type each occurrence of a name and each closure on its own (HM's, which
  * instantiates a name's scheme at each occurrence) has the front end tag
  * them: each occurrence `x` of a library name becomes `N T x`, and each
  * lambda chain `c` (a lambda directly in a lambda's body continuing it)
  * `C T c`, N and C the library's `name_marker` and `closure_marker`, T the
  * occurrence's tag: `next (... (next first))`, `first` and `next` its
  * `tag_origin` and `tag_next`, with as many `next` as
  * occurrences come before it in preorder. Each tag is interned as it is
  * given, one application layer over the previous tag's instruction, so that a
  * tag is one leaf and the tagging is linear in the program.
  *
  * The Prolog front end tags the surface term before it translates it; here
  * the de Bruijn term is tagged after the translation. The two agree: the
  * translation keeps the order of the subterms, maps the instruction leaves to
  * constants and the lambdas of a chain to nested lambdas, and the tagging
  * throws nothing, so a term that fails to translate fails with the same
  * error.
  */
object Occurrences:

  /** The term with each constant and each lambda chain tagged, in the configuration of the specializer in scope. */
  def tagged[C <: NativeSpecializer & Singleton](term: DeBruijnTermOf[Configured[C]], markers: OccurrenceMarkers)(using
      C
  ): DeBruijnTermOf[Configured[C]] =
    taggedCounted(term, markers).value

  /** `tagged` with the count of its operations: one for each node the walk
    * visits, and one for each tag interned
    * (`Interning.layerInternedCounted`).
    */
  def taggedCounted[C <: NativeSpecializer & Singleton](term: DeBruijnTermOf[Configured[C]], markers: OccurrenceMarkers)(using
      specializer: C
  ): Counted[DeBruijnTermOf[Configured[C]]] =
    val (result, state) =
      Tagging(markers, specializer).occurrencesTagged(term, TagState(Configured.fromPure(specializer)(markers.firstTag), 0)).result
    Counted(result, state.operations)

  /** The instruction of the first tag not yet given, and the count of the
    * operations so far.
    */
  private final case class TagState[C <: NativeSpecializer & Singleton](tag: Configured[C], operations: Long):

    /** The state after the walk visited one more node. */
    def visited: TagState[C] = copy(operations = operations + 1)

    /** The state after the tag was given: the next tag, `next` applied to
      * this one, interned.
      */
    def advanced(next: Configured[C])(using C): TagState[C] =
      val Counted(term, counted) = Interning.applicationInternedCounted(next, tag)
      TagState(term, operations + counted)

  /** The walk of one tagging, in the configuration of the specializer, its markers as terms of that configuration. */
  private final class Tagging[C <: NativeSpecializer & Singleton](markers: OccurrenceMarkers, specializer: C):

    private given C = specializer

    private val name: Configured[C] = Configured.fromPure(specializer)(markers.name)
    private val closure: Configured[C] = Configured.fromPure(specializer)(markers.closure)
    private val nextTag: Configured[C] = Configured.fromPure(specializer)(markers.nextTag)

    private def marked(
        marker: Configured[C],
        tag: Configured[C],
        term: DeBruijnTermOf[Configured[C]]
    ): DeBruijnTermOf[Configured[C]] =
      DeBruijnTerm.Apply(
        DeBruijnTerm.Apply(DeBruijnTerm.Constant(marker), DeBruijnTerm.Constant(tag)),
        term
      )

    def occurrencesTagged(
        term: DeBruijnTermOf[Configured[C]],
        entered: TagState[C]
    ): TailRec[(DeBruijnTermOf[Configured[C]], TagState[C])] =
      val state = entered.visited
      term match
        case DeBruijnTerm.Variable(_) => done((term, state))
        case DeBruijnTerm.Free(name) =>
          throw IllegalArgumentException(s"occurrences are tagged in a term with no free name, found $name")
        case DeBruijnTerm.Constant(_) =>
          done(
            (marked(name, state.tag, term), state.advanced(nextTag))
          )
        case DeBruijnTerm.Lambda(_) =>
          tailcall(chainTagged(term, state.advanced(nextTag)))
            .map((chain, after) => (marked(closure, state.tag, chain), after))
        case DeBruijnTerm.Apply(function, argument) =>
          for
            (functionTagged, afterFunction) <- tailcall(
              occurrencesTagged(function, state)
            )
            (argumentTagged, afterArgument) <- tailcall(
              occurrencesTagged(argument, afterFunction)
            )
          yield (DeBruijnTerm.Apply(functionTagged, argumentTagged), afterArgument)
        case DeBruijnTerm.Parallel(left, right) =>
          for
            (leftTagged, afterLeft) <- tailcall(
              occurrencesTagged(left, state)
            )
            (rightTagged, afterRight) <- tailcall(
              occurrencesTagged(right, afterLeft)
            )
          yield (DeBruijnTerm.Parallel(leftTagged, rightTagged), afterRight)
        case DeBruijnTerm.Choice(left, right) =>
          for
            (leftTagged, afterLeft) <- tailcall(
              occurrencesTagged(left, state)
            )
            (rightTagged, afterRight) <- tailcall(
              occurrencesTagged(right, afterLeft)
            )
          yield (DeBruijnTerm.Choice(leftTagged, rightTagged), afterRight)

    /** A lambda of a chain and the lambdas directly in its body, which continue
      * the chain and take no tag of their own, then the body tagged.
      */
    private def chainTagged(
        term: DeBruijnTermOf[Configured[C]],
        entered: TagState[C]
    ): TailRec[(DeBruijnTermOf[Configured[C]], TagState[C])] =
      val state = entered.visited
      term match
        case DeBruijnTerm.Lambda(body) =>
          tailcall(chainTagged(body, state))
            .map((chain, after) => (DeBruijnTerm.Lambda(chain), after))
        case body => tailcall(occurrencesTagged(body, entered))
