package gezi.frontend

import gezi.ir.Instruction
import gezi.ir.Layer
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.Apply

/** The four library terms the tagging uses, those the library declares under
  * the front end entries `name_marker`, `closure_marker`, `tag_origin` and
  * `tag_next` (`gezi.standardlibrary.CombinatorPropertyVocabulary`),
  * read and checked by `gezi.standardlibrary.StandardLibraryIndex.occurrenceMarkers`.
  */
final case class OccurrenceMarkers(
    name: Instruction,
    closure: Instruction,
    firstTag: Instruction,
    nextTag: Instruction
)

object OccurrenceMarkers:

  /** The side `λt. λx. M t x` of the marker M's erasure lemma, spelled by
    * the front end as a lemma's sides are.
    */
  def erasing(marker: Instruction): Instruction =
    Defunctionalization.thunkInstruction(
      Term.λ(tag => Term.λ(bound => Term.closed(marker)(tag)(bound))).deBruijnTerm(Map.empty)
    )

  /** The side `λt. λx. x` of every marker's erasure lemma, spelled by the
    * front end as a lemma's sides are.
    */
  def erased: Instruction = Defunctionalization.thunkInstruction(Term.λ(_ => Term.λ(bound => bound)).deBruijnTerm(Map.empty))

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

  /** The term with each constant and each lambda chain tagged. */
  def tagged(term: DeBruijnTerm, markers: OccurrenceMarkers): DeBruijnTerm =
    taggedCounted(term, markers).value

  /** `tagged` with the count of its operations: one for each node the walk
    * visits, and one for each tag interned
    * (`Interning.layerInternedCounted`).
    */
  def taggedCounted(term: DeBruijnTerm, markers: OccurrenceMarkers): Counted[DeBruijnTerm] =
    val (result, state) =
      occurrencesTagged(
        term,
        markers,
        TagState(markers.firstTag, 0)
      ).result
    Counted(result, state.operations)

  /** The instruction of the first tag not yet given, and the count of the
    * operations so far.
    */
  private final case class TagState(tag: Instruction, operations: Long):

    /** The state after the walk visited one more node. */
    def visited: TagState = copy(operations = operations + 1)

    /** The state after the tag was given: the next tag, `next` applied to
      * this one, interned.
      */
    def advanced(next: Instruction): TagState =
      val Counted(instruction, counted) = Interning.layerInternedCounted(Apply(next, tag))
      TagState(instruction, operations + counted)

  private def marked(
      marker: Instruction,
      tag: Instruction,
      term: DeBruijnTerm
  ): DeBruijnTerm =
    DeBruijnTerm.Apply(
      DeBruijnTerm.Apply(DeBruijnTerm.Constant(marker), DeBruijnTerm.Constant(tag)),
      term
    )

  private def occurrencesTagged(
      term: DeBruijnTerm,
      markers: OccurrenceMarkers,
      entered: TagState
  ): TailRec[(DeBruijnTerm, TagState)] =
    val state = entered.visited
    term match
      case DeBruijnTerm.Variable(_) => done((term, state))
      case DeBruijnTerm.Free(name) =>
        throw IllegalArgumentException(s"occurrences are tagged in a term with no free name, found $name")
      case DeBruijnTerm.Constant(_) =>
        done(
          (marked(markers.name, state.tag, term), state.advanced(markers.nextTag))
        )
      case DeBruijnTerm.Lambda(_) =>
        tailcall(chainTagged(term, markers, state.advanced(markers.nextTag)))
          .map((chain, after) => (marked(markers.closure, state.tag, chain), after))
      case DeBruijnTerm.Apply(function, argument) =>
        for
          (functionTagged, afterFunction) <- tailcall(
            occurrencesTagged(function, markers, state)
          )
          (argumentTagged, afterArgument) <- tailcall(
            occurrencesTagged(argument, markers, afterFunction)
          )
        yield (DeBruijnTerm.Apply(functionTagged, argumentTagged), afterArgument)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          (leftTagged, afterLeft) <- tailcall(
            occurrencesTagged(left, markers, state)
          )
          (rightTagged, afterRight) <- tailcall(
            occurrencesTagged(right, markers, afterLeft)
          )
        yield (DeBruijnTerm.Parallel(leftTagged, rightTagged), afterRight)
      case DeBruijnTerm.Choice(left, right) =>
        for
          (leftTagged, afterLeft) <- tailcall(
            occurrencesTagged(left, markers, state)
          )
          (rightTagged, afterRight) <- tailcall(
            occurrencesTagged(right, markers, afterLeft)
          )
        yield (DeBruijnTerm.Choice(leftTagged, rightTagged), afterRight)

  /** A lambda of a chain and the lambdas directly in its body, which continue
    * the chain and take no tag of their own, then the body tagged.
    */
  private def chainTagged(
      term: DeBruijnTerm,
      markers: OccurrenceMarkers,
      entered: TagState
  ): TailRec[(DeBruijnTerm, TagState)] =
    val state = entered.visited
    term match
      case DeBruijnTerm.Lambda(body) =>
        tailcall(chainTagged(body, markers, state))
          .map((chain, after) => (DeBruijnTerm.Lambda(chain), after))
      case body => tailcall(occurrencesTagged(body, markers, entered))
