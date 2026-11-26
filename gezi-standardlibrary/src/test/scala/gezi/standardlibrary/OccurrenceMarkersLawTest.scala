package gezi.standardlibrary

import hedgehog.Gen
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.OccurrenceMarkers
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Instruction
import gezi.ir.LemmaIdentifier

/** The laws of `StandardLibraryIndex.occurrenceMarkers`:
  * the four front
  * end entries are read by key, and the host tags with a marker only if the
  * library has the marker's erasure `λt. λx. M t x = λt. λx. x`, its sides in
  * either order, the lemma of which each tagging is an instance. The markers
  * and tags are generated closed terms, distinct.
  */
class OccurrenceMarkersLawTest extends GeneratedProperties:

  private def closed(term: Term): Instruction = Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty))

  /** Four closed terms, the name marker, the closure marker, the tag origin
    * and the tag next, distinct by construction: the term of position p under
    * p + 1 binders it does not read.
    */
  private val fourTerms: Gen[Vector[Instruction]] =
    HoasGenerators.closedTerm.list(hedgehog.Range.singleton(4)).map(_.toVector.zipWithIndex.map((term, position) =>
      closed((0 to position).foldLeft(term)((body, _) => Term.λ(_ => body)))
    ))

  private val erased: Instruction = Defunctionalization.thunkInstruction(Lambdalattice.term("λt. λx. x"))

  private def erasing(marker: Instruction): Instruction =
    closed(Term.λ(tag => Term.λ(bound => Term.closed(marker)(tag)(bound))))

  private def index(markers: Vector[Instruction], lemmas: Vector[(Instruction, Instruction)]): StandardLibraryIndex =
    val Vector(name, closure, origin, next) = markers: @unchecked
    StandardLibraryIndex(
      Vector.empty,
      lemmas.zipWithIndex.map { case ((left, right), number) => LemmaSides(LemmaIdentifier(number), left, right) },
      Vector.empty,
      Vector(
        CombinatorProperty(name, Property.NameMarker),
        CombinatorProperty(closure, Property.ClosureMarker),
        CombinatorProperty(origin, Property.TagOrigin),
        CombinatorProperty(next, Property.TagNext)
      )
    )

  /** Whether reading the index's markers throws `IllegalArgumentException`. */
  private def refusal(index: StandardLibraryIndex): Boolean =
    scala.util.Try(index.occurrenceMarkers).failed.toOption.exists(_.isInstanceOf[IllegalArgumentException])

  /** Purpose: catch a reader that takes the four entries from the wrong keys,
    * or refuses a marker whose erasure the library has in either order.
    */
  property("the four markers, each marker's erasure a lemma in either order, are read by key") {
    for
      markers <- fourTerms.forAll
      flipped <- Gen.boolean.forAll
    yield
      val Vector(name, closure, origin, next) = markers: @unchecked
      val sides = (marker: Instruction) => if flipped then (erased, erasing(marker)) else (erasing(marker), erased)
      Result.diff(
        index(markers, Vector(sides(name), sides(closure))).occurrenceMarkers,
        Some(OccurrenceMarkers(name, closure, origin, next))
      )(_ == _)
  }

  /** Purpose: catch the host tagging with a marker the library has no
    * erasure lemma of, a rewrite no proved lemma justifies.
    */
  property("a marker without its erasure lemma is refused") {
    for
      markers <- fourTerms.forAll
      missingName <- Gen.boolean.forAll
    yield
      val Vector(name, closure, _, _) = markers: @unchecked
      val kept = if missingName then closure else name
      val refused = refusal(index(markers, Vector((erasing(kept), erased))))
      Result.assert(refused).log(s"a library with the erasure of $kept alone gave markers")
  }

  /** Purpose: catch a library that declares some of the four entries being
    * read as having no markers, so that its programs go untagged silently.
    */
  property("the entries declared in part are refused") {
    for markers <- fourTerms.forAll
    yield
      val Vector(name, closure, _, _) = markers: @unchecked
      val partial = index(markers, Vector((erasing(name), erased), (erasing(closure), erased)))
        .copy(combinatorProperties = Vector(CombinatorProperty(name, Property.NameMarker)))
      val refused = refusal(partial)
      Result.assert(refused).log("a library declaring the name marker alone gave no error")
  }
