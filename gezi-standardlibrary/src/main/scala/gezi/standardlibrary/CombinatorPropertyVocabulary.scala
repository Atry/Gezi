package gezi.standardlibrary

import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.knowledgereading.KnowledgeReading
import gezi.weakhead.Computation
import gezi.ir.Value
import gezi.weakhead.Values
import gezi.ir.{Configured, NoFacts}

/** What justifies an entry of the vocabulary: a lemma whose two sides are
  * the terms, in either order, each the term (of no facts) whose first
  * abstraction binds the combinator (`CombinatorPropertyVocabulary.side`
  * instantiates it); or nothing, for a matching, a front end or a backend
  * entry.
  */
enum Justification:
  case Lemma(
      left: Configured[NoFacts.type],
      right: Configured[NoFacts.type]
  )
  case Matching
  case FrontEnd
  case Backend

/** The vocabulary of combinator properties, ported from the deleted Prolog
  * implementation. A knowledge file declares a property under the
  * property's key, a fact about the library term it writes as a relative
  * path (`KnowledgeFileReading` reads it). An
  * entry is justified (the compiler checks that its lemma is among the
  * compiled modules), matching (what the framework's matching may look
  * into), front end (how the front end writes a program into a term) or
  * backend (how one backend represents a term). A property is raw material
  * from which a strategy computes where and in what order to search, and
  * gives no term and no node a type. Adding a property is adding an entry
  * here.
  *
  *   - `associative` (justified): the combinator C is associative; its lemma
  *     is an equation with, in either order, the sides
  *     `λx. λy. λz. C x (C y z)` and `λx. λy. λz. C (C x y) z`, the row of
  *     the data file `justified_properties.lambdalattice` (a resource of
  *     this package), from which they are read.
  *   - `noinline` (matching): the matching does not unfold C.
  *   - `name_marker`, `closure_marker` (front end): the term N the front end
  *     wraps each occurrence of a library name in, `N T x`, and the term C it
  *     wraps each lambda chain in, `C T c`, T the occurrence's tag
  *     (`gezi.frontend.Occurrences.tagged`). The library must have the
  *     marker's erasure `λt. λx. M t x = λt. λx. x` as a lemma, of which each
  *     wrapping is an instance (`StandardLibraryIndex.occurrenceMarkers`).
  *   - `tag_origin`, `tag_next` (front end): the first tag, and the term
  *     whose application to a tag is the next one; tags only need to be
  *     distinct, so they need no lemma.
  *   - `first_order_constructor` (backend).
  *   - `native_specialization(Representation)` (backend), Representation an
  *     atom.
  *   - `typed_branch` (backend): operational. C is β-equal to the identity
  *     and marks the member `C @ M` of a choice as the branch a backend may
  *     read first, dropping the other members and reading them only when the
  *     marked member gives no normal form. Soundness: if P is the whole
  *     choice and `C @ M` one member, P = C @ M + P, so P ⊑_O C @ M, which
  *     is β-equal to M, and an answer N of M, M ⊑_O N, is one of P;
  *     reading the marked member alone loses answers, never adds one, and the
  *     backend may drop the untyped members. It is an
  *     order of reading, not a fact of the algebra, added because it cannot
  *     yet be avoided (`CONTRIBUTING.md`, "Efficiency by design, with native
  *     structures"): a lemma that adds the typed
  *     member puts its choice at each site's class, a choice does not
  *     distribute over an argument (only (M + N) P = M P + N P is a law), and
  *     dropping the untyped member is a refinement step, which neither a
  *     lemma nor extraction can take. The property is on the marker, not on the member, and
  *     says nothing about a type. The marker's body must be no other
  *     library term's, or hash consing would make every application of that body
  *     a marker; the backend keeps the fallback to the other members.
  *   - `repeller` (justified): operational. C is β-equal to the identity,
  *     and a class of the e-graph that holds an application of C has no
  *     entry in the extraction (`gezi.extraction.CostModel.repeller`), so
  *     that no term the extraction spells reads through it. Its lemma is C's
  *     erasure, with, in either order, the sides `λx. C x` and `λx. x`, the
  *     row of `justified_properties.lambdalattice`. Soundness: leaving a
  *     class out of the extraction leaves out spellings only, every entry
  *     kept being a term of its class, so no answer is added; a lemma that
  *     writes `C M` in a class writes M's own class, C M being M by the
  *     erasure. It is an order of reading, not a fact of the
  *     algebra, as `typed_branch` is: a lemma that writes a negative
  *     conclusion, such as a typed version whose filter its operand's type
  *     is refuted for, cannot take the term out of the e-graph, where it
  *     stays equal to the class's other members (`CONTRIBUTING.md`,
  *     "A negative conclusion is encoded as an attractor's guard"). The
  *     property is on the marker, not on the member, and says nothing about a
  *     type; the marker's body must be no other library term's, for the
  *     reason `typed_branch` gives.
  *   - `data_family(Arity, Constructors)` (backend), on a family's criterion
  *     C: a filter `x ∥ C @ P1 @ … @ Pk` with k = Arity says x is held as a
  *     value of the family whose constructors are the library terms
  *     Constructors, in the order of their cases; a constructor of the family
  *     is its position in that list. The parameters P1 … Pk are read from the
  *     filter as written, never from a value.
  *   - `data_fields(Constructor, Fields)` (backend), on C, for each of its
  *     constructors: the criterion of each field in order, `parameter(I)` (the family's
  *     parameter of the index I, from 0), `recursive` (C at the same
  *     parameters) or a closed criterion, a library term applied to library
  *     terms (`binary_set false`). It is a fact about the family, on its
  *     criterion, and not about the constructor's term: two families'
  *     constructors may be one instruction (the same body) with different
  *     fields, and two constructors of one family are told apart by their
  *     positions.
  *   - `jvm_type(Name)` (backend), on C: the JVM type the family's values are
  *     held as, from the published list: `generic` (the framework's
  *     constructed value, one codec for every declared family; the family's
  *     identity is the criterion C itself, so C needs no
  *     `native_specialization`) and `list`
  *     (the framework's list codec, `ListCodec`, whose declaration must
  *     agree with the codec: one criterion parameter, nil at the position
  *     0 of no field and cons at the position 1 of `parameter(0)` and
  *     `recursive`). On a criterion whose `native_specialization` names a
  *     codec of the backend (big_integer, boolean, list), `data_family`
  *     gives the codec's constructors, each its position, so no `native`
  *     declaration names a constructor: a type and its constructors are named
  *     by the value of the type's definition, never by a name of their own.
  *   The three data entries, like every
  *   backend entry, say how a backend holds a value the term asserts by
  *   a filter; a value's family is read only from the criterion of a filter
  *   written in the term, never from a constructor's instruction, which several
  *   families' constructors may share.
  */
object CombinatorPropertyVocabulary:

  /** What justifies the property of a combinator: for a justified entry,
    * the lemma of its row of `justified_properties.lambdalattice`.
    */
  def justification(property: Property): Justification =
    property match
      case Property.Associative             => justifiedLemma("associative")
      case Property.Noinline                => Justification.Matching
      case Property.NameMarker              => Justification.FrontEnd
      case Property.ClosureMarker           => Justification.FrontEnd
      case Property.TagOrigin               => Justification.FrontEnd
      case Property.TagNext                 => Justification.FrontEnd
      case Property.FirstOrderConstructor   => Justification.Backend
      case Property.NativeSpecialization(_) => Justification.Backend
      case Property.TypedBranch             => Justification.Backend
      case Property.Repeller                => justifiedLemma("repeller")
      case Property.DataFamily(_, _)        => Justification.Backend
      case Property.DataFields(_, _)        => Justification.Backend
      case Property.JvmType(_)              => Justification.Backend

  /** A side of a justifying lemma for the combinator: the side's first
    * abstraction instantiated by the combinator's instruction, by the front end
    * (`Defunctionalization.bodyInstantiated`).
    */
  def side(term: Configured[NoFacts.type], combinator: Configured[NoFacts.type]): Configured[NoFacts.type] =
    Defunctionalization.bodyInstantiated(term, combinator)(using NoFacts)

  private def justifiedLemma(property: String): Justification =
    justifiedLemmas.getOrElse(
      property,
      throw IllegalStateException(s"justified_properties.lambdalattice has no row of $property")
    )

  /** The evaluator steps the reading of the data file may spend. Measured
    * 2026-11-10 (branch problem-data-lambdalattice, a scratch probe): the
    * table 39 steps, a field at most 1,185 (the name read as a text), so the
    * one reading of the file takes under 1,300; the limit is about 10 times
    * that. Since 2026-11-20 a member is read by its position, not by the
    * property's name as a key,
    * so a reading spends less than it did; corpora/compiler/guard_laws, which
    * declares `associative`, compiles within this limit (a scratch probe,
    * 2026-11-12).
    */
  private val readingLimit: Long = 13000L

  /** The properties `justified_properties.lambdalattice` has a member of,
    * in the order of the members.
    */
  private val justifiedProperties: Vector[String] = Vector("associative", "repeller")

  /** The lemmas of the justified entries, by the property's name, read from
    * the resource `justified_properties.lambdalattice` under weak head as
    * `KnowledgeReading` reads knowledge: the file returns a tuple whose one
    * field is the Scott tuple of the members (`KnowledgeReading.soleField`), each `λs. s Left Right`, in the order of
    * `justifiedProperties`.
    */
  private lazy val justifiedLemmas: Map[String, Justification] =
    val stream = Option(getClass.getResourceAsStream("justified_properties.lambdalattice"))
      .getOrElse(throw IllegalStateException("the resource justified_properties.lambdalattice is missing"))
    val text = String(stream.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8)
    given NoFacts.type = NoFacts
    val table = Defunctionalization.thunkInstruction[NoFacts.type](Lambdalattice.term(text))
    def term(value: Value[NoFacts.type]): Configured[NoFacts.type] = Values.instruction(value)
    KnowledgeReading.run(
      KnowledgeReading
        .soleField(Value.of(table))
        .flatMap(group => KnowledgeReading.fields(group, justifiedProperties.size))
        .flatMap(members =>
          Computation.traversed(justifiedProperties.zip(members))((property, member) =>
            KnowledgeReading.fields(member, 2).map {
              case Vector(left, right) => property -> Justification.Lemma(term(left), term(right))
              case other               => throw IllegalStateException(s"a justified property has ${other.size} fields")
            }
          )
        ),
      readingLimit
    ).toMap
