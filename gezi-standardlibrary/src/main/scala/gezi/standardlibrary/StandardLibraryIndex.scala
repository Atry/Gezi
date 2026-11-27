package gezi.standardlibrary

import gezi.frontend.OccurrenceMarkers
import gezi.ir.LemmaIdentifier
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Pure}

/** An entry of the vocabulary of combinator properties
  * (`CombinatorPropertyVocabulary`).
  *
  * A data family's constructors are the terms its `data_family` lists, in the
  * order of their cases, and a constructor of the family is identified by its
  * position in that list (`DataFields`), never by its term alone: α-equivalent
  * library files, such as `zero`, `true` and `nil`, are one term.
  */
enum Property:
  case Associative
  case Noinline
  case NameMarker
  case ClosureMarker
  case TagOrigin
  case TagNext
  case FirstOrderConstructor
  case NativeSpecialization(representation: String)
  case TypedBranch
  case Repeller
  case DataFamily(arity: Int, constructors: Vector[Pure])
  case DataFields(constructor: Int, fields: Vector[FieldCriterion])
  case JvmType(name: JvmTypeName)

/** The criterion of a field of a data family's constructor, as the backend
  * entry `data_fields(Constructor, Fields)` writes it: the family's parameter
  * of the index, `parameter(I)`; the family's own criterion at the same
  * parameters, `recursive`; or a closed criterion, a library term applied to
  * library terms, such as `binary_set false`, the two names bound by the
  * knowledge file's imports from the library's files.
  */
enum FieldCriterion:
  case Parameter(index: Int)
  case Recursive
  case Closed(criterion: Pure, arguments: Vector[Pure])

/** A JVM type a data family's values are held as, from the published list of
  * the backend entry `jvm_type(Name)`: the framework's generic constructed
  * value, or the framework's list codec's lists. The list holds only what a
  * backend reads. A knowledge file writes one as a constructor of
  * `corpora/compiler/backend_vocabulary/jvm_types`, whose fields are in the
  * order of these cases, and `KnowledgeFileReading` reads it by that position:
  * a case added, removed or moved here is changed there too.
  */
enum JvmTypeName:
  case Generic
  case List

/** A lemma's name, its display name only: the knowledge is read whole, so a
  * lemma knows no knowledge file, and is identified by its identifier, one for
  * each direction and pair of sides. Several names may share one identifier.
  * The Prolog compiler interned a lemma as a layer
  * `lemma(Direction, LeftHandle, RightHandle)` of the one hash_consing store;
  * here lemmas are numbered in a space of their own, from 0, in the order their
  * key (direction and the instructions of the two sides) is first met, so that
  * two lemmas of one direction and the same sides have one identifier as they
  * had one instruction.
  */
final case class LemmaNamed(lemma: LemmaIdentifier, name: String)

/** `lemma_sides(LemmaAddress, Left, Right)`: a lemma's two sides, each a closed
  * term of the configuration `C`; every lemma is an equation. The index holds
  * no number of metavariables and no pattern: how the two closed terms become
  * patterns is an entry's encoding (`gezi.lemmaencoding`). A side may hold a
  * parallel (a filter), so it is no `Pure` key and enters a configuration by
  * the library's crossing (`StandardLibraryIndex.crossed`).
  */
final case class LemmaSides[C <: NativeSpecializer & Singleton](
    lemma: LemmaIdentifier,
    left: Configured[C],
    right: Configured[C]
)

/** `native_bound(Address, Name)`: the library term has the native
  * implementation of the name. The term is a key of the facts, so it is pure
  * (`gezi.ir.Pure`), its own specialized spelling under every configuration.
  */
final case class NativeBound(instruction: Pure, native: String)

/** `combinator_property(Address, Property)`: the library term has the property,
  * a pure key of the facts.
  */
final case class CombinatorProperty(instruction: Pure, property: Property)

/** The index of the standard library, the port of
  * `gezi/prolog/gezi/standard_library_index.pl`: three facts and no type, with
  * the names of the lemmas. The facts are in the order the knowledge's
  * declarations are read; each list holds a fact once. The index knows no
  * library file and no declared name of a term: a file is where a term is
  * written, and a term the engine keeps unexpanded is one of a round's leaves
  * (`noinline`). No fact says what a term's type is, which terms are
  * assertions, or which arguments a native decodes; a combinator property is a
  * fact about a library term and gives no term and no node a type.
  */
final case class StandardLibraryIndex[C <: NativeSpecializer & Singleton](
    specializer: C,
    lemmaNames: Vector[LemmaNamed],
    lemmaSides: Vector[LemmaSides[C]],
    nativeBound: Vector[NativeBound],
    combinatorProperties: Vector[CombinatorProperty]
):

  private given C = specializer

  /** The hash, computed once when the index is made: an index is a part of the
    * keys of the cache service's namespaces that are valid for one library
    * (`gezi.jit.DispatchKey`), and each hash walks every fact.
    */
  override val hashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)

  /** The identifier of the one lemma the index names by the name. Throws
    * `IllegalArgumentException` when the name names no lemma or more than one.
    */
  def lemmaIdentifier(name: String): LemmaIdentifier =
    lemmaNames.collect { case LemmaNamed(lemma, `name`) => lemma } match
      case Vector(identifier) => identifier
      case found              =>
        throw IllegalArgumentException(
          s"the index names ${found.size} lemmas $name"
        )

  /** The sides of the lemma, if the index holds them. */
  def sides(lemma: LemmaIdentifier): Option[LemmaSides[C]] =
    lemmaSides.find(_.lemma == lemma)

  /** The library terms that have the property, pure keys. */
  def withProperty(property: Property): Vector[Pure] =
    combinatorProperties.collect {
      case CombinatorProperty(instruction, `property`) =>
        instruction
    }

  /** The library terms that have the property, as terms of this configuration.
    */
  def termsWithProperty(property: Property): Vector[Configured[C]] =
    withProperty(property).map(Configured.fromPure(specializer))

  /** The noinline library terms (the matching entry `noinline`), as terms of
    * this configuration.
    */
  lazy val noinline: Set[Configured[C]] = termsWithProperty(
    Property.Noinline
  ).toSet

  /** The terms the front end tags occurrences with
    * (`gezi.frontend.Occurrences.tagged`), the library terms of the four front
    * end entries `name_marker`, `closure_marker`, `tag_origin` and `tag_next`;
    * nothing when the library declares none of them.
    *
    * Tagging rewrites an occurrence `x` of a library name as `N T x` and a
    * lambda chain `c` as `C T c`. Each rewrite is an instance, read from right
    * to left, of a lemma of the library `λt. λx. M t x = λt. λx. x`, M the
    * marker: the host tags with a marker only if the library has that lemma, so
    * the tagged program equals the program by a proved lemma whatever the tag
    * T. The tags themselves need no lemma: they are only to be distinct.
    *
    * Throws `IllegalArgumentException` when some but not all four are declared,
    * when one is declared more than once, or when a marker has no such lemma,
    * naming the marker and the lemma it needs.
    */
  lazy val occurrenceMarkers: Option[OccurrenceMarkers] =
    val declared = Vector(
      Property.NameMarker,
      Property.ClosureMarker,
      Property.TagOrigin,
      Property.TagNext
    )
      .map(property => property -> withProperty(property))
    if declared.forall((_, instructions) => instructions.isEmpty) then None
    else
      declared.map((property, instructions) =>
        (property, instructions.distinct)
      ) match
        case Vector(
              (_, Vector(name)),
              (_, Vector(closure)),
              (_, Vector(tagOrigin)),
              (_, Vector(tagNext))
            ) =>
          erasureChecked(name, "name_marker")
          erasureChecked(closure, "closure_marker")
          Some(OccurrenceMarkers(name, closure, tagOrigin, tagNext))
        case other =>
          throw IllegalArgumentException(
            s"the occurrence markers are declared ${other.map((property, instructions) => s"$property ${instructions.size} times").mkString(", ")}, not each once"
          )

  /** Throws `IllegalArgumentException` unless a lemma of the library is the
    * marker's erasure `λt. λx. M t x = λt. λx. x`, its sides in either order,
    * spelled by the front end as the lemma's sides are.
    */
  private def erasureChecked(marker: Pure, key: String): Unit =
    val erasing = OccurrenceMarkers.erasing[C](marker)
    val erased = OccurrenceMarkers.erased[C]
    if !lemmaSides.exists(sides =>
        (Configured.same(sides.left, erasing) && Configured
          .same(sides.right, erased)) ||
          (Configured.same(sides.left, erased) && Configured
            .same(sides.right, erasing))
      )
    then
      throw IllegalArgumentException(
        s"the $key $marker has no lemma λt. λx. M t x = λt. λx. x of it in the library, so tagging with it would not be an instance of a proved lemma"
      )

  /** Every term this index holds: the lemmas' sides, the terms bound to natives
    * and those with properties.
    */
  def instructions: Vector[Configured[C]] =
    lemmaSides.flatMap(sides => Vector(sides.left, sides.right)) ++
      (nativeBound.map(_.instruction) ++ combinatorProperties.map(
        _.instruction
      )).map(Configured.fromPure(specializer))

  /** The index whose noinline terms are the leaves, every other fact kept: the
    * index a round is compiled against, its e-graph's leaves the round's own;
    * this index itself when the leaves are its noinline terms. Throws
    * `IllegalArgumentException` for a leaf that is no noinline term of this
    * index, which holds the leaves of every round.
    */
  def withLeaves(leaves: Set[Configured[C]]): StandardLibraryIndex[C] =
    val unknown = leaves -- noinline
    if unknown.nonEmpty then
      throw IllegalArgumentException(
        s"${unknown.size} leaves of a round are no noinline terms of the library's index"
      )
    if leaves == noinline then this
    else
      copy(combinatorProperties =
        combinatorProperties.filter(fact =>
          fact.property != Property.Noinline || leaves.contains(
            Configured.fromPure(specializer)(fact.instruction)
          )
        )
      )

  /** The sides of the lemmas of direction `equation` among those given, by
    * ascending identifier: the lemmas a round enables, those its knowledge term
    * declares (`StandardLibrary.lemmas`; the Prolog e-graph's
    * `enabled_lemma/2`, which sorted them by instruction).
    */
  def enabledEquations(lemmas: Vector[LemmaIdentifier]): Vector[LemmaSides[C]] =
    val enabled = lemmas.toSet
    equations.filter(sides => enabled.contains(sides.lemma))

  /** The sides of every lemma, whichever module declares it, by ascending
    * identifier.
    */
  def equations: Vector[LemmaSides[C]] =
    lemmaSides.sortBy(_.lemma.number)

object StandardLibraryIndex:

  /** The index read with no facts in the configuration of the specializer: the
    * lemmas' sides crossed into its spelling
    * (`NativeSpecializer.crossedAllFromNoFacts`, the library's one crossing),
    * its pure keys as they are.
    */
  def crossed[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[NoFacts.type],
      specializer: C
  ): StandardLibraryIndex[C] =
    val sides: Map[Configured[NoFacts.type], Configured[C]] =
      (specializer: C).crossedAllFromNoFacts(
        index.lemmaSides.flatMap(found => Vector(found.left, found.right))
      )
    StandardLibraryIndex(
      specializer,
      index.lemmaNames,
      index.lemmaSides.map(found =>
        LemmaSides(found.lemma, sides(found.left), sides(found.right))
      ),
      index.nativeBound,
      index.combinatorProperties
    )
