package gezi.standardlibrary

import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.knowledgereading.Reading
import gezi.weakhead.Computation
import gezi.ir.Value
import gezi.ir.{Configured, NoFacts, Pure}

/** The declarations a knowledge term encodes.
  *
  * A knowledge term is a mixin of the fixed-width encoding, three groups of
  * slots (`KnowledgeSlot`), each slot's body a set (a choice) of Scott tuples;
  * a knowledge file is such a mixin, and knowledge files chosen together are
  * one, the choice merging them slot by slot: what several files contribute to
  * is a fixed-width mixin, keyed by no string, and the fields within one
  * declaration are a Scott tuple, not a mixin. The slots, in the order
  * `StandardLibrary.knowledgeSlots` reads them (a "term" is a library term; a
  * "name" is a trie of a string literal, `λk. k "…"`, whose bits the host
  * reads, `KnowledgeReading.trieText`, and which no library function decodes,
  * so the compiler decodes no text in the object language):
  *
  * {{{
  * lemmas                   λs. s "name" left right proof
  *                          proof a constructor of proof_kinds: munit "suite" | md "link" | tex "citation"
  * natives                  λs. s term "implementation"
  * associative, leaves,
  * first_order_constructor,
  * typed_branch,
  * name_marker,
  * closure_marker,
  * tag_origin, tag_next,
  * repeller                 λk. k term
  * representations          λs. s term "representation"
  * families                 λs. s term arity (list of term)    arity an integer
  * fields                   λs. s term constructor (list of criterion)
  *                          criterion a constructor of field_criteria: parameter index | recursive | closed (list of term)
  * jvm_types                λs. s term jvm_type
  *                          jvm_type a constructor of corpora/compiler/backend_vocabulary/jvm_types
  * }}}
  *
  * A list is the library's Scott list, `cons a λ. cons b λ. nil` with
  * `prelude/list` imported, or written closed as `KnowledgeText.scottList`
  * writes it; a bracket is a CBOR array literal and no list of terms.
  *
  * `leaves` are the noinline terms (`Property.Noinline`), `representations` the
  * native specializations, `families` and `fields` the data families and a
  * constructor's fields.
  *
  * A term is read as the author wrote it (`KnowledgeReading.term`). A native, a
  * property and a constructor bind that term, not a name. Every lemma is an
  * equation, so a lemma has no direction.
  *
  * A sum is a Scott constructor of a published list under
  * `corpora/compiler/backend_vocabulary` (`jvm_types`, `proof_kinds`,
  * `field_criteria`), in the order of the cases its reader names here, which a
  * knowledge file imports or writes closed; it is read by the position of the
  * alternative it takes (`KnowledgeReading.alternative`), never by a name. A
  * value that is no such constructor is a `KnowledgeReadingError`.
  */
object KnowledgeFileReading:

  private given NoFacts.type = NoFacts

  /** The declarations of the knowledge term: the members of each slot in the
    * order of `StandardLibrary.knowledgeSlots`, each slot's members in the
    * order their heads are enumerated.
    */
  def declarations(
      knowledge: Configured[NoFacts.type]
  ): Reading[NoFacts.type, Vector[Declaration]] =
    Computation
      .traversed(StandardLibrary.knowledgeSlots)(slot =>
        slotDeclarations(knowledge, slot)
      )
      .map(_.flatten)

  /** The declarations of one slot of the knowledge term: the members of the
    * choice of its contributions' bodies, read as one set, so that a member two
    * contributions give (a knowledge file two presets import) is read once, as
    * a choice is a set.
    */
  def slotDeclarations(
      knowledge: Configured[NoFacts.type],
      slot: KnowledgeSlot
  ): Reading[NoFacts.type, Vector[Declaration]] =
    KnowledgeReading
      .groupSlots(
        Value.of(knowledge),
        KnowledgeSlot.width,
        slot.group,
        KnowledgeSlot.groupWidths(slot.group)
      )
      .flatMap(slots =>
        slots(slot.position).reduceOption(Value.Choice(_, _)) match
          case None      => Computation.pure(Vector.empty)
          case Some(set) => KnowledgeReading.members(set)
      )
      .flatMap(members => Computation.traversed(members)(member(slot, _)))

  private def libraryTerm(
      value: Value[NoFacts.type]
  ): Configured[NoFacts.type] = KnowledgeReading.term(value, Set.empty)

  /** The library term of the value as a fact's key, pure. Throws
    * `StandardLibraryMalformed` with `MalformedReason.ImpureKey` for a term
    * that is not (a parallel layer, a storage or a thunk without holes inside
    * it).
    */
  private def keyTerm(value: Value[NoFacts.type], what: String): Pure =
    val term = libraryTerm(value)
    Pure
      .of(term)
      .getOrElse(
        throw StandardLibraryMalformed(
          MalformedReason.ImpureKey(what, term.toString)
        )
      )

  private def member(
      slot: KnowledgeSlot,
      fields: Vector[Value[NoFacts.type]]
  ): Reading[NoFacts.type, Declaration] = (slot, fields) match
    case (KnowledgeSlot.Lemmas, Vector(name, left, right, proof)) =>
      for
        nameText <- KnowledgeReading.trieText(name)
        proofRead <- lemmaProof(proof)
      yield Declaration.ReadLemma(
        nameText,
        libraryTerm(left),
        libraryTerm(right),
        proofRead
      )
    case (KnowledgeSlot.Natives, Vector(file, implementation)) =>
      // DOWNGRADE (CONTRIBUTING.md, "lambdalattice coding conventions"):
      // the implementation is a CBOR diagnostic notation string literal the host looks up in `NativeBackend`, an
      // explicit exception to the Scott encoding by default, since the implementations are an open
      // set (`NativesProvider`, `NativeBackend.extended`) and a published Scott list a closed one.
      KnowledgeReading
        .trieText(implementation)
        .map(
          Declaration.NativeBinding(keyTerm(file, "a native's library term"), _)
        )
    case (KnowledgeSlot.Associative, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.Associative
        )
      )
    case (KnowledgeSlot.Leaves, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.Noinline
        )
      )
    case (KnowledgeSlot.FirstOrderConstructor, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.FirstOrderConstructor
        )
      )
    case (KnowledgeSlot.TypedBranch, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.TypedBranch
        )
      )
    case (KnowledgeSlot.NameMarker, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.NameMarker
        )
      )
    case (KnowledgeSlot.ClosureMarker, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.ClosureMarker
        )
      )
    case (KnowledgeSlot.TagOrigin, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.TagOrigin
        )
      )
    case (KnowledgeSlot.TagNext, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.TagNext
        )
      )
    case (KnowledgeSlot.Repeller, Vector(file)) =>
      Computation.pure(
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.Repeller
        )
      )
    // A representation is the name of a codec the backend implements in Scala (`NativeBackend.extended` adds a codec
    // by a name of its own, the fixture natural_pairs's natural_pair). A family declared by facts (jvm_types generic,
    // `DeclaredFamilies`) takes its criterion's term as its identity, so it has no representation.
    case (KnowledgeSlot.Representations, Vector(file, argument)) =>
      // DOWNGRADE: the name is a CBOR diagnostic notation string
      // literal the host looks up, the same explicit exception as a native's implementation, above.
      KnowledgeReading
        .trieText(argument)
        .map(text =>
          Declaration.PropertyBinding(
            keyTerm(file, "a property's library term"),
            Property.NativeSpecialization(text)
          )
        )
    case (KnowledgeSlot.JvmTypes, Vector(file, argument)) =>
      jvmType(argument).map(name =>
        Declaration.PropertyBinding(
          keyTerm(file, "a property's library term"),
          Property.JvmType(name)
        )
      )
    case (KnowledgeSlot.Families, Vector(criterion, arity, constructors)) =>
      for
        arityRead <- KnowledgeReading.integer(arity)
        constructorItems <- KnowledgeReading.items(constructors)
      yield Declaration.PropertyBinding(
        keyTerm(criterion, "a data family's criterion"),
        Property.DataFamily(
          number(arityRead),
          constructorItems.map(keyTerm(_, "a data family's constructor"))
        )
      )
    case (KnowledgeSlot.Fields, Vector(criterion, constructor, criteria)) =>
      for
        items <- KnowledgeReading.items(criteria)
        read <- Computation.traversed(items)(fieldCriterion)
      yield Declaration.FieldsBinding(
        keyTerm(criterion, "a data family's criterion"),
        keyTerm(constructor, "a constructor"),
        read
      )
    case (_, other) =>
      throw KnowledgeReadingError(
        s"a member of the slot $slot has ${other.size} fields"
      )

  /** The JVM type a constructor of the published list
    * `corpora/compiler/backend_vocabulary/jvm_types` names, read by the
    * position of its alternative among `JvmTypeName.values`, whose order is the
    * file's. A value that is no constructor of no field of that many
    * alternatives is a `KnowledgeReadingError`.
    */
  private def jvmType(
      value: Value[NoFacts.type]
  ): Reading[NoFacts.type, JvmTypeName] =
    KnowledgeReading.alternative(value, JvmTypeName.values.size).map {
      case (position, Vector()) => JvmTypeName.fromOrdinal(position)
      case (position, other)    =>
        throw KnowledgeReadingError(
          s"the JVM type of alternative $position has ${other.size} fields, not none"
        )
    }

  /** A lemma's proof, a constructor of the published list
    * `corpora/compiler/backend_vocabulary/proof_kinds` (`munit`, `md`, `tex`)
    * whose one field is a trie of a string literal, read as the `LemmaProof` of
    * the alternative. A proof of no such constructor is a
    * `KnowledgeReadingError`; the content is not checked here
    * (`ProofCitations.citationsChecked` checks a Markdown link).
    */
  private def lemmaProof(
      value: Value[NoFacts.type]
  ): Reading[NoFacts.type, LemmaProof] =
    KnowledgeReading.alternative(value, 3).flatMap {
      case (position, Vector(content)) =>
        KnowledgeReading
          .trieText(content)
          .map(text =>
            LemmaProof
              .ofAlternative(position, text)
              .getOrElse(
                throw KnowledgeReadingError(
                  s"a lemma's proof is of the alternative $position"
                )
              )
          )
      case (position, other) =>
        throw KnowledgeReadingError(
          s"a lemma's proof of the alternative $position has ${other.size} fields, not one"
        )
    }

  /** A field criterion, a constructor of the published list
    * `corpora/compiler/backend_vocabulary/field_criteria`: `parameter` of its
    * index, `recursive`, or `closed` of the list of the head and the arguments.
    */
  private def fieldCriterion(
      value: Value[NoFacts.type]
  ): Reading[NoFacts.type, FieldCriterion] =
    KnowledgeReading.alternative(value, 3).flatMap {
      case (0, Vector(index)) =>
        KnowledgeReading
          .integer(index)
          .map(read => FieldCriterion.Parameter(number(read)))
      case (1, Vector())      => Computation.pure(FieldCriterion.Recursive)
      case (2, Vector(terms)) =>
        KnowledgeReading
          .items(terms)
          .map(items =>
            items.headOption match
              case Some(head) =>
                FieldCriterion.Closed(
                  keyTerm(head, "a closed field criterion's head"),
                  items
                    .drop(1)
                    .map(keyTerm(_, "a closed field criterion's argument"))
                )
              case None =>
                throw KnowledgeReadingError(
                  "a closed field criterion names no term"
                )
          )
      case (position, other) =>
        throw KnowledgeReadingError(
          s"a field criterion of the alternative $position has ${other.size} fields"
        )
    }

  private def number(value: BigInt): Int =
    if value >= 0 && value.isValidInt then value.toInt
    else
      throw KnowledgeReadingError(s"$value is no natural number a field holds")
