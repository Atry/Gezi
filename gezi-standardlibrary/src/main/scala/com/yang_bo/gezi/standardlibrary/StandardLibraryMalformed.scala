package com.yang_bo.gezi.standardlibrary

/** A malformed standard library, the Prolog compiler's
  * `standard_library_malformed(Reason)`. Every malformed input throws it;
  * nothing is skipped. The message names the reason's kind only.
  */
final case class StandardLibraryMalformed(reason: MalformedReason)
    extends RuntimeException:
  override def getMessage: String =
    s"standard_library_malformed(${reason.productPrefix}): $reason"

/** Why a standard library is malformed. Each case is named after the Prolog
  * compiler's reason (`gezi/prolog/gezi/standard_library.pl`), and its fields
  * are the reason's arguments in order.
  */
enum MalformedReason:

  /** `declared_twice(Name)`: two different lemmas of the knowledge have the
    * name.
    */
  case DeclaredTwice(name: String)

  /** `combinator_property(Slot, Property, Reason)`: the declaration of the
    * property in the knowledge's slot is malformed.
    */
  case CombinatorPropertyMalformed(
      slot: String,
      property: String,
      problem: PropertyProblem
  )

  /** A reason a backend gives when it checks its set of facts (the Prolog
    * compiler's BACKENDS): the backend's module defines it.
    */
  case BackendRejected(reason: BackendReason)

  /** The module's knowledge file does not read as its encoding: a head of
    * another shape, a budget that stopped the reading, or a field of the wrong
    * kind.
    */
  case KnowledgeUnread(module: String, reason: String)

  /** The Markdown link of a lemma's proof does not resolve in the repository
    * (`ProofCitations.citationsChecked`): it is no link `[text](path)` or
    * `[text](path#anchor)`, its path is no file inside the repository, or its
    * anchor is no heading of that file, as the reason says. The compiler does
    * not check it.
    */
  case BrokenCitation(lemma: String, link: String, reason: String)

  /** A library term that a fact uses as its key (a native's, a property's, a
    * data family's constructor or a field criterion's) is no pure term
    * (`com.yang_bo.gezi.ir.Pure`): it holds a parallel layer, a storage or a thunk without
    * holes. `what` says which key, `term` is the term as text.
    */
  case ImpureKey(what: String, term: String)

/** Why the declaration of a combinator property is malformed. */
enum PropertyProblem:

  /** `no_justifying_lemma`: no lemma of the compiled modules has the direction
    * and the two sides the vocabulary gives for the entry.
    */
  case NoJustifyingLemma

  /** A `data_fields` whose constructor is not once among the constructors of
    * the one `data_family` of its criterion.
    */
  case NoConstructor

/** A reason a backend's check of its set gives, defined by the backend's
  * module; this module names no backend.
  */
trait BackendReason
