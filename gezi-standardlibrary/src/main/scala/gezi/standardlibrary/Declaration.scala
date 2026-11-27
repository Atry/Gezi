package gezi.standardlibrary

import gezi.ir.{Configured, NoFacts, Pure}

/** One declaration of a knowledge file, checked for its shape. */
enum Declaration:

  /** A lemma read from a knowledge file: its two sides are terms of no facts
    * already, spelled as the front end spells them, and its proof metadata
    * the constructor read under weak head.
    */
  case ReadLemma(
      name: String,
      left: Configured[NoFacts.type],
      right: Configured[NoFacts.type],
      proof: LemmaProof
  )

  /** A native read from a knowledge file: the library term it binds, written as
    * a name the file binds by its imports, and the native's name.
    */
  case NativeBinding(instruction: Pure, native: String)

  /** A combinator property read from a knowledge file, of the library term, written as
    * a name the file binds by its imports; a data family's `data_fields` is
    * `FieldsBinding`.
    */
  case PropertyBinding(instruction: Pure, property: Property)

  /** `data_fields` read from a knowledge file: the family's criterion, the
    * constructor as the file writes it, a library term, and the criteria of
    * its fields. The compiler identifies the constructor by its position in
    * the criterion's `data_family`.
    */
  case FieldsBinding(criterion: Pure, constructor: Pure, fields: Vector[FieldCriterion])
