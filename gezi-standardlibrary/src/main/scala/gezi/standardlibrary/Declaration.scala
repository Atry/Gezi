package gezi.standardlibrary

import gezi.ir.Instruction

/** One declaration of a knowledge file, checked for its shape. */
enum Declaration:

  /** A lemma read from a knowledge file: its two sides are instructions
    * already, spelled as the front end spells them, and its proof metadata
    * the constructor read under weak head.
    */
  case ReadLemma(
      name: String,
      left: Instruction,
      right: Instruction,
      proof: LemmaProof
  )

  /** A native read from a knowledge file: the library term it binds, written as
    * a name the file binds by its imports, and the native's name.
    */
  case NativeBinding(instruction: Instruction, native: String)

  /** A combinator property read from a knowledge file, of the library term, written as
    * a name the file binds by its imports; a data family's `data_fields` is
    * `FieldsBinding`.
    */
  case PropertyBinding(instruction: Instruction, property: Property)

  /** `data_fields` read from a knowledge file: the family's criterion, the
    * constructor as the file writes it, a library term, and the criteria of
    * its fields. The compiler identifies the constructor by its position in
    * the criterion's `data_family`.
    */
  case FieldsBinding(criterion: Instruction, constructor: Instruction, fields: Vector[FieldCriterion])
