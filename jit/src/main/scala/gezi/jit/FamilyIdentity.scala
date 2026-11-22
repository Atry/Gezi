package gezi.jit

import gezi.ir.Instruction

/** The identity of a data family of the backend (`DataFamily.identity`),
  * the key `NativeBackend.family` finds a family by and the first part of a
  * constructor's name (`NativeName.Constructor`).
  * Two
  * kinds of family share the backend, told apart by where their identity
  * comes from: a family whose codec the backend implements in Scala, named
  * as a native implementation is, by a name outside the mixin tree; and a
  * family declared by facts, whose identity is the term of its criterion:
  * a type and its constructors are named by the value of the type's
  * definition, interned, never by a name of their own.
  */
enum FamilyIdentity:

  /** A family whose codec the backend implements (`big_integer`, `boolean`,
    * `list`, `word`, `binary_natural`, an extension backend's own), named by
    * the name the knowledge's `representations` entry gives
    * (`Property.NativeSpecialization`).
    */
  case Codec(name: String)

  /** A family declared by facts (`DeclaredFamily`: the criterion's
    * `jvm_types` entry is generic, with its `families` and `fields`
    * entries): the criterion's term, interned, so that two criteria are one
    * family exactly when they are one instruction.
    */
  case Declared(criterion: Instruction)

  /** The identity as a message shows it: a codec's name, or the text of a
    * declared family's criterion.
    */
  def shown: String = this match
    case Codec(name)         => name
    case Declared(criterion) => criterion.toString
