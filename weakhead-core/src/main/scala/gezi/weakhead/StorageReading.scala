package gezi.weakhead

import gezi.ir.{NativeSpecializer, Value}

/** Which natives a reading calls on the native storages it meets: an option of the reading
  * (`ReadingState.storages`), none by default, under which a reading calls none. A backend implements it from its
  * facts (the JIT's `gezi.jit.StorageReadingOfFacts`), whose facts are those of its configuration `C`, so that a
  * reading of another configuration cannot be given it; this module sees the interface only. A reading builds its
  * parallels through its configuration's native specializer (`ReadingConfiguration`), whatever this option says.
  *
  * The option is a part of the completed tables' namespace
  * (`CompletedTableNamespace`), so a reading that takes it and one that does
  * not never read each other's tables. An implementation is therefore equal
  * to another exactly when the two read and build alike (its facts and its
  * natives), and hashes accordingly.
  */
trait StorageReading[C <: NativeSpecializer & Singleton]:

  /** The result of a native the term is an exact application of, if any, and
    * the number of natives called to get it, none called unless every
    * argument has a value: the term is a library term bound to
    * a native applied to exactly its parameters, each of which has a value by
    * a structural path, a storage of the native's place, or an exact
    * application of a native whose arguments have values in turn, called
    * first. None for any other term, which the reading then reads as it is:
    * a term a function that is no native computes, a choice, an open term.
    * The path forces no term: a storage and a native's result are each one
    * value, so the call is `native = define` on one argument each, an
    * equation. A native that throws on arguments in its places is a defect
    * and is not caught.
    */
  def called(term: Value[C]): (Option[Value[C]], Int)
