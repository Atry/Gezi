package gezi

/** The generic reader of knowledge written in lambdalattice:
  * [[KnowledgeReading]] takes the fields off a record of partial functions
  * of literals by their keys, opens Scott constructors, tuples, lists,
  * strings and integers with fresh neutral variables under weak head, and
  * spells a field again as the front end spells it.
  * It knows the encodings and no knowledge: what each key means is
  * `standardlibrary`'s. The module depends on `weakhead-core` and
  * `frontend`, never on `standardlibrary`, which depends on it.
  */
package object knowledgereading
