package gezi.narrowblocks

/** The group blocks: a closed thunk whose body the group grammar reads
  * ([[GroupGrammar]]) is compiled once ([[GroupCompilation]]) into a group
  * program ([[GroupProgram]]), which runs on groups of values, a choice of
  * values for each parameter, row by row: each row one combination of the
  * parameters' members, the block's results the choice of the rows' values.
  * The JIT asks for a block where it reads an application of such a thunk
  * ([[GroupBlockMechanism]], a `gezi.jit.GroupBlocks` mechanism), entering
  * the arguments through their decode points as storages.
  *
  * A program's operations run on a replaceable backend ([[GroupBackend]]):
  * one value per object ([[ScalarGroupBackend]]), or columns of JVM arrays
  * whose kernels the JVM can vectorize ([[JvmArrayGroupBackend]],
  * [[JvmArrayKernels]]); a recursion's finished calls are kept in a memo of
  * the backend's ([[GroupMemo]], [[JvmArrayMemo]]). A run reads back control
  * data only between its rounds and the values once, at its exit.
  *
  * A block adds no answer: it gives the application's answers, or stops with
  * no value, and the machine then reads the application. It stops where its
  * allowance would run out, at a stop asked for, at a cycle of calls, and on
  * a row it would have to drop, a value a filter rejects or a native has no
  * answer for, which may still have an answer in a context consuming it.
  *
  * A compiled block is the artifact the JIT keeps under a thunk of its configuration
  * (`gezi.jit.GroupBlockArtifact[C]`): it holds terms of that configuration and the operations of its storage
  * encoding, runs itself on the arguments the JIT decoded, and builds the values of its results through those
  * operations. A recursion is named in a run by its number in the block, so that a backend's memo holds no term.
  */
package object groups
