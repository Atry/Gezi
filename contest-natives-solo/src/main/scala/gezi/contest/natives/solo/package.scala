package gezi.contest.natives

/** solo's natives: the implementations that the `native` declarations of
  * `corpora/compiler/solo_binary_natives` bind, found by the JIT through the
  * service `gezi.jit.NativesProvider` (`SoloNatives`). The one native is the
  * product of two canonical binary naturals, the native of
  * `merge_binary_times`, computed on `java.math.BigInteger` by
  * `SoloBinaryOperations.times`, which a narrow block calls as a static
  * method. A native reads only its arguments, the backend's values: no term,
  * no e-graph and no type of its arguments.
  */
package object solo
