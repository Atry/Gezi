package com.yang_bo.gezi.ematching

/** The backend that compiles a program into Java bytecode: one class file for
  * the whole program, generated with the JDK's `java.lang.classfile` and
  * defined as a hidden class
  * (`MethodHandles.Lookup.defineHiddenClassWithClassData`) that implements
  * `GeneratedProgram`. It depends on `ematching` alone; `backendcomparison`
  * selects it.
  *
  * THE DOWNGRADE. `java.lang.classfile` is driven by mutable builders handed to
  * lambdas, which CONTRIBUTING.md's immutability rule ("The code is 100%
  * immutable") forbids. The user, 2026-10-31: "这里可以作为例外，在局部使用可变的 builder". The
  * builders are used in `ClassFileGeneration.scala` alone, inside the one call
  * that turns a program into a defined class; no builder, and not the bytes, is
  * stored, returned or shared. Everything else (the program, the compiled
  * program, the registers, the graph) stays immutable.
  *
  * THE GENERATED CODE's DISCIPLINE. It writes no field (the class has none) and
  * no array; its constants (heads, member shapes, roles, holes, the empty
  * matching of each tree) come from the class data through
  * `MethodHandles.classDataAt`, a constant resolved once. The registers of a
  * key's seed tree are JVM locals of its method, written once on each path
  * through the method after their initial -1; the only locals written again are
  * those that belong to one frame alone: an `Each` loop's index, a witness's
  * count of entries read, and the matching accumulated so far, an immutable
  * `Searched` replaced by a new one. A building's graphs and nodes are fresh
  * locals each, written once.
  *
  * UNLOADING. The hidden class is defined without `ClassOption.STRONG`, so that
  * it is unloaded once the compiled program that holds its one instance is
  * unreachable (JEP 371), independently of the defining loader; nothing else
  * keeps the class. Under the measurement's serial collector, classes are
  * unloaded only at full collections.
  */
package object bytecode
