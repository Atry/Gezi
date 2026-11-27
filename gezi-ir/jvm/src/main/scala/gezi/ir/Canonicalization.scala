package gezi.ir

import com.github.benmanes.caffeine.cache.Interner

/** The canonicalization pool of every interned term on the JVM: one weak
  * interner, so that two terms equal by content are one object while either
  * is reachable (`Interned`). The project `ir-js` compiles the sources of this
  * project for Scala.js with its own pool of this name in place of this
  * file, since Caffeine has no Scala.js build.
  */
private[ir] object Canonicalization:

  // Caffeine's weak interner: library-internal mutable state behind this val,
  // the one canonicalization pool of every constructor, a mutable map
  // encapsulated locally as the underlying store of an immutable interface.
  private val pool: Interner[AnyRef] = Interner.newWeakInterner[AnyRef]()

  /** The live term equal to the given one, or the given one when none is,
    * which the pool then holds weakly. The pool keeps every term as it is
    * given and knows no backend fact: a configuration that converts terms
    * into native storages converts where it builds a term, before it interns
    * it (the JIT's `StorageConstruction`, the readers' `StorageReading`, the
    * e-graph's `TermConstruction`), so that the pool receives the storage.
    */
  def term(made: AnyRef): AnyRef = ScopedValue.where(interned, made).call(() => pool.intern(made))

  // A ScopedValue, bound only within one call of the pool to the object it interns: a global, the user's exception
  // to the immutable Scala, the workaround for Caffeine's interner having no configurable equivalence (the user,
  // 2026-11-25: "好吧，我建议改成ScopedValue"; "对，ScopedValue是Caffeine不支持自定义哈希和相等的workaround").
  // Delete it when the pool takes a hash code and an equality of its own.
  private val interned: ScopedValue[AnyRef] = ScopedValue.newInstance()

  /** Whether the pool is interning this very object on the current thread,
    * so that its hash code and equality are its single layer's; every other
    * object, its fields included, answers by its identity meanwhile.
    */
  def interning(candidate: AnyRef): Boolean = interned.isBound && (interned.get eq candidate)
