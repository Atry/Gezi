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

  /** The live term equal to the given one, or the given one when none is. */
  def term(made: AnyRef): AnyRef = pool.intern(made)
