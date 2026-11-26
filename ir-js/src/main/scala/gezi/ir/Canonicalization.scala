package gezi.ir

import scala.scalajs.js

/** The canonicalization pool of every interned term under Scala.js, in place
  * of the JVM's weak interner (`ir/src/main/scala/gezi/ir/Canonicalization.scala`),
  * which Caffeine has no Scala.js build of: so that two terms equal by
  * content are one object while either is reachable (`Interned`), as on the
  * JVM.
  *
  * The pool maps a hash code to the weak references of the live terms with
  * that hash code. A term is found by its single layer's hash code and then
  * by its single layer's equality (`ConstructorIdentity.singleLayerHash`,
  * `singleLayerEqual`), its constructor fields compared by identity. A term no longer reachable is
  * collected; the registry then prunes its hash code's references, so the
  * pool holds an entry only for a hash code that had a live term. Scala.js
  * runs on one thread, so the pool needs no lock.
  *
  * A mutable exception the user approved for this pool, 2026-11-16:
  * "同意这个可变例外，写法比照 JVM 上已批准的 Caffeine 弱引用池" (the JVM's pool:
  * "直接改Caffeine的weak interner"; "这里可变Map作为底层接口局部封装例外可以引入",
  * 2026-11-01).
  */
private[ir] object Canonicalization:

  // A mutable js.Map, the pool's buckets: the mutable exception the user approved for this pool,
  // 2026-11-16: "同意这个可变例外，写法比照 JVM 上已批准的 Caffeine 弱引用池".
  private val buckets: js.Map[Int, js.Array[js.WeakRef[AnyRef]]] = js.Map.empty

  // The registry that prunes a collected term's bucket: part of the same mutable exception, 2026-11-16:
  // "同意这个可变例外，写法比照 JVM 上已批准的 Caffeine 弱引用池".
  private val registry: js.FinalizationRegistry[AnyRef, Int, Unit] =
    new js.FinalizationRegistry[AnyRef, Int, Unit]((hash: Int) => pruned(hash))

  /** Whether the pool is interning this very object: never asked under
    * Scala.js, whose pool reads the single layer's hash code and equality
    * itself (`singleLayerHash`, `same`).
    */
  def interning(candidate: AnyRef): Boolean = false

  /** The live term equal to the given one, or the given one when none is,
    * which the pool then holds weakly.
    */
  def term(made: AnyRef): AnyRef =
    val hash = singleLayerHash(made)
    val live = liveTerms(hash)
    live.find(same(made, _)) match
      case Some(found) => found
      case None =>
        buckets.update(hash, js.Array((live :+ made).map(new js.WeakRef(_))*))
        registry.register(made, hash)
        made

  /** The hash code the pool files a term under: a constructor's single
    * layer's, a native storage's own.
    */
  private def singleLayerHash(made: AnyRef): Int = made match
    case constructor: InternedConstructor => ConstructorIdentity.singleLayerHash(constructor)
    case storage: NativeStorage           => storage.contentHash
    case other                            => other.hashCode

  /** Whether the term given is the live one: a constructor by its single
    * layer, a native storage by its own equality.
    */
  private def same(made: AnyRef, live: AnyRef): Boolean = made match
    case constructor: InternedConstructor => ConstructorIdentity.singleLayerEqual(constructor, live)
    case storage: NativeStorage           => live match
        case other: NativeStorage => (storage eq other) || storage.sameContent(other)
        case _                    => false
    case other                            => other == live

  /** The terms of the hash code's bucket still reachable, in the order they
    * entered.
    */
  private def liveTerms(hash: Int): Vector[AnyRef] =
    buckets.get(hash).toVector.flatMap(_.toVector).flatMap(_.deref[AnyRef]().toOption)

  /** The bucket of the hash code with its collected terms' references
    * dropped, and dropped itself when none is left.
    */
  private def pruned(hash: Int): Unit =
    val live = liveTerms(hash)
    if live.isEmpty then
      val _ = buckets.delete(hash)
    else buckets.update(hash, js.Array(live.map(new js.WeakRef(_))*))
