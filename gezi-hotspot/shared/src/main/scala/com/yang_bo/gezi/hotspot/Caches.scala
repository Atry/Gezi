package com.yang_bo.gezi.hotspot

/** A namespace a module owns in the cache service, declared as an object in
  * that module, with the types of its keys and values. The framework knows no
  * namespace; a module declares its own, as an ECS declares a component type.
  * What a namespace holds is governed by the cache-table rule
  * (`CONTRIBUTING.md`, "Tables"): costs, or the memo of a pure function the
  * host may compute anyway, keyed by every input of the function; never a type,
  * a membership or an answer read within a budget.
  *
  * TODO (https://github.com/Atry/private-overlay/issues/1549, section 6): a
  * namespace is also to take
  * `(using CacheEncoding[Key], CacheEncoding[Value])`, how its keys and values
  * are written out of the process for a provider that serializes. No such
  * provider exists yet, and no baseline of one, so the encodings would be code
  * nobody calls; they come with the first slow tier.
  *
  * @param name
  *   the namespace's name, unique in the build, for a provider's configuration
  *   and diagnostics
  */
abstract class CacheNamespace[Key, Value](val name: String):

  /** How long the provider may keep the namespace's entries, beside the
    * lifecycle events it clears at. Every entry of every namespace may be
    * dropped at any time (the clearing check), so a retention says only how
    * eagerly; a provider that cannot keep one keeps the entries strongly, which
    * costs memory and nothing else.
    */
  def retention: Retention = Retention.Strong

/** How eagerly a provider may drop a namespace's entries, every one of which
  * can be computed again: the interface tells strong references from weak ones,
  * so that what may be recomputed may be dropped. What is being computed, and
  * so may not be dropped, is not in the cache service at all: it is held by the
  * computation's own state, a value no one else reaches.
  */
enum Retention:

  /** Kept until a lifecycle event at which the provider clears. */
  case Strong

  /** Kept until a lifecycle event, or until the memory runs short. */
  case SoftValues

  /** Kept until a lifecycle event, or until no one holds the key: a key that is
    * an interned term, collected from the interner, can never be asked for
    * again.
    */
  case WeakKeys

/** The cache, handed to every module by the framework. An instruction is the
  * canonical object of its term, so a key or a value holds instructions
  * directly and needs nothing beside it.
  *
  * Two steps, after Rust's lock: `locked` takes the namespace's lock, and the
  * body calls the guard's operations as often as it likes. There is no
  * operation that takes a computation as a function to memoize
  * (`CONTRIBUTING.md`, "Tables"): each use names the namespace, the key and the
  * computation at the call. No lock is taken while another is held: a
  * computation that needs another entry takes that namespace's lock on its own,
  * after the first is released, so a thread holds at most one real lock and no
  * lock order can form a cycle. A long computation runs outside the lock:
  * `tryGet` first, compute on a miss, then `getOrElseUpdate` to write.
  */
trait Cache:

  /** The value of the body, run while the namespace's lock is held. The guard
    * is valid inside the body only and must not escape it.
    */
  def locked[Key, Value, Result](namespace: CacheNamespace[Key, Value])(
      body: CacheGuard[Key, Value] => Result
  ): Result

/** A value that belongs to the thread that made it and must not be shared with
  * another thread or captured in a closure (a lambda, a partial application, an
  * eta-expansion, an anonymous class or a by-name argument) (`CONTRIBUTING.md`,
  * "Tables"), which the custom wart `NoThreadConfinedCapture` of the project
  * `warts` enforces.
  */
trait ThreadConfined

/** The lock of one namespace, held by one thread inside `Cache.locked`. */
trait CacheGuard[Key, Value] extends ThreadConfined:

  /** The value held under the key, if any. Never blocks: a key another thread
    * is computing is answered as absent.
    */
  def tryGet(key: Key): Option[Value]

  /** The value held under the key, or else `value`, which is then written under
    * the key. `value` is by name: a computation is run only when the key is
    * absent, and an already computed value is written only when the key is
    * absent. Whether two threads may both compute it, or one waits for the
    * other, is the provider's policy for the namespace; since an entry is a
    * pure function of its key, the caller cannot tell.
    */
  def getOrElseUpdate(key: Key, value: => Value): Value

/** What the framework, not a module, calls on the provider. An entry of the
  * contest is handed a `Cache` and never the provider, so it can announce no
  * event and connect to no service of its own.
  *
  * TODO (https://github.com/Atry/private-overlay/issues/1549, section 3.7;
  * nothing calls these yet): a provider takes, when it is built, an immutable
  * policy value per namespace, and the callers' code does not change with it.
  *   - Duplicate computation in `getOrElseUpdate`. Hold the lock and compute:
  *     no duplicate, other threads wait. Allow duplicates: release, compute,
  *     take the lock again, write if absent; never blocks. The baselines do
  *     only this one. Compute once: put a placeholder future with `putIfAbsent`
  *     and compute outside the mapping function, never inside
  *     `ConcurrentHashMap.computeIfAbsent`; a thread wanting the same key
  *     waits. Wait cycles across keys stay out of the hotspot executor's path
  *     because it uses the non-blocking `tryGet`.
  *   - Capacity and admission, whose inputs are costs only (`CONTRIBUTING.md`,
  *     "Tables").
  *   - A provider that really locks (a plain `HashMap`, one thread taking the
  *     lock once and calling many times) throws at once when `locked` is
  *     entered on a thread that already holds its guard; thread-safe providers,
  *     whose lock is a no-op, need no such check.
  *   - Tiers are a composition of providers: a fast tier that misses asks a
  *     slow one.
  *   - A provider that persists writes its data out while handling
  *     `RoundFinished`, before the JVM exits.
  */
trait CacheProvider extends Cache:

  /** Clears, at the event, the entries the provider's policy clears. The
    * clearing check (`CONTRIBUTING.md`, "Tables") makes this change only cost,
    * never an answer.
    */
  def lifecycle(event: LifecycleEvent): Unit

/** The boundaries the judge announces. A family's events are there because the
  * judge times a family as a whole, and reuse across the points of a family is
  * what a family rewards.
  */
enum LifecycleEvent:
  case RoundStarted, FamilyStarted, PointStarted, PointFinished, FamilyFinished,
    RoundFinished
