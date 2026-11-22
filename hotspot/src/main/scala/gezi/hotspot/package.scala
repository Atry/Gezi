package gezi

/** The interfaces of hotspot compilation: an [[Executor]] runs an IR term within a [[Budget]]
  * and gives its [[Progress]], a suspension of its own type that only it
  * resumes, and what it [[Spent]]; a [[Compiler]] compiles a
  * [[CompilationUnit]] of a residual term into the cache service under an
  * [[ArtifactKey]]; a [[TieringPolicy]] gives a [[Decision]] from costs; the
  * [[Cache]], which the framework hands to every module, holds each module's
  * [[CacheNamespace]], read and written through the [[CacheGuard]] of
  * `Cache.locked`; a [[CacheProvider]] is the cache the framework holds,
  * which answers the [[LifecycleEvent]]s of rounds, families and points; and
  * `Forks` (on the JVM only) runs tasks, each with its own budget, on virtual threads and
  * joins them.
  *
  * What the module is for: optimizing memory by profiling and compiling to
  * the most efficient eager code while keeping halting and time complexity,
  * with the simplest choice, collecting nothing at all, kept as an option.
  * Halting, the number of answers and the time complexity are those of
  * tablambda's tabling (Algorithms 1 to 3 of the tablambda paper); which
  * cache to keep is the trade of memory for time that profiling decides,
  * since no local view knows whether a kept cache will be reused globally,
  * and collecting nothing stays one of the choices.
  *
  * Every value here is immutable, but for the providers of the cache
  * service and the inside of `Forks`, local mutable exceptions each
  * recorded at its site; every table is keyed by a term's identity and
  * holds costs or the memo of a pure function the host may compute anyway,
  * never a judgment about what a value is (`CONTRIBUTING.md`, "Tables"). The module depends on `ir` and on `frontend` (for
  * instructions); the baselines are in `hotspot-baselines`, `weakhead`,
  * `jit` (the compiler of code units) and `narrow-blocks` (the compiler of
  * program units).
  *
  * The synchronized convention of the multithreading framework: every
  * mutable data structure belongs to a framework of use, in which its users
  * make it thread safe with `synchronized`, as that framework documents, and
  * both the framework's users and its providers keep the convention. The
  * main logic is pure and immutable and needs no convention. For every
  * mutable data structure, whether a framework provider's or a user's:
  *
  *   - its site names, in a comment, the framework it belongs to and the
  *     monitor that guards it, and its `@SuppressWarnings`
  *     points to that comment;
  *   - every read and every write of its state is inside a `synchronized`
  *     block on that monitor; a structure of the JDK that is thread safe on
  *     its own (`java.util.concurrent.ConcurrentHashMap`) names its own
  *     locking as its monitor, and its operations are its blocks;
  *   - while holding the monitor, the code does no IO, calls no code outside
  *     its framework (no foreign call, no callback of a module) and takes no
  *     other framework's monitor, so the frameworks' locks never nest and
  *     cannot deadlock: IO is done outside the lock and its result recorded
  *     inside it.
  *
  * On the development JDK (25), `synchronized` no longer pins a virtual
  * thread to its carrier (JEP 491, JDK 24), so it works with the virtual
  * threads of `Forks`. A heavily contended monitor may be split by hash into
  * segments, each with its own monitor, under the same rules. Several
  * operating system threads are allowed; a single carrier thread
  * (`jdk.virtualThreadScheduler.parallelism=1`) is a configuration for
  * debugging and reproduction, and correctness does not depend on it.
  * DOWNGRADE: the convention is not checked mechanically.
  */
package object hotspot
