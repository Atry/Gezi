# Contributing to Gezi

This file is the contributor's guide to Gezi: what the language is for, how a run goes through the code, the design
principles every change is weighed by, the conventions of the code and of lambdalattice text, a map of the framework,
and how to build and test. `README.md` says how to use Gezi; this file says how to change it.

## The Vision

Gezi is a practical programming language. A programmer writes untyped λ-lattice terms at whatever level of abstraction
they like, in any equivalent spelling; the program runs as fast as an expert's typed native code, works with the JVM and
other ecosystems, and never gives a wrong answer (for a program that calls external services, under the conditions the
FFI states for them). An exception to what follows is recorded where it stands, as an exception.

- Meaning is Definition 14 (⊑_O, section "Terms" below), which is not computable. Every executor (weak-head, eager,
  the e-graph, the JIT) is a sound approximation of it: it may lose answers, never add one. Its evaluation order,
  caching, tables, call counts and where it stops are its behaviour, not what a program means.
- The default semantics is the best approximation so far, best as scored over a benchmark of problems against native
  reference solutions. It is predictable, weak-head and eager approximate it in turn, and it evolves as lemmas are
  added, using speculation, fallback, profiling and hotspot optimisation. So whatever you build is one replaceable,
  configurable option among those that entries choose between. A module need not beat the existing ones everywhere: it
  is useful where it is better in some cases. The speed of the whole is the work of speculation, hotspot compilation
  and whole-block lemma rewriting, which choose between modules by measured cost, not the work of any one module.
  So a new module for an existing interface, a copy-on-write improvement included, needs no proof of performance: it
  replaces nothing and so regresses nothing. Its review asks whether it breaks a rule, keeps the architecture's
  conventions, and is modular, reusable and configurable. No module is ever made more complex inside, or less
  composable, to meet a performance target.
- The compiler is knowledge: library files, lemmas sound by Definition 14, natives and combinator properties. Types and
  rules live only in the term and the library. The host decides nothing by a type, a rule or a name: every typing and
  rewriting choice is a pure function of the term's structure, and a strategy weighs measured costs and nothing else.
  Names the host keeps for display, provenance and proofs decide nothing.
- Programs that HM accepts compile whole-block onto native representations, in linear time, with no dispatch and no
  decoding midway. Several types or encodings are options, and more of them never make anything slower. Programs written
  by their definition (a DP by its recursion, a search on an infinite graph) are recognised by lemmas and replaced by the
  best known algorithm, at the speed of optimal Java bytecode.
- The object language has no mutation, so a program cannot cache explicitly; caching is the host's choice. There is no
  free lunch: without a cache a computation may be repeated, with one it pays space and time, and a local hotspot often
  runs faster untabled. Tabling is the default and dropping a table the speculation: tabling costs at most a constant
  factor over not tabling, while not tabling can cost exponentially more. Which tables to drop, and whether a hotspot
  runs untabled, is a configurable option decided by profiling, never a fixed rule. The tabled weak-head's fixpoint over
  the calls in progress is another matter: it gives the reference reading its halting and its answers, and weak head
  without it is not a reference reading.
- Intermediate state and configuration are terms read by the same interpreter, so the interpreter may be slower than
  native code by a constant factor, but its time complexity has no evident defect.

## The Architecture

The main line every run takes. Whoever moves it updates this section in the same commit.

- An entry (`gezi.contest.entry.Entry`, built by `EntryProvider.initial`) is one configured approximation. The judge
  (`contest-judge`, through `contest-runner` in the entry's JVM) and the Jupyter kernel (`jupyter-kernel`) are
  adapters: each hands an entry its cells (`Entry.run(cell, source, stop)`) and decides nothing about how they are
  evaluated. The source (`gezi.hotspot.ExpansionSource`) is the version of the files the cell's URI nodes expand to,
  which only the adapter knows: the judge gives one for its run, the kernel one for each cell, and nothing an executor
  kept under one source answers under another.
- An entry's configuration is its data, `entry.lambdalattice`, read by the same interpreter (`EntryData`): its lemma
  rounds, its backend's knowledge and its options, each option a Scott constructor published under
  `corpora/compiler/entry_options`, none defaulted in the data. What the entry alone writes is a Scott tuple read by
  position (the compiler `λs. s rounds backend`, a round and the backend `λs. s knowledge options`); what several
  files contribute to is a fixed-width mixin, knowledge that of `KnowledgeSlot` and the options of a round and of the
  backend one with no self, a multi-valued Scott coproduct of groups of slots (`KnowledgeReading.coproductGroupSlots`),
  so that presets contribute options by the choice, a slot written with two different values being refused: the host
  reads no string key, except for the exception in "lambdalattice coding conventions" below, a native's implementation
  name and a representation's codec name. `Defaults` is the one place the framework chooses the default implementation
  of each replaceable interface.
- Executors share `gezi.hotspot.Executor`, whose calls take and return `gezi.hotspot.ExecutionDependencies`, the cache
  service and the expansion source an execution runs against. `ReadingExecutor(mode, jitState)` runs the tabled weak head or the JIT
  (`Mode.Jit`). An entry's data chooses the executor that reads its programs by its `executor`
  (`ExecutorOption`, `Defaults.executor`): `jit`, the framework's, or `module selector parameters`, the executor of a
  module registered with `java.util.ServiceLoader` (`ExecutorModule`), found by the interned instruction of its
  selector, the term its selector file gives, never by a name (`ExecutorModules`). A round's `extractor` opens its list
  the same way: `module selector parameters` is the extraction of a module registered with `java.util.ServiceLoader`
  (`ExtractorModule`), together with the narrow blocks' route it pairs with, `gezi.narrowblocks.LemmaRoute` for a
  module that changes only the extraction, both built from its parameters and `ExtractorModuleInputs` and found by its
  selector's interned instruction (`ExtractorModules`, `Defaults.route`, `Defaults.extractor`). A module of either kind
  lives in a project `contest-modules-<name>` that depends on contest-entry and registers itself in its own
  `META-INF/services`; every entry's project depends on every module's, and the suites that read the in-tree entries
  (`InTreeEntriesTest`, `CancelGraceLawTest`, `CompilationPlaceLawTest`) are in the test-only project
  `contest-in-tree-entries`, which depends on every entry's, since the framework's `contest-entry-generic` sees no
  module.
- An entry's lemma rounds rewrite a program on the e-graph (`LemmaRoute.compiledRounds`), where its data's
  `compilation_place` (`CompilationPlaceOption`, `Defaults.compilationPlace`) says: `upfront`, the generic entry runs
  them (`ProgramCompiler.compiledProgram`) before the executor reads the program; `by_executor`, the generic entry runs
  none and hands the executor the program uncompiled, the entry's prepared compilation
  (`gezi.narrowblocks.ProgramCompilation`, built once at the entry's setup whatever the option says) a field of
  `ExecutorModuleInputs`, so that a module may interpret within a small budget and compile only what does not finish,
  as the tiered module `contest-modules-solo-tiering` does; the framework's executor reads the uncompiled program as it
  is. Under `by_executor` no round's reports, article or trace are written (a FIXME in `GenericEntry.answered`).
  Before the rounds, the generic entry tags the program as occurrences as its data's `occurrence_tagging` says
  (`OccurrenceTaggingOption`, `Defaults.occurrencesTagged`): `untagged`, the program as the cell gives it, or
  `names_and_closures`, its lambda chains and shared parts marked with the library's occurrence markers
  (`gezi.frontend.ProgramOccurrences`), so that a library whose lemmas type each occurrence on its own, the HM
  baseline's, has occurrences to start from on a point whose library terms are inlined.
- The tabled weak head applies a function to a continuation as its `ReadingState.continuations` says
  (`ContinuationReading`): `Substituted`, the β rule as it is, the reference reading's; or `Packed`, a head that uses
  its continuation in tail position read as applied to a closed pack first, its work before the continuation shared,
  each step checked and a failed check falling back. An entry chooses it by its data's `continuation`, which
  `Defaults.executor` passes to its `ReadingExecutor` and `GenericEntryProvider.initializedWithLibrary` to the read of
  its knowledge; an entry's data itself is read under `Defaults.entryDataState`, `Packed`. A `Packed` reading's marks of
  failed checks are kept and dropped with its tables, and shared with them through the cache service
  (`SharedReadingTables`). The tabled weak head reads a parallel as its `ReadingState.parallels` says
  (`ParallelReading`): `BothSides`, the reference reading's, each parallel set of one side with each of the other's; or
  `HeadsMet`, each parallel set met head by head, the lambda heads of one code merged by their fillings and a set of
  heads that apply different binders dropped, which may lose answers and adds none, and reads a fold over a list
  filtered by a recursive type in steps linear in the list. An entry chooses it by its data's `parallel`, which
  `Defaults.executor` passes to its `ReadingExecutor`; the read of its knowledge stays `BothSides`. The cache service
  keeps the tables of the two apart (`CompletedTableNamespace`). FIXME: the option reaches the tabled weak head only. An https://github.com/Atry/private-overlay/issues/2018
  entry's executor reads under `Mode.Jit`, whose parallel heads (`Jit`'s `JitValue.Parallel`, `JitHead.Parallel`) do
  not meet their heads, so for every entry today the option changes nothing.
- What an executor keeps between calls is in the executor it returns: the JIT's `JitState`, whose instance table the
  entry's `JitOptions` configure, and the readings' tables as its `TableRetention` says, chosen by the entry's data's
  `table_retention` (none kept, all kept, or all until a share of the table limit). What executors share is
  `gezi.hotspot.Cache`, whose `CacheProvider` an adapter builds (`Defaults.caches`) and sends `LifecycleEvent`s. A
  reading keeps its complete tables there, the tabled weak head's and the JIT instance table's, and the JIT its
  compiled codes, when its `ReadingState.sharing` says so (`TableSharing`): the tables in progress stay in the state,
  the namespace declares the references' strength (`Retention`), and the adapter's lifecycle events clear it. The JIT's
  state keeps its own copies as its `InstanceRetention` says, a bounded first level before the service. The problem
  corpora read so (`ProblemFamilies`); an entry chooses it by its data's `table_sharing`, which `Defaults.executor`
  passes to its `ReadingExecutor`.
- The default semantics of the Vision is the entry this section names, the best approximation so far by the scored
  benchmark: `contest-entries-plover`, which selects the narrow list block and whose knowledge recognises dynamic
  programs written by their definition (counting dice sums and coin combinations, removing digits, modular
  exponentiation) and replaces them through lemmas by native algorithms. Naming it runs nothing: the kernel and the judge run the entry they are given, and there is no
  default entry; every preset is opt-in.
- An FFI program is a closed term, a Moore machine state (section "Terms"), and how it runs is the configured entry's,
  so that a type once recognised costs no encoding and the call can compile with the Gezi code around it. The Jupyter
  kernel only injects the JVM service (`gezi.hotspot.ForeignService`, in the execution's dependencies, as the cache
  service is) and calls `Entry.interacted`. An entry's data selects the executor module `contest-modules-moore`, which
  reads `x ∥ moore_state_type` at the JIT's decode point with no normal form, calls the service, and applies each
  reply, a native value (a bit tuple is a JVM value, `gezi.jit.JvmBits`), to the transition it kept unread; an executor
  that runs no FFI program has no answer for one. A choice is read as lanes: the states of a round are read together
  and their calls go to the service in one batch, and choices in different argument positions multiply.
  The kernel reads no term by an evaluator of its own, its value members shown by the entry as well.
- A new option or policy (an evaluation mode, a cache or table policy) enters as an entry-data constructor with its
  default in `Defaults`, never as a CLI flag, a hard-coded mode or an unconditional call in an adapter. An adapter runs
  a cell only through its entry and calls no `WeakHead`, `Mode` or `ReadingState` itself; the judge's reference reading,
  the tabled weak head, is the one exception. The `conventions` project checks `contest-runner` and `jupyter-kernel`
  (`AdapterRoutesThroughEntryTest`), and each place that breaks the rule today carries a FIXME.
- A design of a change states its position on this line: the call path from an adapter through `Entry` and `Executor`
  to the code it changes, and the configuration point that selects it.

## Terms

- **Definition 14**, **⊑_O**, **≃_O**: the contextual preorder of M. Dezani-Ciancaglini, U. de'Liguoro and A. Piperno
  (1996), their Definition 14, the meaning of every term. M ⊑_O N when for every context C[ ], C[M] solvable implies
  C[N] solvable; ≃_O is its symmetric part. A term is solvable when every head reduction sequence from it is finite.
  Head reduction only defines what a context observes; it is not an operational semantics an implementation must follow.
- **choice** `M + N` and **parallel** `M ∥ N`: the two binary operators of the calculus beside λ and application,
  primitives whose meaning is ⊑_O's. A set is the intuition of the choice, as a mathematical function is the intuition
  of a lambda term, not its definition. In a lambdalattice file `+` and `∥` share one precedence and associate to the
  left, and the text `c + b + a` is the IR's `Choice(a, Choice(b, c))`. A parallel filter is `x ∥ T`, T a term that
  stands for a type.
- **`top`** and **Ω**: `top`, the closed term Y (λz. λx. z ∥ x), is one spelling of the top of ⊑_O, "no answer";
  Ω = (λx. x x) (λx. x x) is its bottom, which a variable of the object language names `bottom`.
- **⊢_{λ-lattice-unit-η}**, the derivability of the paper proofs and of the lemmas: E ⊢_{λ-lattice-unit-η} M = N when
  M = N is in the least congruence (an equivalence closed under every constructor) that contains the equations E, the
  β rule, the **η rule** λx. M x = M (x not free in M) and the ten equations below, whose numbers are their names. The
  β rule with the equations other than (7) are the **λ-lattice laws**, Definition 51 of M. Dezani-Ciancaglini et al.
  (1996) written as equations; (7) is the **unit law** of the empty choice `{}`, which the proofs and the Lean
  formalization still use and the language's terms no longer contain (they write `top`). The axioms are the β rule,
  the η rule, (3), (5), (7) and (10); the other six follow. A subscript names the groups a statement uses (⊢_{βη},
  ⊢_{λ-lattice-η}). It is a proof tool, not the meaning: every equation it derives holds up to ≃_O, so a lemma it
  derives is sound by Definition 14 and is called a theorem of λ-lattice-unit-η.

  ```
  M + N = N + M                 (1)      M + (M ∥ N) = M               (6)
  (M + N) + P = M + (N + P)     (2)      {} + M = M                    (7)
  M ∥ N = N ∥ M                 (3)      (M + N) P = M P + N P         (8)
  (M ∥ N) ∥ P = M ∥ (N ∥ P)     (4)      (M ∥ N) P = M P ∥ N P         (9)
  M ∥ (M + N) = M               (5)      M A + M (A + B) = M (A + B)   (10)
  ```
- **variable arguments**: a literal, written in CBOR diagnostic notation (`42`, `"prelude"`, `h'00ff'`), is passed as
  the bits of its CBOR encoding, each byte eight Scott booleans, each an argument of an application. A **variable
  arguments partial function** `λL. M`, L a literal, takes those bits one by one, answering `top` at the first that
  differs; a choice of them maps keys to values.
- **module system**: a directory and a file are classes, mixins with a self, and a tree of directories is one term, a
  mixin tree. Self-application `omega` (`λmixin. mixin mixin`) is `new`. A file's content is a Scott tuple of its public
  members, `λexport. … export M1 … Mn`.
- **URI node**: a node of the IR named by an absolute URI, equal to the closed term the front end reads from what the
  URI locates; the evaluator expands it, and no strategy, backend or lemma looks at its URI.
- **Moore machine state**: what an FFI program is, a closed term `λk. k output transition`; the output is what the
  state asks the FFI to do, and the transition takes an input symbol to the next state.
- **specialization**: a function's untyped version and its typed versions overlapped, `f + typed_f`; the backend may
  drop the untyped version or run it as a fallback.

## Design principles

### What Gezi is

- **Semantics.** A term means what Definition 14 says. Every executor (the tabled weak-head reader `weakhead`, the
  e-graph's saturation and extraction `saturation` and `strategies`, the JIT `jit`) is a sound approximation of it, and
  each may lose answers and never adds one. Several such approximations, configured differently, are different
  operational semantics of one meaning.
- **The default semantics.** It is a sound approximation of Definition 14, weak-head a sound approximation of it, and
  eager of weak-head. It goes beyond weak-head by computing what weak-head cannot, such as a depth-first search on an
  infinite graph turned into a breadth-first one that halts, so it needs speculation, fallback, profiling and hotspot
  optimisation, since no single simple optimisation is better everywhere. Keep the simplest option among those you make
  configurable, and state what holds only under your component as a property of that approximation, with its
  conditions, never as what a program means: how often a reader runs a call is not how often the program calls it, and
  no caller clears every table at a fixed threshold unconditionally.
- **Purity.** The object language has no mutation, so a program cannot write an explicit cache; the host's automatic
  tabling may turn into one (section "Tables" below).
- **Interface.** The standard library meets the host (Scala) only through `lemma`, `native` and `combinator_property`
  over library files reached by paths. There is no `define`. Type information lives only in the term, as assertion
  combinators; the host holds no type and no rule.
- **Text.** The grammar is the Scaladoc of `gezi-frontend/shared/src/main/scala/gezi/frontend/Lambdalattice.scala`: no `=`, not
  even in pseudo-code, no free name, and `null` is a keyword only inside a literal. Read real files
  (`corpora/library/prelude/`) and the layout rules below before writing lambdalattice text, and write none you have
  not checked against the reader; `README.md`, "Getting started", says how.

### Types live only in the term

- Every type fact about a node is an object-language assertion (an `assert_T` combinator, a contract) written in the
  term, at that node. It survives inlining because the assertion is a noinline attractor: a term the evaluator does not
  unfold, restored by reverse β where its unfolded shape appears. A noinline function need not be in normal form.
- The host holds no type information: no membership or type checker, no `Map` or field from an identifier or a handle
  to a type, no signature used to type a node, no guessing among candidate types, no memo of established memberships.
- The host may read syntax and content addresses, and may decode a value whose term carries an assertion in order to
  run a native implementation. A strategy may remember costs only (budgets, evaluator steps, give-ups), never types,
  and never names a lemma or a combinator. Search metadata is a `combinator_property` of a library file, the raw
  material a strategy computes its order from, never a property of a lemma; a property may be a fact of a backend
  (big integers, first-order constructors), and backend facts come in sets, one per backend. An intermediate
  proposition that guides a search is itself a lemma, which attracts the search to it.
- Every step of HM's inference, the hypothesis included, is encoded as combinators and `lemma` declarations; the host
  chooses which lemma instance to add where and nothing more. Ask of each phase of a pass "which typing rule is this?":
  if the answer is a rule of the type system, the pass is in the wrong place.
- Everything but the front end works on the IR, whose layers are `thunk` (a closure is a thunk with holes and no code
  of its own), `apply`, `choice` and `parallel`, with the URI node beside them; there is no layer of records, no empty
  choice, no knot and no fixpoint layer (`fixpoint` is an ordinary library file). After the front end no module, index,
  e-graph node, lemma statement, trace line or extracted view is a de Bruijn tree. Every term is interned in one weak
  pool, and a layer's identity is its handle there; a content hash serves only as the key of an external cache service.
- Free variables are rejected: the front end treats a free name as an error by default (`FreeNames.Rejected`), and
  allows one only where a call names `FreeNames.Allowed`. A name is bound by the context its text is read in: a file of
  a directory tree is never read alone, and a text read with no context is a closed term. The neutral value a reader
  puts in place of a binder it opens (`gezi.weakhead.Value.Neutral`) is a free variable too, used only where its
  declaration argues the exception.

### Ordinary programs compile as a native typed compiler compiles them

- On problems written in a cooperative sublanguage, deterministic type checking by term rewriting suffices, with no
  search; HM alone covers the programs within it, and more lemmas reach programs beyond HM.
- Programs within HM use native representations everywhere, and compile whole-block: no dispatch, no Scott encoding or
  decoding midway. Only a program HM cannot fully check may decode midway. Dispatch is the worst evaluation and is kept
  for the strangest programs.
- HM's checking is greedy and linear: a program HM checks runs in linear time, and no budget is ever triggered by one.
  Budget control is for programs beyond HM only.

### Several types or encodings are options, never a cost

- A term may have several types: hash consing makes `zero`, `true` and `nil` one term, which is checked as every type it
  supports at once. Where recovering one HM typing is hard, several are kept.
- If a program checks as several native types, any native encoding may run it; if a fragment checks as several but the
  whole program fixes one, the program uses that one. Several efficient native encodings are not a conflict: type
  checking looks for at least one, and several never run slower than one, the backend choosing the fastest.
- A program HM rejects because it has several feasible types is not rejected here; only one with none is.
- Every big integer could be encoded as a singly linked natural number, which is slower; a value that is a natural
  number by structure, but not recognisable by name, still gets the big integer.

### Structure only: no names, and every function a pure function of the term

- The backend never chooses a representation by a type's name; everything is a pure function of structure.
- Untyped `true` and untyped `zero` in the Scott encoding are the same term; type-filtered `true` and type-filtered
  `zero` differ only in the backend's representation.
- Every function is a pure function of the term, so type checking at JIT time and ahead of it are the same: bottom up,
  never top down. A greedy algorithm needs no global order, only an order among the nodes one hop from the newest.
- One e-graph supports several applications at every node; the depth and breadth of the search are tuned by how
  aggressively it prunes, not by giving each application its own graph.

### Soundness, monotonicity, modularity, budgets

- Every transformation is sound by Definition 14: each rewrite L = R has Lσ ≃_O Rσ. No degradation is allowed. The
  meaning forbids false positives, not false negatives.
- Monotonicity in knowledge: adding knowledge (lemmas, modules, typed versions, native representations) only adds
  results or slows down within a bounded factor, never loses a result found before; missing some knowledge (a type with
  no native representation) only slows down, never errs, and never hides a typed version.
- Saturation and extraction are modular: adding a module has no catastrophic effect, and the greedy extraction a
  baseline uses can be replaced by another configuration as a module. The framework never depends on the baseline or
  on an entry (section "The framework", checked by `conventions`' `FrameworkBoundaryTest`).
- A complete framework adds budgets and extensibility, and its saturation and extraction end within budget and search a
  reasonable range.

### Efficiency by design, with native structures

- Time complexity matters, not space: prefer pure functions and tabling, and treat memory as cheap. Small limits remain
  a debugging instrument: a limit hit is explained before anything else, and when the explanation is the expected space
  of tables or of pure, shared terms, that read's limit is raised to what was measured, with the measurement at the
  site.
- No operation has a higher complexity than classic HM's, and nothing is written slow first to be made fast later; the
  requirement is complexity, not a constant factor.
- The JVM's JIT reaches C's speed, so any data structure can be written in Scala.
- Native performance needs native data structures and the λ-lattice's own features to encode types, not extra
  combinators; a synthesized combinator such as `compose` is a red flag. A combinator marks a λ, as a decorator marks a
  Python function; the structure stays λ.
- Big integers and first-order constructors are facts of the backend, kept in `combinator_property`, not operational
  properties; an operational property is added only where it cannot yet be avoided.
- Native types are typed only where the configured backend represents them: a backend and the native typing of the
  types it supports are one preset of the module system (`corpora/compiler/prolog_backend_preset.lambdalattice`), which
  a configuration enables whole, and no configuration enables a native typing without its backend.
- An operation a native data structure supports runs as that native operation, on its native data: it is never done
  by spelling the structure out as storage-free IR, operating on the IR and building the structure again. Only an
  operation the structure does not support reads it as IR, and then one layer at a time, as the operation asks for
  each layer (a reader eliminating a storage reads its one-layer view, and a field it meets is again a storage).
- Reading a storage's view recursively is forbidden everywhere but in the formatters: no code walks, copies or writes
  out a storage by reading its view and then its children's views. What a walk needs from a storage, the storage
  answers from its own data (the terms it holds, its constructor, its fields). Computing a program's normal forms leaves
  a storage in place: IR that holds storages represents the same terms, so a normal form may have storages as its
  leaves, and only the terms a storage holds as written are read further. A formatter, which writes a term as text for a reader outside the program
  (`frontend`'s `ReadableText`, and the writer of OpenTheory articles for the proof checker), may read each storage's
  view and its fields' views as it writes, building no IR from them.
- A storage's view is one layer of native-free IR (IR holding no storage at that layer): `C f1 … fk ∥ T`, its fields
  still storages or the terms the storage holds. No API gives a term's native-free IR deeper than that one layer; the
  formatter's recursion over views is its own, private to it.

### Tables

A table keyed by a term's identity (a handle, a code, a compilation unit), whether it is called a cache, a memo, a side
table or a field of a state value, holds only:

1. costs: budgets, evaluator steps spent, give-ups;
2. the memo of a pure function that the host is allowed to compute anyway, reading only the term's syntax, content
   addresses and backend facts (`combinator_property`): a handle's layer, the backend representation a criterion's
   syntax names, a compiled artifact keyed by its unit and the compiler's configuration. The key holds every input of
   the function. Rewriting by lemma instances is such a function: a term the host computes by adding lemma instances and
   extracting, equal to its input, its assertions in the term, such as the refined output of a test under a schedule
   (`jit`'s `DispatchCache`), keyed by the input, the schedule with its budgets and the refinement, and valid for one
   library.

Two checks decide a table:

- Clearing: emptying a table changes only cost (time, and the steps a reading spends), never an answer. A table of the
  second kind saves steps, so a budget may reach fewer results without it; every result found with or without it is a
  result of the term, and a reading that finishes both ways finds the same results. Emptying a table of costs may change
  a strategy's choices, and so which results a budget finds, never whether a result is sound.
- Source: could the host compute the entry without the table, by reading syntax? If computing it needs a judgment about
  what a value is (a type, a membership, a lemma's premise discharged, a guess among candidates), it is neither stored
  nor computed in the host: it is written in the term, an assertion node derived by lemma instances in the e-graph.

Anti-patterns:

- a record of a type or a membership keyed by a handle, a judgment about a value kept beside the term, however it was
  computed; a term the type check outputs, its assertions in the term, is not one;
- a record that lemma L held at class c, read later as a premise (a deduplication memo kept for termination, with no
  type in its key or value, is a cost);
- a key that leaves out an input, such as a compiled artifact keyed by its unit alone when it depends on the schedule
  and the refinement;
- an answer read within a budget (normal forms) cached as if it were a pure function of the term: it depends on the
  budget;
- a flag beside an e-graph class or an interner entry ("this class is typed"), a fact outside the term hidden next to it.

The architecture extends behaviour (executors, compilers, strategies, backends) by composition, as the module graph
below draws it, and extends derived data by such tables; it does not use the cake pattern.

A memo table is consulted at the call, never wrapped into a function value: no API returns a memoized function
(`memo(f): Key => Value`), and no code stores one. Each use names the table, the key and the computation at the call
site (`memo(f, a)`), so the table and every input of the key are visible where the result is used, and the JIT sees a
direct call instead of a function value called from many sites. A memoized function value is thread-unsafe without
showing it, and unfriendly to the JVM's inliner. The cache service follows Rust's lock: a caller first acquires the
table's lock, a thread-unsafe guard, and then calls `getOrElseUpdate(key, value)` on the guard as often as it likes; no
signature takes the computation as a function to memoize. The custom wart `NoThreadConfinedCapture` (project `warts`)
forbids a thread-unsafe value, one of a type extending `gezi.hotspot.ThreadConfined`, inside any closure (a lambda, a
partial application, an eta-expansion, an anonymous class, a by-name argument) that it is not defined in, except an
argument of an `inline` method, which is inlined at the call.

### Dogfooding, and what work is weighed by

- Intermediate state and the compiler's configuration are encoded in the object language and read by the same
  interpreter, so the interpreter's time complexity has no evident defect, while a constant factor (a hundred times
  slower than C) is tolerable.
- Eager execution at native speed is kept: a change that slows it needs a gain that outweighs it.
- For compute-intensive hotspots the yardstick is the optimal Java bytecode for the same algorithm-contest problem,
  written by its definition: the aim is to cover whole datasets of such problems, recognising each definition by
  lemmas and replacing it by the best known algorithm, at least for the common algorithms.
- Gezi interoperates with ecosystems, the JVM included, through an FFI based on continuation passing: a call to a
  service, with no proof obligation about the service. A `native` is different: a synchronous interface whose meaning
  must equal the IR the compiler transforms, an equality not yet proved mechanically.

So when a change adds intermediate state or configuration, ask whether it can be a term read by the interpreter; when a
change touches the interpreter, ask whether its time complexity has an evident defect.

### Compilation and analysis are λ-calculus rewriting

1. The whole of compilation, optimisation and analysis is λ-calculus rewriting: β, η, the Cartesian product and lemmas.
2. Analysis is written as rewriting rules, a lemma library and attractors, not as analysis code in the host.
3. This was impossible before because the object language could not encode a type system; under Definition 14 the
   object language's assertions can.
4. A negative conclusion is encoded as an attractor's guard.
5. An induction lemma is encoded as a combinator of a particular shape, found by equations.
6. Statistics about an island are themselves λ-terms, kept from inlining by attractors. A function's domain can be
   written as `if parameter is valid then do something else top`; the domain then needs a proof or a case analysis by
   specialization, and the specialization keeps that information.
7. Once the combinators and the types are recognised, the island compiles whole-block and runs fast; recognising the
   combinators of known problems is always possible with attractors made for them. Hotspots do not yet reach the
   yardstick of the section above.
8. An input may be any shape of set overlaid; where the input must be a binary natural, a guard can copy it into a trie
   of binary naturals.

### HM exactly, saturation in rounds, the domain checked at run time

Three conflicts are not looked at in isolation (a dispatch's domain check that may not end, a typed version with no
native representation, a new module starving HM's steps):

- The end-to-end goal: HM's type inference carried out by stepwise rewrites that keep the meaning by Definition 14 (each
  step ≃_O), its trace exported to Lean and checked there with the lemmas implemented in Lean.
- HM exactly: with only HM's lemmas enabled, the e-graph simulates HM deterministically; with a given rule set and a
  budget of one, it is the greedy HM. Other lemmas solve problems HM cannot, at the risk of slowing down.
- Saturation's extensibility: the rule sets the meaning admits are unbounded, so saturation cannot run to a fixed point
  blindly; guided equality saturation, backoff schedulers and sketches that configure which combinators each phase
  looks for are the prior work. The search space grows linearly under HM alone and exponentially with more options; a
  search prunes aggressively and stays within a constant factor of the deterministic HM at equal depth.
- Saturation in rounds, each round with its own strategy, on one e-graph (`strategies`' `Schedule`,
  `FixpointSearch.sharedGraph`).
- The domain checked at run time: falling back is a switch at compile time; at run time a typed version runs where its
  input is proved in its domain, the untyped one (a fallback) or an error (strict) otherwise. Whether an input is Scott
  data is never marked outside the object language. The check should be fast (a simple run of HM); its termination is
  later work. No count of its own decides a check's answer: a check runs to its conclusion or is cut by the reading's
  budget, which stops the whole reading.

## The code

### The code is 100% immutable

- No `var`; no `scala.collection.mutable`; no mutable `java.util` or `java.util.concurrent` collection, atomic,
  `ThreadLocal`, `StringBuilder`, builder, `Iterator` or loop; no `Array` (an immutable array is `IArray`).
- No `Var` of Binding.scala, although it is a library's; each use is an exception argued at its site.
- `lazy val` is allowed: it is written once.
- A cache or a state is a value, passed as an argument and returned as a result; nothing is kept between calls except
  through values.
- The implementations of the JVM and of the libraries are not under the rule; only the code of this repository is.
- WartRemover (`build.sbt`, `wartremoverErrors`) checks the sources of every module, tests included, on every compile;
  `conventions/src/test/scala/gezi/conventions/WartSuppressionTest.scala` checks that every suppression carries the
  quoted justification of its exception.
- JVM bytecode is the JIT's target, generated with `java.lang.classfile`, which any module may use.
- Exceptions, each at its sites with `@SuppressWarnings` for the wart it breaks and the justification quoted:
  - the classfile builders: `java.lang.classfile` is driven by mutable builders, used only inside the call that turns
    one program into a defined class; nothing it builds is kept but the class or its instance;
  - the JMH protocol: a `@Param` field, which JMH assigns, is a `var`, as in
    `jmh-pipeline/src/main/scala/gezi/jmh/pipeline/KnowledgeReadingBenchmark.scala`;
  - the local mutable exceptions of hotspot compilation: a cache provider adapts to a mutable store underneath, and the
    fork and join primitive confines the JDK's virtual thread executor to one call. Each site names its framework and
    monitor, under the synchronized convention in the Scaladoc of the package `gezi.hotspot`: the map of
    `hotspot-baselines`' `ConcurrentMapCacheProvider` and the executor of `hotspot`'s `Forks`;
  - arrays exchanged with an external library: where a library's interface takes an `Array` the code must make, such as
    the `Array[Byte]` of borer's `Dom.ByteArrayElem`, the array is made at that site and passed to the library, and the
    code's own data stays `IArray` (`frontend`'s `DiagnosticNotation.hexadecimalBytes`);
  - the executor of `FailFastSuite` (section "Tests fail fast").
- Exception without a wart, since it is generated bytecode and no Scala source: the kernels of the JVM array group
  backend (`gezi.narrowblocks.groups.JvmArrayKernels`) allocate an `int[]` or a `long[]` and write it in a counting
  loop, the most efficient structure and one HotSpot's C2 vectorizes: cell by cell, by increments at the cells its
  input names (a histogram), or by `java.util.Arrays.sort` in place on its own copy of the input. A kernel writes only
  the array it allocated, before it returns it; the Scala code holds the result as an `IArray` and never writes it.

### The module graph

`build.sbt` draws it, and a module depends on nothing else:

| Module | Depends on | Holds |
|---|---|---|
| `ir` | nothing | instructions and codes interned by content (global weak interners), holes, patterns |
| `orientation` | `ir` | the orientations of lemmas and what is computed from them alone |
| `egraph` | `ir` | the persistent e-graph: nodes, classes, union-find, heads, closure states, agenda, counts; `GraphView` |
| `ematching` | `ir`, `egraph` | THE BACKEND INTERFACE: programs as first-order data, `Backend`, `CompiledProgram` |
| `ematching-indexing` | `ematching`, `orientation` | the compiler of orientations and codes into a program (the inverted index) |
| `ematching-interpretation` | `ematching` | a backend: the program's steps and buildings walked at every call |
| `ematching-closures` | `ematching` | a backend: a program compiled once into a tree of Scala closures |
| `ematching-bytecode` | `ematching` | a backend: a program compiled once into a hidden class generated with `java.lang.classfile` |
| `saturation` | `ematching` | the fixed-point loop over a compiled program; no backend and no fixture |
| `extraction` | `egraph`, `saturation` (for `StopSignal`) | the greedy extraction of a graph's best entries by a cost model, and their spellings |
| `backendcomparison` | `ematching-indexing`, `saturation`, `ematching-interpretation`, `ematching-closures`, `ematching-bytecode` | the backends by name (`Backends`), a run's input compiled by one of them (`RunInput`, `Compiled`), the form of a fixed point (`FixedPoint`); its tests check that the backends agree |
| `narrow-blocks` | `jit`, `strategies`, `frontend`, `standardlibrary`, `lemma-encoding-baseline`, `hotspot` | the narrow back end: the narrow grammar's check, its bytecode compilation, the lemma route, and the compiler of a program unit by the lemma rounds (`ProgramCompiler`) |
| `provenance` | `egraph`, `locations` | the locations of an e-graph's nodes, computed from its union log, the inputs' source maps and the lemmas' sides; outside the framework |
| `migration` | `frontend`, `directory-sugar`, `knowledge-reading`, `provenance`, `saturation`, `ematching-indexing`, `ematching-closures` | migrations of lambdalattice texts checked by reading them again: parentheses removed on the reader's spans, a lemma's instances rewritten where the e-graph's matching finds them and the formatter of a tree's files read in their scope, the conversion of a file's export to its first binder `export`; outside the framework |
| `locations` | `ir` | source locations for people and tools, never for a choice: spans, locations, the source map of an occurrence |
| `conventions` | nothing (tests only) | the checks of this file's rules |
| `generatedinputs` | nothing (test support) | properties checked by Hedgehog in munit suites, seeded samples and snapshots, state machine tests; a module's own generators are in its test sources, package `gezi.generatedinputs` |

A backend is one more module that depends on `ematching` alone and is named in `backendcomparison`'s `Backends`; adding
one changes no other module. The backends the interface is designed for are interpretation, closure compilation, TASTy
(quoted code compiled at run time by scala3-staging) and Java bytecode (class files made with `java.lang.classfile` and
loaded as hidden classes); all but TASTy are implemented.

### Knowledge comes in as data

The code names no type, lemma, combinator or definition. Lemmas enter only as their sides, patterns over instructions,
from which the `orientation` module compiles the orientations; definitions only as instructions; and the noinline
property only as a set of instructions. A test's inputs are generated, generic (no Gezi data), and a test is a property,
a state machine or a seeded snapshot (section "Tests"); tests written before those rules may keep their hand-written
inputs until a later pass.

### Configuration and data files are lambdalattice, or a framework's own format

Every configuration or data file the project reads is either a lambdalattice file, read by the project's own front end
(dogfooding), or a file in the format of a framework the project already uses (sbt, Nix, Lean's lakefile, munit and
snapshot4s snapshots), read by that framework. A new ad hoc format, with a parser of its own, is added only where neither
can express the data, and the reason is written at the site. The exchange format of terms (the judge's points file and
pipe, the problem corpora's references) is one line of lambda-lattice text, `frontend`'s `ExchangeText`: the IR written
by the printer (`ReadableText.printedNameless`), each repeated closed instruction bound once, inside
`λstart. start (λk. k N) (TERM)`, N the number of the printer's bindings, so that a line is written and read at the size
of the IR's graph. The line of no normal form is the format's own `{}`, which is no term of the language
(`ExchangeText.noNormalFormLine`).

### lambdalattice coding conventions: static features before dynamic ones

- An algebraic data type, a record included, is written in a lambdalattice file in the Scott encoding: a constructor is
  a function of its fields that hands them to the matching branch, and a value is read by position.
- A record or an ADT is not written as a variable arguments partial function keyed by labels, nor as a CBOR map literal.
- Variable arguments partial functions encode directories and file names, the module system's mixin tree, and nothing
  else.
- In short, a static feature (a constructor, a position) comes before a dynamic one (a key looked up at run time).
- Exception, the FFI's method symbols: a computation graph names a Java method by its owner, name and descriptor, CBOR
  diagnostic notation string literals the host reads to find the method. Which Java method runs is chosen by these
  strings, and a misspelled symbol is found only when the call runs. It covers the symbols of a computation graph and
  nothing else.
- Exception, natives and codecs: a knowledge file names a native's implementation (the `natives` slot,
  `λk. k "wren_binary_plus"`) and a representation's codec (the `representations` slot, `λk. k "big_integer"`) by a string
  literal in CBOR diagnostic notation, which the host decodes and looks up in `NativeBackend`. A Scott list does not
  serve: the implementations and codecs are an open set (`NativesProvider.loaded` from the classpath,
  `NativeBackend.extended`), a published Scott list a closed one, and lists of one width cannot be told apart by
  structure. Which Scala code a bound library term runs is thus chosen by the value of that string, checked by the
  backend's look-up. The exception covers these two slots and nothing else; every other option or property stays a
  Scott ADT.
- The conventions govern the library, the configuration files, the schema files and every other lambdalattice file the
  project writes, but not problems: a problem may be written against them on purpose, to test the spellings they do not
  adopt.

### lambdalattice files export through their first binder `export`

A file's content is the Scott tuple of its public members written as an abstraction of the whole file: its first binder
is `export`, the imports and local definitions stand under it, and the last step of the spine hands the members to
`export`:

```
λ export
. (λtuple. tuple λmixin. mixin mixin)
λ omega
. omega (omega (omega (omega corpora "library") "prelude") "fixpoint")
λ fixpoint
. …
λ boolean_list
. export list binary_list boolean_list
```

A file that is its tuple alone is `λexport. export M`. A local definition stays an inline tuple, `(λtuple. tuple V)
λx.`, and an import is unchanged, `omega (omega … "file") λa b c.`: the file's instance applied to the importer's
continuation hands it the members, as the tuple at the end of the spine did. `migration`'s `ExportBinderConversion`
converted the tree's files from that older form.

Several related functions in one file are a positional tuple, closed: a set that may grow is grouped as well, its file
closed and a new file added for what comes later. A group holds about seven fields, a design guideline and not a hard
limit.

### lambdalattice layout: no right-associative parentheses, CPS one step per line

The rules below govern every lambdalattice text, written by hand or by a printer, and the files of the tree are formatted
to them by `migration`'s `LambdalatticeFormatting`, which reads a file into the IR with its source map and writes it back
(`frontend`'s `SourceFormatting`), keeping its names, literals, sharing, comments and blank lines, and its line breaks
where the rules allow one. The tools support several options. The reader ignores whitespace, so none of the layout rules
changes what a text means.

- **No right-associative parentheses.** The last argument of an application is never parenthesized: an atom (a name, a
  literal) is written as it is, an abstraction as `f λx. M`, and an application after `λ.` (the binder of no name,
  Haskell's `$`), so `foo (bar (baz qux))` is `foo λ. bar λ. baz qux`. A right spine is parenthesized only as a whole,
  where it stands in function position or has arguments after it.
- **Adjacent binders are merged, and `λ.` is written only where needed**: `λf. oo λ. (λb. λa. λr. λ. (baz λ. qux))` is
  written `λf. oo λb a r. baz qux`.
- **`+` and `∥` share one precedence, mix in one chain, and associate to the left**, as `+` and `-` do in arithmetic,
  so `foo + bar ∥ baz` is `(foo + bar) ∥ baz` and a chain needs no parentheses of its own. The text `x + y` is the IR's
  `Choice(y, x)`.
- **Abstraction and application bind tighter than `+` and `∥`** (Dezani-Ciancaglini, de'Liguoro and Piperno's
  convention; `frontend`'s `Lambdalattice`, PRECEDENCE). So an abstraction stands bare as an operand,
  `λx. a + λy. b` being `(λx. a) + (λy. b)`, and the body of an abstraction is parenthesized exactly when it is a chain,
  `λx. (a + b)`; no other body is parenthesized. A compound argument that is not the last one is parenthesized as well,
  `f (g x) y`.
- **Single-line examples.** Fully parenthesized, the term
  `λf. λx. f x (g 42 (λa. λb. a)) (λy. λ"k". λw. ((y w (g 42 (λa. λb. a))) + (λz. z) ∥ x))` is written
  `λf x. f x (g 42 λa b. a) λy "k" w. (y w (g 42 λa b. a) + λz. z ∥ x)`: the last arguments `λa. λb. a` and
  `λy. …` lose their parentheses and merge their binders, the argument `g 42 …` before the last keeps its parentheses,
  and the body of `λy "k" w.` is a chain, so it is parenthesized, its operands `y w (g 42 λa b. a)`, `λz. z` and `x`
  needing none. The printer lifts the repeated `g 42 λa b. a` into a binding written as a library import:
  `(λt. t λ. g 42 λa b. a) λ$merkle$89abcdef f x. f x $merkle$89abcdef λy "k" w. (y w $merkle$89abcdef + λz. z ∥ x)`.
- **Names follow Scala's alphanumeric identifier rules**, a character a name cannot hold escaped with `$` as
  `frontend`'s `NameSpelling` does (`string_a$u002Eb_digit_5`); a name is never put in backquotes, which CBOR's
  diagnostic notation uses for strings.
- **A single line writes `λx. body`.** A text that spans lines is written in the multi-line CPS layout:
  - along the right spine, expressions and parameter lists alternate, one per line, hand-written and generated text
    alike;
  - a parameter list's `.` begins the next line, so a line that begins with `.` begins the body of an abstraction;
  - `λ.` is a line holding `λ` alone, the next line beginning with `.`;
  - siblings have the same indent: along a right spine its expressions and parameter lists, in an expression its
    curried head and arguments, in a chain its first operand and each operator with its operand.

  Four more rules:
  1. a right spine on lines always begins with a parameter list: one that begins with an expression gets a first line
     holding `λ` alone, the expression following after `.` on the next line;
  2. the markers `λ` and `.` stand in the column of their block, followed by one space, the content starting two
     columns in. A block is a pair of parentheses whose contents span lines, whose column is two in from its `(`, or
     the whole text, whose column is the first. So a `λ` stays on the line of the `(` before it, and the lines of the
     spine it begins line up under it;
  3. a text that is a right spine on lines has no parentheses around it; any other text on lines is wrapped in
     parentheses;
  4. a chain keeps its layout: `+` and `∥` begin lines in the column of the chain's `(`, as its `)` does, each followed
     by one space, the operand two columns in, and a first operand that is an expression writes `( operand`:

    ```
    . ( λs. s binary_minimum λk. k "wren_binary_minimum"
      + λs. s binary_maximum λk. k "wren_binary_maximum"
      + λs. s merge_binary_plus λk. k "wren_binary_plus"
      )
    ```

  The single-line example above with its shared binding, laid out on lines:

  ```
  λ
  . (λt. t λ. g 42 λa b. a)
  λ $merkle$89abcdef f x
  . f x $merkle$89abcdef
  λ y "k" w
  . (y w $merkle$89abcdef + λz. z ∥ x)
  ```

  The same with its chain on lines too:

  ```
  λ
  . (λt. t λ. g 42 λa b. a)
  λ $merkle$89abcdef f x
  . f x $merkle$89abcdef
  λ y "k" w
  . ( y w $merkle$89abcdef
    + λz. z
    ∥ x
    )
  ```

  Two more examples, the second with a multi-line abstraction as an argument:

  ```
  λ
  . read_line f
  λ line
  . parse line
  λ number "k"
  . log number
  λ
  . done number
  ```

  ```
  λ
  . fixpoint
  λ eval environment expression
  . expression
    (λname. lookup environment name)
    ( λ function argument
      . apply (eval environment function)
      λ
      . eval environment argument
    )
  λ parameter body
  . closure environment parameter body
  ```

`frontend`'s `LambdalatticeLayout`, which the formatter (`SourceFormatting`) calls, lays text out this way with
`ParameterLists.Prefixed`, keeping the author's line breaks where the rules allow one and setting the columns;
`ParameterLists.Inline` keeps the single-line rules alone, and the existing callers use it. The last four examples above
are its snapshot (`layout/prefixed-examples.txt`).

The printer writes in this layout (`frontend`'s `ReadableText.Printed.laidOut`): it breaks a spine, a chain or a
parenthesized argument wider than the width where the layout allows a break and leaves the columns to
`LambdalatticeLayout`. The start text of a trace (`rewrite-trace`'s `TraceStart`) is written this way at
`ReadableText.lineWidth`.

### Naming

Every identifier, in every language of this repository, is spelled in complete English words: no abbreviation,
truncation or invented shorthand (`position`, not `pos`; `index`, not `idx`), however the paper writes its metavariable.

## The framework

The framework is the projects `ir`, `orientation`, `egraph`, `ematching`, `ematching-indexing`,
`ematching-interpretation`, `ematching-closures`, `ematching-bytecode`, `saturation`, `extraction`, `backendcomparison`
and `generatedinputs`: an e-graph saturated to one least fixed point over the defunctionalized IR of the λ-lattice
(layers `apply`, `parallel`, `choice`, `thunk`, and noinline leaves), with lemma orientations matched through an
inverted index. Its inputs' digests and the forms of its fixed points on generated program families are snapshots of
`programfamilies`' tests. The e-graph is a search strategy, not an engine, and can be replaced whole; its nodes, unions
and class data are immutable values.

This section is a map of the code base for a reader who wants to understand it from the top down: what the program does
as a whole, then each module in the order a run passes through it, then the support code.

### What a run does

The repository saturates an e-graph over the defunctionalized IR of the λ-lattice. A run starts from instructions (every
term is an interned `Instruction`, the canonical object of its one layer: an application, a parallel, a choice or a
thunk) and a store that names the noinline ones, which the graph keeps as leaves, a set of lemmas given by their two
sides, and some input instructions. It then:

1. compiles the lemmas into orientations, each one a side to match and a side to add;
2. compiles the orientations into a program, the inverted index from the key of a node to the matching steps that start
   from such a node;
3. hands the program to a backend, which turns it into an object that runs it;
4. adds the inputs to an empty e-graph and saturates it: every new node (a delta) is looked up in the index, every match
   adds the other side and unites the two classes, congruence and the β rule add their own unions, until no delta is
   left (a fixed point) or a budget of instances is spent;
5. optionally extracts from the saturated graph a best term for each class under a cost model.

Every data structure is a persistent value: an operation on the e-graph returns the graph after it and leaves the one it
was called on unchanged.

### The directory structure

The root `build.sbt` declares the projects and dependencies, and the comment at its top draws the module graph. A
shared-source JVM/Scala.js project uses `sbt-crossproject`'s default `CrossType.Full` layout:
`<module>/shared/src/{main,test}/scala/`, `<module>/jvm/src/{main,test}/scala/` and
`<module>/js/src/{main,test}/scala/`. Its `jvm/build.sbt` and `js/build.sbt` are symlinks to
`shared/build.sbt`; platform-specific settings go in `jvm/jvm.sbt` or `js/js.sbt`. Other projects use
`<module>/src/main/scala/` and `<module>/src/test/scala/`. The framework's projects:

```
gezi/
├── build.sbt                  the projects and their dependencies
├── project/                   sbt plugins and the sbt version
├── CONTRIBUTING.md            this guide
├── backendcomparison/         the backends by name, a run compiled, the form of a fixed point
├── gezi-orientation/          lemma sides compiled into orientations
├── gezi-ematching-indexing/   orientations compiled into a program (the inverted index)
├── gezi-ematching/            the backend interface: programs as first-order data
├── gezi-ematching-interpretation/ a backend: the program walked at every call
├── gezi-ematching-closures/   a backend: a program compiled into Scala closures
├── gezi-ematching-bytecode/   a backend: a program compiled into a hidden class
├── gezi-saturation/           the fixed-point loop over a compiled program
├── gezi-egraph/               the persistent e-graph
├── gezi-extraction/           the greedy extraction of best terms by a cost model
├── gezi-ir/                   instructions, codes, layers, patterns: the IR's vocabulary
├── generatedinputs/           generated test inputs: properties, snapshots, state machines
└── conventions/               tests that check the rules of this guide over all sources
```

The list runs from the top of the dependency order to the bottom: a module depends only on modules below it in the list,
never on one above.

### The modules, from the top down

#### `backendcomparison`: the backends and the forms of fixed points

Start reading here.

- `RunInput.scala`: `RunInput` (what a run reads: the store, the orientations, the pattern instructions, the inputs and
  the budget) and `Compiled` (its program, indexed and compiled by a backend, closure compilation by default).
- `Backends.scala`: the backends by name. `backendcomparison` is the only module of the framework that depends on the
  concrete backends.
- `FixedPoint.scala`: the form of a fixed point independent of node numbers and union order, so that two runs can be
  compared by what they reached rather than by how.

#### `orientation`: lemmas into orientations

`OrientationCompilation.scala` takes each enabled lemma as `LemmaSides` (its identifier, its number of metavariables,
and its two sides as patterns) and computes its usable orientations, `Orientation` (`Orientation.scala`): which side is
matched, which is added, the subterms the two sides share, and the function metavariables whose applications the β rule
reads. It is the framework's `OrientationCompiler`, `StandardOrientationCompiler`, which a round chooses by its
`orientation_compiler` as it chooses its indexer. `Orientations.scala` holds what is computed from orientations alone,
and `StandardOrder.scala` the order they are sorted in.

#### `ematching-indexing`: orientations into a program

`Indexing.program` compiles the orientations and the codes into a `Program`: for every orientation, `Seeding` writes one
seed per position of its matched side, a sequence of steps that starts from a node at that position and walks out to the
rest of the side; the seeds are filed by their kind and key, which makes the table an inverted index from the shape of a
delta node to the seeds that can start from it. Where the rest of a node's children are determined (instructions, or
metavariables already bound), a seed looks the node up by its signature instead of reading a class's users or members.
It also writes the buildings of the added sides, the shared subterms and the code bodies.

#### `ematching`: the backend interface

`Program.scala` defines the program as immutable first-order data, with no function value in any field: `SeedKind`,
`SeedKey`, `Step`, `Seed`, `Building`, `OrientationPlan`, `Program`. `SeedTree.scala` merges the seeds of one kind and
key into a trie of their steps, so that the steps they begin with in common run once; `Program.trees` is that tree for
every key, and it is what a backend runs. `Backend.scala` defines the interface every backend implements: a `Backend`
turns a whole `Program` into a `CompiledProgram`, which answers the matches of a delta node under a key and builds the
nodes of an added side, a shared subterm or a code body. Every backend must give the same matches in the same order and
build the same nodes in the same order. The interface is designed for four backends (interpretation, closure
compilation, TASTy through scala3-staging, and Java bytecode), of which all but TASTy are implemented; adding one is a
new module that depends on `ematching` alone.

#### `ematching-interpretation`, `ematching-closures`, `ematching-bytecode`: the backends

`Interpretation` keeps the program as it is and walks a key's seed tree and a building's tree at every call; the
registers are an immutable `IArray`, copied on each write.

`ClosureCompilation` compiles each key's seed tree, each node's steps from the last to the first, into nested Scala
closures, so that what each step does is decided once at compile time, and each building into a closure from a graph and
the caller's values to the graph after it and the node built. The registers of a run of a seed are an immutable vector,
written once each.

`BytecodeCompilation` generates one class file for the whole program (`ClassFileGeneration.scala`, the one place
`java.lang.classfile`'s mutable builders are allowed) and defines it as a hidden class implementing `GeneratedProgram`: a
static method per key's seed tree, with the registers in JVM locals, each `Each` step a loop and the branches one after
another, and a static method per building; `GeneratedCodeSupport` makes the Scala values the generated code needs. The
package documentation states the discipline of the generated code.

`backendcomparison/src/test/.../BackendAgreementTest.scala` checks on generated programs that the three backends give the
same runs and the same matchings.

#### `saturation`: the fixed-point loop

`Saturation.run` builds the initial graph from the pattern instructions, adds the inputs, and calls `saturated`, which
works the agenda (pending unions and β steps) and then matches deltas through the `CompiledProgram` until none is left or
the budget is reached. The result is a `Run`: the graph, the node of each input, and the `End`, `FixedPoint` or
`BudgetExhausted` with the number of instances that changed the graph. `saturation` depends on the backend interface and
on no backend.

#### `egraph`: the persistent e-graph

`EGraph.scala` is the largest file and the core data structure: the nodes numbered by creation, the data of each class
kept in its root, the hash-cons table from a layer over class roots to its node, the union-find by size, the agenda, and
the counts. Its methods return the graph after the operation. Around it:

- `GraphView.scala`: the read-only view a compiled program matches against (`Head`, `MemberShape`, the members of a class
  under a shape).
- `GraphBuilding.scala`: the operations a compiled program builds nodes with.
- `Records.scala`: the values the graph stores, among them `ClosureState` (a thunk with the arguments given to it so far)
  and `Justification` (why two classes were united: a lemma instance, congruence, or the β rule).

#### `extraction`: best terms

`CountedExtraction.fixed` computes, for a saturated graph and a `CostModel`, the best entry of each class by a greedy
fixed point; `Extraction.spelled` writes the chosen entries out as terms. `PairingHeap.scala` is the persistent priority
queue the greedy fixed point reads its pending productions from. `extraction` depends on `egraph` alone, not on
saturation.

#### `ir`: the vocabulary of the IR

The bottom of the graph, with no dependency. `Identifiers.scala` defines `Instruction`, an interned term canonical by its
content (`Interned.scala`, one weak pool), the interned `Code` of a thunk's body, and the number `LemmaIdentifier`;
`Constructors.scala` the layers' constructors; `Layers.scala` the layer types (`IrLayer`, `Layer` with its noinline leaf,
`CodeLayer`), the `Hole` of a thunk's binder and the `Store` of noinline instructions; `Pattern.scala` the patterns of a
lemma's sides and the `Direction` an orientation matches. Read this file first if a type in a higher module is
unfamiliar.

### Support code

#### `generatedinputs`: generated test inputs

Every test's inputs are generated (section "Tests"). `generatedinputs` depends on no module, so that the tests of every
module can use it:

- `GeneratedProperties.scala`: properties checked by Hedgehog inside munit suites;
- `SeededSamples.scala` and `SeededSnapshots.scala`: samples drawn from a fixed seed and their outputs recorded as
  snapshots;
- `StateMachine.scala`: state machine tests, commands generated against a model.

A generator of one module's own data lives in that module's test sources, in the package `gezi.generatedinputs` (for
example `gezi-ir/shared/src/test/scala/gezi/generatedinputs/StoreGenerators.scala`), because `generatedinputs` cannot depend on the
modules whose tests depend on it.

#### `conventions`: the rules, checked

`conventions` has tests only. `WartSuppressionTest` reads the sources of every module and fails on a WartRemover
suppression that lacks its quoted justification; the constructs this guide forbids are compile errors under WartRemover.

## Tests

- A test is of one of three kinds, and its inputs are always generated, never hand-written: a property test checks a
  concise law on generated inputs; a state machine test generates a sequence of operations, folds it over the
  implementation and over a simple model, and checks after each step that they agree; a snapshot test records generated
  inputs with their outputs, from a fixed seed. Writing the generator forces you to say what you are testing.
- Every test states its purpose in its Scaladoc, in one sentence: the defect it would catch. Snapshot is the default
  kind; a property or a state machine is written only when its law or its model is much simpler than the implementation.
  Where no concise law exists, do not write the implementation's logic again as a test oracle; record a snapshot.
- A law covers each kind of case it must reach by construction, never by a share of random draws: each kind has a
  generator that yields that kind by construction (a multi-valued case is a choice of at least two members whose answers
  differ by construction), and every iteration checks the law on one sample of each kind; where the construction gives
  the exact outcome, the law asserts it. Hedgehog's `cover` is not used: a percentage of draws under a seed that changes
  from run to run fails now and then and catches nothing.
- Do not assert a value against a literal written in the test: assert it against a snapshot (snapshot4s with munit,
  `assertFileSnapshot` with a descriptive path, or `assertInlineSnapshot`). When a snapshot fails, run
  `sbt snapshot4sPromote`, review the promoted diff, and run the tests again without promoting. No snapshot compares two
  values computed in the same test, or a trivially obvious outcome.

### Tests fail fast

- Every test has a default deadline of a couple of seconds. A test that overruns it fails. munit's own `munitTimeout`
  neither stops nor interrupts a body: on a timeout munit 1.3.6 only fails the test's promise
  (`munit.internal.PlatformCompat.waitAtMost`), and under its default parasitic execution context a synchronous body is
  not even reported until it returns (scalameta/munit#730).
- The test suites handle munit's timeout themselves and cancel the body by portable cooperative cancellation, never
  `Thread.interrupt`: on the timeout the suite requests a stop on a signal the body's computations read
  (`gezi.saturation.StopSignal`), and the CPU-intensive computations check that signal at chosen points. Nothing kills
  the test process behind munit's back.
- Every suite extends `gezi.generatedinputs.FailFastSuite` (project `generatedinputs`, which every project with tests
  depends on at test scope), never `munit.FunSuite`; `FailFastSuiteTest` in `conventions` fails otherwise. Its default
  `munitTimeout` is 3 s (measured over 1191 tests with every body running and every deadline raised to 600 s: median
  0.16 s, 90th percentile 3.17 s, 95th 7.5 s, 99th 38 s; its Scaladoc has the distribution). It runs each body on a
  pooled platform daemon thread and, at the deadline, fails the test with a `TestDeadlineExceeded` and completes the
  test's stop promise. A test written with `stoppableTest(name) { stopped => ... }` gets that promise's read-only future
  and hands `StopSignal.completedWith(stopped)` to the computations it runs. Nothing interrupts a thread. The JVM cannot
  stop a body that reads no signal; it runs on a daemon thread until the forked test JVM exits.
- Exception: the thread pool and the deadline scheduler of `FailFastSuite` are mutable runtime objects; the sites carry
  `@SuppressWarnings` for `NoJavaUtilConcurrent` with their justification, citing scalameta/munit#730.
- Tests are timed without their shared fixtures: a suite lists a value several of its tests share (a compiled library, a
  schedule) in `sharedFixtures`, forced in `beforeAll` under `fixtureTimeout` (15 s, from the slowest measured fixture,
  13.5 s), so that the run order does not decide which test pays for a lazy value shared across suites.
- The suites that exceed the default carry a per-suite `munitTimeout` with its measurement and either a reason
  (end-to-end runs of real JVMs, the Lean toolchain) or a FIXME that the suite is to be made fast.
  `NeverStoppedInTestsTest` lists the test sources that still name `StopSignal.NeverStopped`, each with its reason.
- A longer deadline is an exception, written at the site with its measured time and the reason the test cannot be made
  faster. A slow test is made fast first: smaller generated inputs that still catch the defect the test states, a shared
  fixture, or a narrower subject.
- Small limits are a debugging instrument: never raise a limit before finding why it was hit. If it is a bug, fix it and
  keep the limit; if it is the algorithm's expected cost, raise that one limit to what was measured and write the number
  and its measurement at the site.
- Which tests a change needs, how much memory a run needs and how long a test may run are judged case by case; the
  numbers in this file and at the sites are measurements to judge from, not settings to copy.

### Timings are JMH benchmarks

Every timing of the Scala code is a JMH benchmark run through sbt-jmh in the module `jmh-pipeline`, which holds
benchmarks only: no timing written by hand (`System.nanoTime` and the like around a call). A reading reports JMH's score
and error with its unit, mode, forks, iterations, command, commit, date and load, and the warm-up count is justified from
the warm-up readings. A benchmark returns its result or feeds it to a `Blackhole`. A count (evaluator steps,
instances, matches, table entries, decodings) is a test's expectation only when the test states, before it is run, the
expected value and the part of the design it follows from: a deterministic test on a small generated input, whose
differing reading is a defect or a fault in the design's reasoning, never a reason to change the expectation. A count
with no such derivation is neither a test's expectation nor evidence of a speed-up; a step budget that bounds a run is
control. A change whose effect follows from its design is shown by such a test on one small example from the case it is
for, and no exploratory benchmark is written for it. Only an effect that cannot be derived beforehand, on a complex
program, is shown by timing one small example on which the effect is large, by a short JMH of one fork (allocation per
operation with `-prof gc`, or a short JFR profile, where the mechanism matters). A large change made in several steps
does not prove each step: a step that adds an option nothing selects yet changes no measurement, and the step that
selects it carries the example.

## Building and testing

From this directory, inside the dev shell of the Nix flake, which provides the JDK and sbt:

```bash
direnv exec . env SBT_OPTS='-Xms64m -Xmx2g -Xss4M -XX:ReservedCodeCacheSize=128m -XX:+UseZGC -XX:ZUncommitDelay=60' sbt --client "<project>/Test/compile"
direnv exec . env SBT_OPTS='-Xms64m -Xmx2g -Xss4M -XX:ReservedCodeCacheSize=128m -XX:+UseZGC -XX:ZUncommitDelay=60' sbt --client "<project>/testOnly <suite> <suite>"
```

While working, compile; the type checker and WartRemover's immutability check run at compile time. Run tests only when
a change is ready, and choose them by judging what the change could actually break, not by how much code it touches: a
rename in a class every file depends on touches the whole build and risks almost nothing beyond what compiling checks,
while a one-line change to the extraction's cost model risks every reading that extracts. Run the suites that could catch
such a breakage, and no others. Do not run the whole build's `test`, or a module's `test` out of habit, as a gate.

Every Scaladoc link (`[[...]]`) resolves: `sbt --client docLinks` runs scaladoc over every project's main sources and
fails on each unresolved link in Gezi's sources, named by its file, line and query (`project/DocumentationLinks.scala`;
`<project>/docLinks` checks one project). Scaladoc itself only warns, and `-Werror` does not reach it. Run it after a
change to Scaladoc or to the names it links. A whole run took 265 s on two cores, with the server at `-Xmx3g` under a
5 GB scope that peaked at 4.7 GB, with 90% of sbt's tasks served from its cache (2026-11-21, load 11 to 17). The relative links and
anchors of the Markdown files are checked by `conventions`' `MarkdownLinksTest`.

`sbt --client` keeps one sbt server running, which saves the JVM start-up on every command; stop it with
`sbt --client shutdown`. The server runs the commands and forks the tests, and its CPU set, niceness, cgroup and
`SBT_OPTS` are those of the command that started it: wrapping a later client in `taskset` or `systemd-run` changes
nothing. Shut the server down and start it again under the wrapping you need, and check the server's pid, not the
client's.

The server's JVM options are given where sbt is started, in `SBT_OPTS`, not by the dev shell; they take effect when the
client starts a server, and a running server keeps the options it started with. Give them on every start:

- `-Xmx` fits the server and the test JVMs it forks into the memory the run may use. A measurement to judge it from: a
  server that holds the whole build retains about 0.8 GB of Zinc analyses after a full GC (35 projects) and allocates
  about 170 MB/s in sbt's own task engine even when every suite is served from the cache, so under `-Xmx1200m` it spent
  most of a run of every project in GC on two CPUs, slowing the forked tests past their deadlines; under `-Xmx2g` its
  live set peaked at 1.47 GB. Narrowing sbt's `concurrentRestrictions` cut the scheduler's share of the allocation about
  tenfold but changed neither the GC time nor the wall time, so the build keeps sbt's default. A server that compiles the
  whole build and also links trace-player with Scala.js needs more: under `-Xmx2g` it ran out of heap in trace-player's
  links (`fullLinkJS`, then the test `fastLinkJS`) and stopped answering, `sbt --client shutdown` included; under
  `-Xmx4g` its heap still ran near full. Such a run, the server with ZGC and its forked tests at `-Dgezi.testHeap=3g`,
  peaked at 6.93 GB compiling alone, 9.85 GB at `-Xmx4g` with one test thread, 11.05 GB at `-Xmx6g` with one, and
  12.44 GB at `-Xmx4g` with four.
- `-Xms64m`, `-XX:+UseZGC` and `-XX:ZUncommitDelay=60` let an idle server give its memory back. sbt's own defaults,
  used when `SBT_OPTS` gives neither `-Xms` nor `-Xmx`, are `-Xms1024m -Xmx1024m`, a heap that never shrinks; with a
  small initial heap and ZGC uncommitting memory unused for 60 seconds, an idle server keeps only its live set.

Tests and runs fork a JVM, and for the JVM the small limit is time, not memory: the test deadlines of "Tests fail fast"
and the reading budgets. A JVM's own footprint (metaspace, code cache, JIT, GC structures) is large, so a small heap
mostly catches that footprint rather than the tests. A test JVM's heap is sized to the memory the run may use, leaving
room so that a test that does run out fails with the JVM's own `OutOfMemoryError`, naming the test, rather than being
killed by the kernel.

Tests run in parallel by threads in one test JVM, not by processes: one sbt test worker (`Global / workerMaxInstances` 1)
whose suites run in parallel threads, with a heap that takes nearly all the memory the run may use, so that its fixtures,
JIT warm-up and footprint are paid once. Suites that must not overlap inside that JVM, such as two that run `lake` over
one `.lake`, are kept apart at the test level, since sbt's tags order sbt tasks, not threads inside a JVM. How many
threads a run uses is not fixed by the build: the suites run one at a time unless a run says
`set every Test / testForkedParallelism := Some(n)`, with the heap its server was started with (`-Dgezi.testHeap`);
`project/TestHeap.scala` has the details and the FIXME on a heap measured per thread. The heap leaves room for a high
parallelism, so that a run on a server that may use every core does not run out of memory.

One knob changes what the default run costs: the JIT's law against weak_head (`contest-corpora`'s `JitReadingLawTest`)
checks 30 generated inputs per property; `LAMBDAJIT_JIT_LAW_SAMPLES=<count>` checks another count, and
`HEDGEHOG_SEED=<seed>` replays a failure's inputs.

The CI workflow, `.github/workflows/scala.yml`, runs `sbt test` on every push (except Scala Steward's `update/**`
branches) and pull request.
