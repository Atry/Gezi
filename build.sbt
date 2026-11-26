// Gezi's Scala code and the framework it is built on, the generic e-graph, in one build.
// Every project is a top-level directory of this one whose name is its
// package below `gezi`, the segments joined by `-`; each directory's
// build.sbt holds all of that project's settings, and this file holds the
// projects and their dependencies only.
//
// The module graph. Each arrow is the only kind of dependency a module may
// have (CONTRIBUTING.md, "The module graph" and "The framework", gives the
// reason for each framework module):
//
// The framework:
//
//   generatedinputs      (nothing: the infrastructure of generated test
//                        inputs, which the tests of every module use)
//   ir
//   orientation          -> ir
//   egraph               -> ir
//   ematching            -> ir, egraph                (the backend interface)
//   ematching-indexing   -> ematching, orientation    (orientations to programs)
//   ematching-interpretation -> ematching             (a backend: the program walked)
//   ematching-closures   -> ematching                 (a backend: Scala closures)
//   ematching-bytecode   -> ematching                 (a backend: a hidden class)
//   saturation           -> ematching                 (no backend, no fixture)
//   extraction           -> egraph                    (the greedy extraction)
//   backendcomparison    -> ematching-indexing, saturation,
//                           ematching-interpretation, ematching-closures,
//                           ematching-bytecode
//
// Gezi:
//
//   frontend             -> ir (the front end)
//   standardlibrary      -> frontend, knowledge-reading (the standard
//                           library's loader and index); its tests also run orientation,
//                           ematching-indexing, saturation and
//                           ematching-closures, and read the fixtures
//   programfamilies      -> standardlibrary, strategies, orientation and
//                           backendcomparison (the program families of the
//                           two configurations and their runs to the fixed
//                           point); its tests also use standardlibrary's
//                           test helpers
//   jmh-pipeline         -> programfamilies, contest-corpora, jit,
//                           contest-entry-generic, provenance, and
//                           standardlibrary's test generators (JMH
//                           benchmarks only: the pipeline's stages, the
//                           classic Hindley-Milner reference, the contest
//                           families' native solvers, the JIT's run of a
//                           program the framework's fixture entry compiled
//                           and what source locations cost)
//   rewrite-trace        -> frontend, knowledge-reading, saturation (the
//                           rewrite trace: its commands, their replay, and its
//                           text read under weak head, all the animation
//                           player needs; a backward higher-order conversion
//                           replayed by saturation's HigherOrderMatching)
//   proofs               -> standardlibrary, frontend, rewrite-trace (the
//                           OpenTheory article
//                           of a strategy's proof and the Lean module of the
//                           library's lemma statements); its tests also use
//                           standardlibrary's test helpers, and run the
//                           opentheory tool and Lean's lake
//   strategies           -> standardlibrary, proofs, orientation,
//                           ematching-indexing, the three backends
//                           (ematching-interpretation, ematching-closures,
//                           ematching-bytecode), saturation and extraction
//                           (the baseline's search strategies, the
//                           extraction's ordering modules and the schedule,
//                           which writes a round's article with proofs'
//                           writer); its tests also use standardlibrary's
//                           and proofs' test helpers, and run the opentheory
//                           tool and Lean's lake on the articles of the
//                           fixpoint runs
//   weakhead             -> standardlibrary, frontend (the weak-head
//                           evaluator, its tabling, the readers and the
//                           codecs); its tests also use standardlibrary's
//                           test helpers
//   contest-corpora      -> standardlibrary, weakhead (the generators of the
//                           problem corpora's programs, written in the HOAS,
//                           and their judges); its tests check the
//                           generators and also run the JIT of
//                           jit on the corpora (the corpora stand above
//                           jit), and build their cache
//                           service with hotspot-baselines' provider
//   jit                  -> weakhead, standardlibrary, strategies,
//                           rewrite-trace (whole-block compilation, the JIT,
//                           the natives, the backend's checks, whose premise
//                           check steps by rewrite-trace's β rule, and the
//                           dispatch of a test under a strategy, whose
//                           schedule `strategies` runs, as jit_strategies.pl
//                           called schedule.pl);
//                           its tests also use their test helpers
//   interface-laws       -> jit, strategies and their test helpers,
//                           generatedinputs (the laws of the replaceable
//                           interfaces, run on any implementation; test
//                           support, a test dependency of every entry and
//                           module)
//   contest-entry        -> jit, frontend, hotspot-baselines,
//                           lemma-encoding-baseline, narrow-blocks, the
//                           e-matching backends (the interface a contest
//                           entry implements, and `Defaults`, the one
//                           place the framework's default implementation of
//                           each interface is chosen)
//   contest-runner       -> contest-entry (the runner in an entry's JVM: the
//                           provider loaded by ServiceLoader, the ready line,
//                           the pipe loop)
//   narrow-blocks        -> jit, strategies, frontend, standardlibrary,
//                           lemma-encoding-baseline, hotspot (the narrow
//                           back end: the narrow grammar's check, its
//                           bytecode compilation, the lemma route, and the
//                           compiler of a program unit by the lemma rounds;
//                           one of the baseline's public projects, which
//                           every entry and module depends on)
//   contest-entries-<entry> -> contest-entry and the baseline's public
//                           projects (each directory contest-entries-<entry>/
//                           with a build.sbt or a src/, found by
//                           project/EntryProjects.scala) and every
//                           contest-modules-<name>, never contest-corpora or
//                           contest-judge
//   contest-modules-<name> -> contest-entry, whose replaceable interfaces
//                           it implements (ExecutorModule, ExtractorModule),
//                           and the baseline's public projects (a
//                           reusable module with no EntryProvider, found by
//                           project/EntryProjects.scala)
//   contest-in-tree-entries -> every contest-entries-<entry>, through them
//                           every contest-modules-<name>, and
//                           contest-entry-generic (tests only: the suites
//                           that read the in-tree entries, InTreeEntriesTest,
//                           CancelGraceLawTest and CompilationPlaceLawTest,
//                           on a classpath that, as an entry's JVM, holds
//                           every module's registrations; defined by
//                           project/EntryProjects.scala)
//   contest-judge        -> contest-entry, contest-runner, contest-corpora,
//                           jit (the points file,
//                           the reference readers, the supervisor and the
//                           article check); its
//                           tests run the supervisor on an entry, whose
//                           classpath and the runner's the build passes as
//                           properties: an entry's JVM runs on those two
//                           alone, without contest-corpora or contest-judge
//   jupyter-kernel       -> contest-runner, contest-entry-generic (the
//                           Jupyter kernel of lambdalattice cells, an almond
//                           adapter that hands each cell to Entry.run of the
//                           data entry of a directory given at the install;
//                           no module depends on it)
//   warts                (nothing: the custom warts of the immutability rule,
//                        loaded by the compiler plugin into every other project)
//   conventions          (tests only: reads the sources of the others)
//
// Scala.js (the trace player; no JVM project depends on these):
//
//   generatedinputs-js, ir-js, frontend-js, hotspot-js,
//   weakhead-core-js     (the sources of the JVM project of the name without
//                        `-js`, but those its build.sbt lists as needing the
//                        JVM, depending as that project does)
//   trace-player         -> frontend-js, weakhead-core-js (the player, a
//                           script with no module system)

// An sbt server started in the background exits after 15 minutes without a
// command; under sbt 2 plain `sbt` is the thin client and starts such a server,
// as `sbt --client` does (`sbt --server` runs it in the foreground instead).
// sbt's own default is 7 days (sbt 2.0.12, Defaults.globalSbtCore), so servers
// of finished worktrees stayed alive: on 2026-10-31, 45 idle servers held
// 61.5 GB of the machine's 64 GB swap.
// The next client starts a fresh server. sbt reads the timeout in the scope of
// the current project (sbt 2.0.12, ProjectExtra.updateCurrent), which is this
// root when the server starts.
LocalRootProject / serverIdleTimeout := Some(scala.concurrent.duration.FiniteDuration(15, java.util.concurrent.TimeUnit.MINUTES))

LocalRootProject / publish / skip := true

// One test group at a time among those that run lake in the Lean package
// (project/LeanTests.scala; proofs/build.sbt, standardlibrary/build.sbt and strategies/build.sbt tag
// their groups).
Global / concurrentRestrictions += Tags.limit(LeanTests.lean, 1)

// One test worker, whose JVM runs its suites in parallel threads and may use
// nearly all the memory (project/TestHeap.scala): tests run in parallel by
// threads in one JVM, not by processes. sbt 2.1's default is two.
Global / workerMaxInstances := 1

// The server's one root output directory: its working directory's target/out,
// as sbt chooses by default (sbt 2.0.12, RemoteCache.globalSettings), or
// target/<gezi.outputDirectory> when the server is started with that system
// property, so that a second server over the same worktrees, one that runs the
// tests while the first compiles, writes its own outputs and the two share
// results only through sbt's machine-wide disk cache, and the tests do not
// block the compilation. It is one
// root for every build the server loads, Global and computed alike in each:
// sbt 2's action cache stores a task's outputs only when they lie under it
// (sbt 2.1.0-RC3, ActionCache: "Cannot cache task because its output files
// are outside the output directory"), so a root per build left every task of
// a build attached to the shared server uncached (measured 2026-11-16). The
// builds attached to a server put their projects' outputs in a directory of
// their own under it (project/BuildOutputs.scala).
Global / rootOutputDirectory :=
  appConfiguration.value.baseDirectory.toPath.resolve("target").resolve(sys.props.getOrElse("gezi.outputDirectory", "out"))

// The immutability rule of CONTRIBUTING.md ("The code is 100% immutable"), enforced
// by WartRemover on every project's Compile and Test sources: `var`, the
// `scala.collection.mutable` collections and `while` are compile errors. The
// JMH protocol's `@Param` fields are suppressed at their declarations with
// @SuppressWarnings. The rest of the rule is the custom warts of the project
// `warts` (one per family of symbols, found by symbol and not by text), whose
// classes the compiler plugin loads from the classpath below.
// NoArray forbids making or writing an array in source: `Array(...)`, `new Array`,
// `Array.ofDim`, `fill`, `tabulate`, `empty`, `range`, `iterate`, `concat`,
// `copyOf` and `copyAs`; `update` (also reached by `a(i) = x`);
// `System.arraycopy`; `java.util.Arrays.fill`, `setAll`, `sort` and
// `parallelSort`; and `toArray` on a collection. It does not forbid a type
// that mentions Array, reading an array, an array that a JDK call returned,
// or the `Array[String]` of `@main`.
ThisBuild / wartremoverErrors ++= Seq(Wart.Var, Wart.MutableDataStructures, Wart.While) ++ Seq(
  "NoArray",
  "NoDynamicVariable",
  "NoIterator",
  "NoJavaUtilConcurrent",
  "NoJavaUtilMutableCollection",
  "NoNewBuilder",
  "NoStringBuilder",
  "NoThreadConfinedCapture",
  "NoThreadLocal",
  "NoUnsafe",
  "NoVarHandle",
  "NoVolatile"
).map(name => Wart.custom(s"gezi.warts.$name"))

// A match the compiler cannot prove exhaustive (E029) is an error: each match
// is total, a case that cannot occur ending in a throw that names the
// invariant, never in a silent wildcard (f2e5dc1e4 and the commit that adds
// this line made the last sites total).
ThisBuild / scalacOptions += "-Wconf:id=E029:e"

// The classes of the custom warts, and a second entry that names no file: the
// URI carries the jar's content hash, because sbt 2 caches a compilation by
// its inputs, the options among them, and the jar's path stays the same when
// a wart changes, so that a failure (or a success) of the compilation under
// the old wart would be served from the cache. The class loader ignores an
// entry that is not there.
ThisBuild / wartremoverClasspaths ++= {
  val converter = fileConverter.value
  (warts / Compile / exportedProducts).value.flatMap(entry =>
    Seq(
      converter.toPath(entry.data).toUri.toString,
      s"file:///custom-warts-content-hash/${entry.data.contentHashStr}"
    )
  )
}

// The custom warts of the immutability rule, for WartRemover: classes that
// the compiler plugin loads while it compiles every other project, so this
// project's classes depend on nothing of the build and hold warts only; its
// tests depend on generatedinputs (FailFastSuite).
lazy val warts = project.dependsOn(generatedinputs % Test)

// Generated inputs (CONTRIBUTING.md, "Tests": every test's inputs are
// generated, whether it checks a law or records a snapshot). The
// infrastructure of generated test inputs: properties checked by Hedgehog in
// munit suites, seeded samples and snapshots, and state machine tests. It
// depends on no module, so that the tests of every module can depend on it;
// a generator of a module's own data lives in that module's test sources, in
// the package `gezi.generatedinputs`, and the modules above reach them
// with `test->test`, since a project the module's tests depend on cannot
// depend on the module (sbt rejects the cycle: "Cyclic reference involving",
// 2026-10-31).
lazy val generatedinputs = project

lazy val ir = project.dependsOn(generatedinputs % Test)

lazy val orientation = project.dependsOn(ir, generatedinputs % Test)

lazy val egraph = project.dependsOn(ir % "compile->compile;test->test", generatedinputs % Test)

lazy val ematching = project.dependsOn(ir, egraph)

lazy val `ematching-indexing` = project.dependsOn(ematching, orientation, generatedinputs % Test)

lazy val `ematching-interpretation` = project.dependsOn(ematching)

lazy val `ematching-closures` = project.dependsOn(ematching, generatedinputs % Test)

lazy val `ematching-bytecode` = project.dependsOn(ematching)

lazy val saturation = project.dependsOn(ematching, generatedinputs % Test, ir % "test->test")

lazy val extraction = project.dependsOn(egraph, saturation, generatedinputs % Test)

// The source locations of an e-graph's nodes, from its union log
// outside the framework, and no choice reads a location.
lazy val provenance = project.dependsOn(
  egraph,
  extraction,
  locations,
  generatedinputs % Test,
  frontend % "test->test",
  backendcomparison % Test
)

// Migrations of lambdalattice texts checked by reading them again, a
// lemma's instances found by the e-graph's matching; outside the framework.
lazy val migration = project.dependsOn(
  frontend % "compile->compile;test->test",
  `directory-sugar`,
  `knowledge-reading`,
  provenance,
  saturation,
  `ematching-indexing`,
  `ematching-closures`,
  generatedinputs % Test
)

lazy val backendcomparison = project
  .dependsOn(
    `ematching-indexing`,
    saturation,
    `ematching-interpretation`,
    `ematching-closures`,
    `ematching-bytecode`,
    ir % "test->test",
    generatedinputs % Test
  )

// TODO: a JMH benchmark (CONTRIBUTING.md, "Timings are JMH benchmarks") of the three e-graph matching backends, interpretation
// (`ematching-interpretation`), closures (`ematching-closures`) and bytecode
// (`ematching-bytecode`), on inputs generated from `programfamilies`' HOAS
// program families instead of the deleted Prolog fixtures, in a project
// that holds benchmarks only, where the project `jmh-ematching` stood.

// Source locations for people and tools; no choice reads one (`conventions`' dependency check).
lazy val locations = project.dependsOn(ir, generatedinputs % Test)

// The front end: the object language as written (Scala HOAS, lambdalattice
// text) to de Bruijn terms, and those to the IR, hash-consed by an interner threaded through as a value.
lazy val frontend = project.dependsOn(ir, locations, generatedinputs % Test)

// The interfaces of hotspot compilation:
// executors, compilation units and compilers, the tiering policy's
// decisions, the cache service with its namespaces, guards, providers and
// lifecycle events, and the multithreading framework's fork and join.
// Interfaces only, and the fork and join primitive; every
// other implementation is elsewhere. It depends on `ir` for instructions and
// codes and on `frontend` for instructions.
lazy val hotspot = project.dependsOn(ir, frontend, saturation, generatedinputs % Test)

// The baselines of the cache and of the tiering policy: a thread safe cache provider in the process over a concurrent map,
// cleared when a round starts, and a tiering policy that always
// interprets with the whole budget. The executors and the compiler of the
// baseline are in `weakhead` and `jit`, beside what they wrap.
lazy val `hotspot-baselines` = project.dependsOn(hotspot, generatedinputs % Test)

// The loader of the standard library: the source trees read by the
// directory loader, the knowledge files and the library files they reach,
// and the declarations (lemma, native
// and combinator_property) read with knowledge-reading into the five facts
// of its index.
lazy val standardlibrary = project
  .dependsOn(
    frontend % "compile->compile;test->test",
    `knowledge-reading`,
    `directory-sugar`,
    generatedinputs % Test
  )

// The interface by which an entry encodes a lemma's two closed terms as the
// patterns of its orientations, an entry's choice and not the framework's
// (the arity of a pattern is how an entry writes it): `LemmaEncoding` and
// `EncodedLemma`.
// `strategies` and `proofs` depend on it and on no implementation.
lazy val `lemma-encoding` = project.dependsOn(standardlibrary)

// The baseline's lemma encoding, `BaselineLemmaEncoding`. The
// top-level composers choose it: programfamilies, the contest entries, and
// the tests of proofs, strategies and jit. Its tests compile orientations
// and saturate with them.
lazy val `lemma-encoding-baseline` = project
  .dependsOn(
    `lemma-encoding`,
    standardlibrary % "test->test",
    generatedinputs % Test,
    orientation % Test,
    `ematching-indexing` % Test,
    saturation % Test,
    `ematching-closures` % Test
  )

// The program families of the two configurations (gezi.programfamilies.Configurations),
// written in the HOAS, and their runs: the configuration's library and orientations
// compiled, the program put through the front end, the graph saturated and
// the form of its fixed point computed by backendcomparison
// (`gezi.programfamilies.FixedPoints`). Its tests record the forms of
// generated items' fixed points as a snapshot and compare the inputs with
// snapshots of their digests. The pipeline whose stages it counts
// (`gezi.programfamilies.Pipeline`) runs, after the saturation, the
// extraction of the baseline's round with the strategies' cost model.
lazy val programfamilies = project
  .dependsOn(
    standardlibrary % "compile->compile;test->test",
    strategies,
    `lemma-encoding-baseline`,
    generatedinputs % Test,
    orientation,
    backendcomparison
  )

// The JMH benchmarks of the pipeline, of the classic Hindley-Milner
// reference and of the contest families' native solvers (CONTRIBUTING.md,
// "Timings are JMH benchmarks"), run through sbt-jmh:
// `jmh-pipeline/Jmh/run`. The project holds benchmarks only; what they run
// is programfamilies' code, contest-corpora's native solvers
// (`NativeSolverBenchmark`, `ContestWorkloadBenchmarks`) and the JIT's
// reading of contest programs under its instance table
// (`InstanceTableBenchmarks`) and as the framework's fixture entry,
// contest-entries-fixture/entry.lambdalattice, compiles it under the generic
// entry (`CompiledRunBenchmark`), and what reading a text with its locations
// and computing a saturated graph's provenance cost (`LocationBenchmarks`).
// The benchmarks' knowledge is generated from a fixed seed by
// standardlibrary's generator of knowledge, which lives in its test sources
// as every module's generators do; the benchmarks, which are this project's
// main sources, depend on those test sources and on generatedinputs for it.
lazy val `jmh-pipeline` =
  project.dependsOn(
    programfamilies,
    `contest-corpora`,
    jit,
    `contest-entry-generic`,
    `jupyter-kernel`,
    provenance,
    standardlibrary % "compile->test",
    generatedinputs
  )

// The baseline's search strategies, the port of the Prolog baseline/
// strategies and schedule.pl: the
// ordering modules of a normality degree, the strategy fixpoint_egraph
// (saturation, then extraction under the ordering modules),
// the schedule of rounds, the native route's schedules and the dispatch
// strategy. Strategies remember costs only and name no lemma and no
// combinator (CONTRIBUTING.md, "Types live only in the term"). A round that
// writes an article writes the OpenTheory article of its strategy's proof
// with the writer of `proofs`, as schedule.pl does with
// opentheory_article.pl; the proof is `gezi.proofs.StrategyProof`. The
// tests of the fixpoint runs of opentheory_article.plt are here, since they
// run the schedule: they read proofs' test helpers and run the opentheory
// tool and Lean's lake. The saturation of fixpoint_egraph runs on a backend
// of the framework (`SaturationOptions.backend`), closure compilation unless
// an entry chooses interpretation or bytecode compilation; the three are
// compile dependencies, so that every project above, the entries included,
// reaches them.
lazy val strategies = project
  .dependsOn(
    standardlibrary % "compile->compile;test->test",
    proofs % "compile->compile;test->test",
    `lemma-encoding`,
    `lemma-encoding-baseline` % Test,
    generatedinputs % Test,
    ir % "test->test",
    orientation,
    `ematching-indexing`,
    `ematching-interpretation`,
    `ematching-closures`,
    `ematching-bytecode`,
    saturation,
    extraction
  )

// The core of the weak-head evaluator, the part that reads no library index:
// the evaluator on the IR in its two modes, weak_head and tabling(weak_head),
// the immutable tabling that decides the second, the readings within a
// budget of evaluator steps and the normal-form reader. It depends on no
// knowledge, so that the reader of knowledge files can evaluate them. The
// package gezi.weakhead spans it and weakhead, whose package object
// documents both.
lazy val `weakhead-core` = project.dependsOn(frontend, hotspot, `directory-sugar`)

// The generic reader of knowledge written in lambdalattice: the
// slots of a top-level mixin, Scott constructors, lists and strings, read
// under weak head. It knows no knowledge; standardlibrary depends on it.
lazy val `knowledge-reading` =
  project.dependsOn(`weakhead-core`, frontend % "compile->compile;test->test", generatedinputs % Test)

// The sugar of a directory tree: the tree read as one term, each directory and
// each file a mixin, its entries URI nodes of the IR whose expansions it
// gives, a directory listed or a file parsed when the evaluator first expands
// it. It resolves no name: a reader applies the root to keys and evaluates.
// The evaluator (weakhead-core) calls its expansion, so its laws, which read
// under the evaluator, are knowledge-reading's tests.
lazy val `directory-sugar` =
  project.dependsOn(frontend, generatedinputs % Test)

// The codecs of the Prolog backend's representations, which read the
// library's index, and the Scott decoder of the problem corpora
// (gezi.weakhead.oldcorpora), over weakhead-core. The port of
// weak_head.pl, evaluators.pl, reading.pl, normal_forms.pl, the three codecs
// and old_corpora/scott_decoding.pl. Its
// tests draw random terms with standardlibrary's test helper SplitMix.
lazy val weakhead = project
  .dependsOn(
    `weakhead-core`,
    standardlibrary % "compile->compile;test->test",
    frontend,
    hotspot,
    `hotspot-baselines` % Test,
    generatedinputs % Test
  )

// The FFI to the JVM:
// the computation graph a program's Moore machine state asks to run, decoded
// from a normal form the adapter's entry read, and the calls it makes. It
// depends on the front end alone and on no evaluator.
lazy val ffi = project.dependsOn(hotspot, generatedinputs % Test)

// The problem corpora: the generators of gezi/corpora's programs,
// ported from the clauses with bodies of its .pl files, whose facts stay in those files as data, and the judges that read
// the programs on the evaluator. The dependency runs from the corpora to
// weakhead, never back: weakhead's tests keep their own minimal helpers,
// and the corpora's tests use weakhead's (the reference evaluator). The
// law of the JIT against weak_head on the corpora's programs is here
// (`JitReadingLawTest`), so the tests also depend on jit and its test
// helpers: the corpora stand above jit, and nothing of jit reads the corpora.
lazy val `contest-corpora` = project
  .dependsOn(
    standardlibrary % "compile->compile;test->test",
    `directory-sugar`,
    weakhead % "compile->compile;test->test",
    generatedinputs % Test,
    jit % "test->test",
    `hotspot-baselines` % Test
  )

// The proof outputs: the OpenTheory article of a search strategy's proof
// and the Lean module of the library's lemma statements. A search strategy
// gives its proof as data (`gezi.proofs.StrategyProof`); the module
// `strategies`, whose schedule asks a round for its article, depends on this
// one. Its tests run
// the opentheory tool (tests/check_opentheory_article.sh) and `lake` of
// gezi/lean, both on the dev shell's PATH, and read standardlibrary's
// test helpers (`LibraryFiles`, `LeanFiniteTerms`).
// The rewrite trace: a start term and the commands of each round, replayed to the terms
// they make, and the trace's text, Scott data read under weak head. It needs
// no proof, no library and no strategy, so that the animation player depends
// on it alone; `proofs` flattens an article's proof into its commands.
lazy val `rewrite-trace` =
  project.dependsOn(frontend, `knowledge-reading`, saturation, generatedinputs % Test)

lazy val proofs = project
  .dependsOn(
    standardlibrary % "compile->compile;test->test",
    frontend,
    `rewrite-trace`,
    `lemma-encoding`,
    `lemma-encoding-baseline` % Test,
    generatedinputs % Test
  )

// The whole-block compilation of the thunk IR into Scala closures behind a
// backend interface, the JIT evaluator on it (the evaluator `Mode.Jit` of
// `weakhead` runs), the native implementations of the backend's set,
// the backend's checks of the standard library and the refinement of a
// test's typed output. The port of jit.pl, jit_emission.pl,
// jit_strategies.pl, prolog_backend_library.pl and prolog_backend_natives.pl
// A test is dispatched under a strategy whose schedule is a schedule of
// `strategies` (below this module), run by its `Schedule.run` as jit_strategies.pl ran
// schedule_run/3, and its dispatch strategy is one of `strategies`. Its
// tests use standardlibrary's, weakhead's and strategies' test helpers;
// the tests of the native route's compilation, which run the schedules and
// the JIT, are here.
lazy val jit = project
  .dependsOn(
    weakhead % "compile->compile;test->test",
    hotspot,
    `hotspot-baselines`,
    standardlibrary % "compile->compile;test->test",
    strategies % "compile->compile;test->test",
    `rewrite-trace`,
    `lemma-encoding-baseline` % Test,
    generatedinputs % Test
  )

// The laws of the replaceable interfaces (JitEvaluator, Extractor), written
// against each interface and run on any implementation. Test
// support, like generatedinputs: its main sources are munit suites over the
// test helpers of jit and strategies; its tests run the laws on the
// baseline's implementations, and every entry's and module's tests depend
// on it (project/EntryProjects.scala).
lazy val `interface-laws` = project.dependsOn(
  jit % "compile->compile;compile->test",
  strategies % "compile->compile;compile->test",
  generatedinputs
)

// The narrow back end: the narrow grammar's check, its bytecode compilation,
// and the lemma route, and the compiler of a program unit by the lemma rounds
// (hotspot's `Compiler`). Moved from the entry `wren`'s module of the base natives; it
// names no entry's native, an entry hands it its native backend. Every
// entry and module depends on it (project/EntryProjects.scala).
lazy val `narrow-blocks` =
  project.dependsOn(jit, strategies % "compile->compile;test->test", frontend, standardlibrary, `lemma-encoding-baseline`, hotspot)

// The interface of a contest entry: EntryProvider, registered with java.util.ServiceLoader, and
// Entry, and `Defaults`, the framework's default implementation of each
// replaceable interface, so it depends on
// the projects of those defaults (hotspot-baselines' cache provider,
// lemma-encoding-baseline's encoding, narrow-blocks' lemma compilation, the
// e-matching backends a round may choose). An entry's project,
// contest-entries-<entry>, is defined by project/EntryProjects.scala for
// every directory contest-entries-<entry>/ that holds a build.sbt or a src/.
lazy val `contest-entry` =
  project.dependsOn(
    jit,
    frontend,
    hotspot,
    `hotspot-baselines`,
    `lemma-encoding-baseline`,
    `narrow-blocks`,
    `ematching-closures`,
    `ematching-interpretation`,
    `ematching-bytecode`,
    `knowledge-reading`,
    generatedinputs % Test
  )

// The framework's entry for an entry written as data: it registers GenericEntryProvider
// with ServiceLoader, so only the project of an entry directory that holds
// entry.pl and no Scala depends on it (project/EntryProjects.scala); a
// second provider on an entry's classpath would be refused by the runner.
lazy val `contest-entry-generic` =
  project.dependsOn(
    `contest-entry`,
    `narrow-blocks`,
    standardlibrary,
    strategies,
    frontend % "test->test",
    generatedinputs % Test
  )

// The runner in a contest entry's JVM: it loads the entry's provider by ServiceLoader, writes
// the ready line and answers the points of the pipe. It depends on
// `contest-entry` only: an entry's JVM runs on the entry project's classpath
// and this project's, so that it holds neither contest-corpora (the
// generators and the references) nor contest-judge. Its tests use the front
// end's test helpers.
lazy val `contest-runner` =
  project.dependsOn(`contest-entry`, frontend % "test->test", generatedinputs % Test)

// The judge: the
// points file, the reference readers and the supervisor, a separate
// process. `contest-judge/run` starts the supervisor in a forked JVM that
// knows each entry's classpath and the runner's. An entry's JVM gets the
// small heap of -Xmx256m as every reader's does.
lazy val `contest-judge` = project
  .dependsOn(
    `contest-entry`,
    `contest-runner`,
    `contest-corpora` % "compile->compile;test->test",
    jit,
    generatedinputs % Test
  )

// The Jupyter kernel of lambdalattice cells: almond's interpreter, which
// hands an io member's Moore machine state and the JVM service to its entry
// and shows the values a cell's keys hold
// through the entry its classpath registers, the framework's generic entry,
// reading the data entry of the directory the install names (no entry is the
// default: every preset is opt-in). The executor module of FFI programs is on its classpath
// so that an entry's data may select it. The whole module, an adapter on
// almond, is a local exception to the immutability rule.
lazy val `jupyter-kernel` = project.dependsOn(
  `contest-runner`,
  `contest-entry-generic`,
  LocalProject("contest-modules-moore"),
  ffi,
  frontend % "test->test",
  generatedinputs % Test
)

// The projects compiled for Scala.js, for the trace player. Each compiles the
// sources of the JVM project its name ends in `-js` after, from that
// project's directory, but those that need the JVM, which its build.sbt
// lists with the reason, and depends on the projects compiled for Scala.js
// that the JVM project's dependencies are compiled into. No JVM project
// depends on them.
lazy val `generatedinputs-js` = project

lazy val `ir-js` = project.dependsOn(`generatedinputs-js` % Test)

lazy val `locations-js` = project.dependsOn(`ir-js`)

lazy val `frontend-js` = project.dependsOn(`ir-js`, `locations-js`, `generatedinputs-js` % Test)

lazy val `hotspot-js` = project.dependsOn(`ir-js`, `frontend-js`, `generatedinputs-js` % Test)

lazy val `directory-sugar-js` = project.dependsOn(`frontend-js`)

lazy val `weakhead-core-js` = project.dependsOn(`frontend-js`, `hotspot-js`, `directory-sugar-js`)

lazy val `knowledge-reading-js` = project.dependsOn(`weakhead-core-js`, `frontend-js`)

// The e-graph and saturation's higher-order matching compiled for Scala.js,
// so that the trace player replays a backward higher-order conversion with
// the matching the saturator runs, on a graph of the replaced term alone.
lazy val `egraph-js` = project.dependsOn(`ir-js`)

lazy val `saturation-js` = project.dependsOn(`egraph-js`, `ir-js`)

lazy val `rewrite-trace-js` = project.dependsOn(`frontend-js`, `knowledge-reading-js`, `saturation-js`)

// The trace player: a Scala.js script with no module system, which reads the
// trace embedded in its page, the start and the commands, and
// replays it with `rewrite-trace-js` to the terms it draws. Its tests run on
// Node.js and draw their inputs with frontend's generators.
lazy val `trace-player` =
  project.dependsOn(
    `frontend-js` % "compile->compile;test->test",
    `weakhead-core-js`,
    `rewrite-trace-js`,
    `generatedinputs-js` % Test
  )

// The generator of the trace player's end-to-end showcase, the directory
// trace-showcase that `trace-showcase/regenerate` writes: its program is in its
// test sources, where the strategies' and the standard library's test
// helpers it uses are on its classpath.
lazy val `trace-showcase` = (project in file("trace-showcase-generator"))
  .dependsOn(
    strategies % "compile->compile;test->test",
    standardlibrary % "compile->compile;test->test",
    `contest-entry-generic`,
    `contest-corpora`,
    jit
  )

// The immutability test and the package documentation test, run on this
// build's sources (tests only).
lazy val conventions = project.dependsOn(generatedinputs % Test)

lazy val `lambda-jit` = (project in file("."))
  .aggregate(
    generatedinputs,
    ir,
    locations,
    orientation,
    egraph,
    ematching,
    `ematching-indexing`,
    `ematching-interpretation`,
    `ematching-closures`,
    `ematching-bytecode`,
    saturation,
    extraction,
    provenance,
    migration,
    backendcomparison,
    frontend,
    hotspot,
    `hotspot-baselines`,
    standardlibrary,
    `lemma-encoding`,
    `lemma-encoding-baseline`,
    programfamilies,
    `jmh-pipeline`,
    strategies,
    `weakhead-core`,
    `knowledge-reading`,
    `directory-sugar`,
    weakhead,
    ffi,
    jit,
    `interface-laws`,
    `narrow-blocks`,
    `rewrite-trace`,
    proofs,
    `contest-corpora`,
    `contest-entry`,
    `contest-runner`,
    `contest-judge`,
    `jupyter-kernel`,
    `generatedinputs-js`,
    `ir-js`,
    `frontend-js`,
    `hotspot-js`,
    `locations-js`,
    `directory-sugar-js`,
    `weakhead-core-js`,
    `knowledge-reading-js`,
    `egraph-js`,
    `saturation-js`,
    `rewrite-trace-js`,
    `trace-player`,
    `trace-showcase`,
    warts,
    conventions
  )
  .aggregate(LocalProject(EntryProjects.aggregateProjectName))
  .enablePlugins(EntryProjects)
