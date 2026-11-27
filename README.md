# Gezi

A lambda calculus with choice and parallel, written in Scala 3. The standard library
is written as library files with the DSL declarations `lemma` and `native`
(there is no `define`; FIXME: files are still resolved by name), https://github.com/Atry/private-overlay/issues/2019
plus `combinator_property/2`, a fact about a library file, which needs a lemma only
when its vocabulary entry registers one (the associative entry does; backend
entries do not) (a downgrade of the rule that the library declares only `lemma` and
`native`);
type information lives only in the term, as assertion combinators; the
host (Scala) holds no type and no rule, and only chooses.

## Getting started

Gezi comes as `gezi-jupyter`, an OCI image of Jupyter with Gezi's kernel of
lambdalattice cells built in, built by Nix. Its entrypoint is `jupyter`: the
arguments of `docker run` are a subcommand of Jupyter, `console` when none is
given. The commands below work in this directory, whose `flake.nix` holds
Gezi's build artifacts, and in the monorepo's root, which imports the same
modules; both build the same images. With Podman, write `podman` for `docker`
and `.copyToPodman` for `.copyToDockerDaemon`.

### The images

The kernel runs a data entry, the `entry.lambdalattice` of the directory
`/gezi/entry` in the image, which chooses the compiler's knowledge, rounds and
backend; there is no default entry. The base image `gezi-jupyter-base:latest`
has none: mount a directory holding one there. Each in-tree entry written as
data has an image of its own, `gezi-jupyter:<entry>` (`:fixture`, `:solo` and `:wren`),
that holds its entry; that name has no `latest` tag. Build and load the entry `wren`'s:

```bash
nix build -L .#gezi-jupyter-wren
```

```bash
nix run .#gezi-jupyter-wren.copyToDockerDaemon
```

To run an entry of your own, build and load `.#gezi-jupyter-base` the same
way, copy an entry into a directory of its own (run from this directory),

```bash
mkdir my-entry && cp gezi-contest-entries-wren/entry.lambdalattice my-entry/
```

and mount the directory, not the file, at `/gezi/entry`, so that an edit saved
by renaming a new file over the old one reaches the container:

```bash
docker run -it --rm -v "$PWD/my-entry:/gezi/entry:ro" gezi-jupyter-base:latest
```

The entry's imports are written from `gezi "corpora"`: the image's `/gezi`
holds `corpora`, the library and compiler files, beside the entry's directory.
The kernel reads the entry when it starts; without one it stops with a message
saying where to mount it. Each image holds the commit it was built from:

```bash
docker run --rm --entrypoint cat gezi-jupyter:wren /gezi/REVISION
```

### Cells

The cells of a notebook are mixins joined by choice, at the notebook's place in the tree of URIs.
The kernel reads each cell after a prefix that
names the levels of that place, the root's self `uri` first, then for each level its key and its self: for a cell
run in the image's working directory `/env`, as `jupyter run` and `jupyter console` below run them, the prefix is

```
λuri "file" file "env" env.
```

and in a notebook it ends with the notebook's file name without `.ipynb` (for `/env/demo.ipynb`, `"demo" demo`).
Each self is named after its key, a key that is no name written with `$` escapes (`com.yang_bo.gezi.frontend.NameSpelling`).
A cell is any closed term under that prefix, and every cell joins the notebook by choice, but only a cell that is
a chain of `+` of partial functions, abstractions whose first binders are literals, has an output: the kernel
shows the notebook's member at each partial function's key path, as `"key" = value`, its binders renamed `x_0`,
`x_1`, and so on. A cell reads another cell's members, and its own, through the self of the notebook's level,
`env env "key"` at `/env`. Members of one key written by several cells are a choice, and each of its answers is a
line of the output.

A key path that starts with `"io"` is the one the kernel reserves: its member is the state of a Moore machine,
`λk. k output transition` (`corpora/library/java_ffi/moore`). The
output either ends the branch with an answer or runs a Java call, and the transition takes each reply to the next
state. How a state runs is the entry's: an entry runs one when
its data selects the executor module `gezi-contest-modules-moore` and enables the knowledge `corpora/compiler/java_ffi`, as
`tests/moore_fixtures/entry_with_moore.lambdalattice` does, and any other entry shows `this entry's executor runs no
FFI program`. Under such an entry, a state that only answers:

```
λ"io" "answer" k. k (λfinish run. finish λx. x) λinput_symbol. input_symbol
```

shows `"io" "answer" = λx_0. x_0`.

Running a cell of a notebook again replaces its earlier version, which the cell's Jupyter cell id names; a front
end that sends no cell id, as `jupyter console` does not, adds each cell as a new one. Only the new cell's keys
are shown: an earlier cell's output is not updated when a later cell adds to its key.

### From a shell: run cells and check text

`jupyter run` runs its standard input as one cell, prints what the kernel shows, and exits with status 1 when the
cell is answered with an error. It waits at most 10 s for the cell's answer (jupyter_client's `OUTPUT_TIMEOUT`,
which no option changes) and then fails with `TimeoutError: Timeout waiting for output`; a cell that runs or shows
longer is for the console or a notebook below. This is the way for a script or an agent to have a text read and
evaluated before showing it:

```bash
echo '(λ"two". λf x. f (f x)) + (λ"four". env env "two" (env env "two"))' | docker run -i --rm gezi-jupyter:wren run --kernel lambdalattice
```

prints `"two" = λx_0. λx_1. x_0 (x_0 x_1)` and `"four" = λx_0. λx_1. x_0 (x_0 (x_0 (x_0 x_1)))`. A text that
does not read is answered on the standard error with the reason, and the command exits with status 1:

```bash
echo '(λk. k null) λx. x' | docker run -i --rm gezi-jupyter:wren run --kernel lambdalattice
```

says `the cell does not read: UnboundName(null)`, since `null` is a name outside a literal and nothing binds it;
a Python traceback follows. A syntax error's offset is counted in code points from the start of the text the
kernel reads, the prefix and an opening parenthesis on a line of its own, whose length the message gives. The
JVM's lines on the standard error, `Picked up JAVA_TOOL_OPTIONS` and the warnings about `sun.misc.Unsafe`, come
with every run and are no error.

To check only that a closed text reads, without evaluating it, run the text itself as the cell: it has no output
unless it is a chain of partial functions, so the command prints nothing and exits with status 0 whenever the
text reads (`printf '%s'` passes it as written):

```bash
printf '%s' 'λf x. f (f x)' | docker run -i --rm gezi-jupyter:wren run --kernel lambdalattice
```

A text that closes a parenthesis it did not open, such as `λf x. f) (λy. y`, does not read, though the
parenthesis would close the kernel's own.

### Interactively: console and notebook

```bash
docker run -it --rm gezi-jupyter:wren
```

starts `jupyter console` on the kernel, which reads lines until the cell reads, and sends a cell that no further
line could make read at once, to be answered with its error; leave it with Ctrl-D and `y`.

```bash
docker run -it --rm -p 8888:8888 gezi-jupyter:wren notebook --ip=0.0.0.0 --no-browser
```

starts the notebook server and prints its address with a token,
`http://127.0.0.1:8888/tree?token=...`; open it, and pick the kernel
`lambdalattice` for a new notebook (Python's is there too, and is the
default).

### The library from a cell

The tree of URIs holds the image's `/gezi`, with the library under `corpora`, at the keys `"file" "gezi"`. A cell
projects a file off it as a file imports one, with `(λm. m m)` for `omega`, one `omega` and one key for each level
on the path, from the root's self `uri`, the file's key its name without `.lambdalattice`: the cell

```
λ"boolean". (λomega. omega (omega (omega (omega (omega (omega (omega uri "file") "gezi") "corpora") "library") "prelude") "boolean")) (λm. m m)
```

shows the tuple of `corpora/library/prelude/boolean`,
`"boolean" = λx_0. x_0 (λx_1. λx_2. x_1) (λx_1. λx_2. x_2) (λx_1. x_1 (λx_2. λx_3. x_2) (λx_2. λx_3. x_3)) (λx_1. x_1 (λx_2. λx_3. x_2))`.
A value with no normal form, such as a function defined by `fixpoint`, is shown for at most 10 s and then as
`not shown: the entry was stopped before it finished, by the end of the cell's 10 s of showing or by an interrupt`; the whole tuple of `list` or `natural`
shows so in `jupyter console` or a notebook.

A file's text is the tuple of its members: its first binder is `export`, and its last step hands the members to it,
`export nil cons append map length` in `corpora/library/prelude/list.lambdalattice`. A cell takes members by matching the tuple as an importing file
does, one binder for each member and `_` for a member it does not use. The import is written inside the partial
function whose member it shows:

```
λ"cons". (λomega. omega (omega (omega (omega (omega (omega (omega uri "file") "gezi") "corpora") "library") "prelude") "list") λ_ cons _ _ _. cons) (λm. m m)
```

shows `"cons" = λx_0. λx_1. λx_2. λx_3. x_3 x_0 x_1`. Written as a library file writes it, the import around the
partial function,

```
(λomega. omega (omega (omega (omega (omega (omega (omega uri "file") "gezi") "corpora") "library") "prelude") "list") λ_ cons _ _ _. λ"cons". cons) (λm. m m)
```

gives the notebook the same member, but the cell is an application, not a chain of partial functions, so it shows
nothing: where the import stands changes only what the kernel shows. Matching the tuple reads the file, so this is
also the way to check a file of the tree in its scope: a file that does not read is answered with `a file the cell
read is no lambdalattice text:` and the reason. A file is read only when a cell's output needs its value.

### Where the language is described

The grammar is the Scaladoc of
`gezi-frontend/shared/src/main/scala/com/yang_bo/gezi/frontend/Lambdalattice.scala`; the layout of a
text is `CONTRIBUTING.md`, "lambdalattice layout: no right-associative parentheses, CPS one step per line"; the library is
`corpora/library/`, and `corpora/library/prelude/` is the place to start
reading real files.

### How the images are built

Everything in the images is a Nix derivation (`modules/gezi-jupyter-image.nix`):
the JDK, and Python with jupyter_console and notebook, from nixpkgs, and the
kernel's jars, built by sbt inside the derivation `.#lambdalattice-jupyter-kernel`
through sbt-derivation's `mkSbtDerivation`, which fetches sbt's dependencies in
a fixed-output derivation. When a dependency of the build changes (a library, a
plugin, the version of sbt or of Scala), that derivation's hash changes: set
`depsSha256` in `modules/gezi-jupyter-image.nix` to `lib.fakeHash`, run
`nix build -L .#lambdalattice-jupyter-kernel`, and put the hash Nix reports
after `got:` in its place. Developing the code does not go through these
images: the dev shell below leaves the dependencies to sbt.

## Building and testing

An sbt build (`build.sbt`), Scala 3.10.0 on JDK 25, with munit, snapshot4s
and Hedgehog. It holds Gezi's projects and the framework's (the IR's
store, orientations, the e-graph, the index, the three backends,
saturation, extraction; section "The framework" below), each a top-level
directory named after its package below `gezi`. `build.sbt` declares
the projects and their dependencies, and each project's directory has a
`build.sbt` with that project's settings. From this directory, in the
monorepo's dev shell:

```
direnv exec .. sbt --client test
```

Tests fork with `-Xmx256m`; a project that needs more says so in its
`build.sbt`, with the measurement. All Scala is immutable, enforced by
WartRemover at compile time.

The Jupyter kernel of lambdalattice cells (`jupyter-kernel`) is installed by
a task of the build, the way almond installs its own kernels:

```
direnv exec .. sbt --client "gezi-jupyter-kernel/jupyterKernelInstall $PWD/gezi-contest-entries-wren"
```

Its argument is the directory of the data entry whose `entry.lambdalattice`
the kernel runs, read by the framework's generic entry; there is no default
entry. It writes `target/jupyter/kernels/lambdalattice/`, a kernel spec and a
launcher that holds the kernel's whole class path; the monorepo's dev shell
points `JUPYTER_PATH` at `target/jupyter` and has the same call as the
command `install-lambdalattice-jupyter-kernel <entry directory>`. Jupyter starts the kernel's
JVM from that launcher, without sbt. The kernel runs the code as it was at
the install: install again after a change, and restart the kernel.

An optional second argument, a directory relative to the notebook's (such as
`gezi-traces`), makes the kernel write the trace of every point its cells
extract there and show each in the cell's output with the trace player, in
JupyterLab (`com.yang_bo.gezi.jupyter.kernel.CellTraces`). Each trace's page holds the
player, about 4.8 MB.

The [trace showcase](https://atry.github.io/Gezi/) plays example traces.
The Pages workflow publishes the checked-in `trace-showcase` directory on pushes
to `main` and can also be run manually. The repository's Pages source must be
set to GitHub Actions; regenerate the showcase with `sbt trace-showcase/regenerate`.

## Projects

From the bottom up; each depends only on those above it (the module graph
at the top of `build.sbt`):

- `frontend`: the front end. The HOAS `Term` for writing the object language
  in Scala, the lambdalattice files' text, occurrence labels, and the
  defunctionalization into the IR, hash consed by `ir`'s global weak
  interners: the defunctionalization builds `Instruction`s and `Code`s
  directly (`Instruction.Apply`, `Instruction.Thunk`, `Code.Slot` and the
  rest). After the front end, only the IR.
- `standardlibrary`: the standard library's compiler and index, reading only
  `define` (the lambdalattice files), `lemma`, `native` and
  `combinator_property`, and the vocabulary of combinator properties. A
  lemma is its two closed terms, with no count of metavariables and no
  pattern.
- `lemma-encoding`: the interface by which an entry encodes a lemma's two
  closed terms as the patterns of its orientations (`LemmaEncoding`,
  `EncodedLemma`). `strategies` and `proofs` depend on it, never on an
  implementation; the caller chooses one.
- `lemma-encoding-baseline`: the baseline's encoding,
  `BaselineLemmaEncoding`, chosen by the top-level composers
  (`programfamilies`, the contest entries, and the tests).
- `proofs`: the OpenTheory article of a strategy's proof and the Lean module
  of the library's lemma statements, each lemma stated by the encoding its
  caller gives.
- `strategies`: the baseline's search strategies, the extraction's ordering
  modules and the schedule of rounds.
- `weakhead`: the weak-head evaluator on the thunk IR, its tabling, the
  readers within a budget of evaluator steps, the normal-form reader and the
  codecs.
- `contest-corpora`: the generators of the problem corpora's programs,
  written in the HOAS, and their judges; the old corpora's decoders.
- `jit`: whole-block compilation to Scala closures, the JIT, the
  natives, the backend's checks and the dispatch of a test under a
  strategy.
- `contest-entry`, `contest-runner`, `contest-judge`: the interface of a
  contest entry, the runner in an entry's JVM, and the judge; each entry is
  a directory `gezi-contest-entries-<entry>`, and `gezi-contest-in-tree-entries`
  holds the tests that read the in-tree entries on a classpath that sees
  every module.
- `programfamilies`: the classic HM reference, the program families and the
  pipeline split into its stages; no pipeline project depends on it.
- `jmh-pipeline`: the JMH benchmarks of those stages and of the classic
  HM reference (`gezi-jmh-pipeline/Jmh/run`), and nothing else.
- `conventions`: tests over the sources of the others.

## Data and the rest

- `corpora/`: the problems, their claims, answers and baselines, and the
  standard library's DSL sources (`corpora/standard_library/`), all read
  by the Scala as data.
- `tests/`: the fixtures the Scala tests read (`standard_library_fixtures/`,
  `opentheory_fixtures/`), the references they compare against (such as
  `opentheory_article_expected/`), and
  `check_opentheory_article.sh`.
- `lean/`: the Lean package that checks the exported traces; `modules/`: the
  nix modules of Lean and of the OpenTheory tool.
- `doc/gezi-proofs/`: paper proofs of the problems' claims and of earlier library
  lemmas. The paper proofs of the current library's lemmas are not in this
  repository; each lemma's declaration names its proof.

## The framework

The framework is the projects `ir`, `orientation`, `egraph`, `ematching`,
`ematching-indexing`, `ematching-interpretation`, `ematching-closures`,
`ematching-bytecode`, `saturation`, `extraction`, `backendcomparison` and
`generatedinputs`.

A prototype, in Scala 3, of an e-graph saturated to one least fixed point over
the defunctionalized IR of the λ-lattice, with every data structure immutable
and lemma orientations matched through an inverted index compiled by a
pluggable backend. `CONTRIBUTING.md` describes the modules and the rules of the code.

```bash
sbt --client test
```
