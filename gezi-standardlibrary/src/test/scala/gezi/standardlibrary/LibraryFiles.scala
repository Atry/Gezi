package gezi.standardlibrary

import java.nio.file.Path
import java.nio.file.Paths

/** The source trees the tests compile libraries from, found from the build's
  * root, and the helpers several tests share.
  */
object LibraryFiles:

  /** The root of Gezi's build, which the build passes to the forked test JVM.
    */
  val buildRoot: Path = Paths.get(
    sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalStateException(
        "the build passes gezi.buildRoot to the forked test JVM"
      )
    )
  )

  /** The source tree of the standard library, `corpora`, whose `library` holds
    * the library files and `compiler` the knowledge files.
    */
  val sourceTree: Path = buildRoot.resolve("corpora")

  /** The library of the file at the path relative to the build root, such as
    * `tests/library_fixtures/presets.lambdalattice` or
    * `corpora/compiler/top.lambdalattice`, with the backends' checks: the
    * knowledge the file holds as the one field of its tuple, a knowledge file
    * of one field or a fixture whose field is the choice of the knowledge files
    * it imports at its top (`StandardLibrary.compiledAt`), read off the tree
    * whose visible subtree is Gezi's directory. A fixture under tests/ imports
    * from `gezi "corpora"`. FIXME: those
    * https://github.com/Atry/private-overlay/issues/1924 imports depend on the
    * project root's directory being named gezi; they break if that directory is
    * renamed.
    */
  def compiled(
      file: String,
      backends: Vector[LibraryBackend]
  ): StandardLibrary =
    StandardLibrary.compiledAt(buildRoot, buildRoot.resolve(file), backends)

  /** The source tree of a small library of `tests/standard_library_fixtures`, a
    * directory whose name is the fixture's.
    */
  def fixture(name: String): Path =
    buildRoot.resolve("tests/standard_library_fixtures").resolve(name)

  // TODO: compiledDeclaring, directoryFiles and standardWith stood here. Their purpose: a library compiled with
  // the library files of directories declared beside its knowledge, so that a test's programs could name them.
  // They named library terms by declared library files listed by directory, a table of library files deleted
  // when the library became files reached by paths. Their replacement reads the library
  // terms it needs as members of a fixture file under tests/ by projection and composes them with the HOAS case
  // of a closed instruction. The deleted code:
  // git show 2908bffd5:lambda_jit/standardlibrary/src/test/scala/lambdajit/standardlibrary/LibraryFiles.scala.

  // TODO: prologTerm, nativeRouteDirectories, nativeDirectories, preludeDirectories, both programNames,
  // worldDirectories, namedInstruction, declaredDirectories and filesOf stood here. Their purpose: the map from
  // the names of library files to their instructions through which the tests' programs, written in the HOAS of `Term`
  // (Term.define) or in the Prolog surface, named library files, and the directories that map was taken from.
  // They named library terms by LibraryFiles.programNames and namedInstruction, a free variable (blacklisted) and
  // a table of library files deleted when the library became files reached by paths.
  // Their replacement reads the library terms it needs as members of a fixture file under tests/ by projection
  // (`StandardLibrary.entryTerm`, `KnowledgeReading.memberTerm`) and composes them with the HOAS case of a closed
  // instruction. The deleted code:
  // git show 2908bffd5:lambda_jit/standardlibrary/src/test/scala/lambdajit/standardlibrary/LibraryFiles.scala.
