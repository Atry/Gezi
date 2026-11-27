package gezi.directorysugar

import java.net.URI
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.frontend.NameSpelling
import gezi.ir.ChoiceSpine
import scala.jdk.StreamConverters.*
import scala.util.Using
import gezi.ir.{Configured, NativeSpecializer, UriNode}

/** The sugar of a directory tree: the tree read as one term, each directory
  * and each file a mixin, a choice of partial functions of literals with a
  * self whose variable is named after the entry (`CONTRIBUTING.md`, "Terms",
  * module system), and the file's content read under the abstractions of its
  * directories and its own self, never alone: there is no special loader, and
  * the general interpreter reads the tree:
  *
  * {{{
  * directory e, entries c1 … ck:   ⟦e⟧ = λe. (λ"c1". ⟦c1⟧) + … + (λ"ck". ⟦ck⟧)     top when k = 0
  * file e.lambdalattice:            ⟦e⟧ = λe. M                                      M the file's content
  * }}}
  *
  * A member of a mixin X is taken by self-application, `X X "c"`; nothing
  * here resolves a name or a member: a reader applies the root to the keys
  * it wants and evaluates with the general weak-head evaluator.
  *
  * LAZY (after MIXINv2's `_mixin_directory.py`, which loads directories and
  * files as a lazy AST, so that a file is parsed on demand). Each entry is a URI node of the IR
  * (`NativeSpecializer.uri`) whose expansion (`expansion`) is its ENTRY UNIT, ⟦e⟧
  * abstracted once more over the selves of the directories d1 … dn above it:
  *
  * {{{
  * file:        U_e = λd1. … λdn. λe. M
  * directory:   U_e = λd1. … λdn. λe. (λ"c1". U_c1 d1 … dn e) + … + (λ"ck". U_ck d1 … dn e)
  * }}}
  *
  * so that `U_c d1 … dn e` is ⟦c⟧ by the β rule. A directory's expansion
  * lists the directory and writes each entry's unit as the entry's URI
  * node, so that it is made without reading any entry; a file's expansion
  * reads and parses the file. The front end thus defines the equation
  * between a URI node and the IR (`CONTRIBUTING.md`, "Terms", URI node).
  *
  * THE SCOPE IS THE URI'S. The mapping from a URI to the path of mixins is
  * the scheme's, not one rule for all; for `file:`, the levels count from the
  * file system's root, after the root's entry of the
  * scheme (`root`), so the mixin path of `file:///a/b/c.lambdalattice` is
  * file, a, b, c, its scope the root's self `uri`, then file, a, b and c,
  * and the expansion is a function of the URI alone. The path stays
  * absolute and no source path is configured, which would need a scheme of
  * its own: an entry is reached by the projections of its mixin path, which
  * the host can compute from the absolute path, off the tree's root.
  *
  * VISIBLE. What is configured is the visible subtree, a directory whose
  * entries alone the tree reaches (the corpora's directory, say): the path
  * stays absolute, and the ancestors' other entries are hidden. Each directory above it has one member, the
  * next level on the way down (`root`), so a projection off it checks one key
  * whatever the directory holds, and a key of another of its entries is a
  * miss, top, as any key no member has. The levels above stay in the scope, as
  * bound variables of the files below. A caller passes the visible subtree
  * with the path (`mixin`, `instance`), and a path outside it is
  * an error before anything is read.
  *
  * An entry is a file whose name ends in `.lambdalattice`, its key the name
  * without the extension, or a directory whose name does not start with
  * `.`, its key its name; other files are no entries. A file and a
  * directory of one key are two entries of that key, two members of the
  * directory's choice, so the key's mixin is the choice of both: the front
  * end joins several sources with `+`; a scheme whose key
  * has several sources joins them the same way. A key is a string
  * literal, so a projection reaches an entry whatever its spelling. Each
  * level of the scope is also a bound variable of the files under it, named
  * by the name that spells the level's name (`NameSpelling.escaped`, Scala's
  * `$` escape, which spells any non-empty text as a name). An
  * inner level shadows an outer one of the same name. A file whose text is malformed or uses a name outside its
  * scope throws `LambdalatticeMalformed` when it is expanded, not before.
  *
  * COST. Reading an entry expands every directory on its mixin path under
  * the visible subtree, and a directory's expansion lists it and makes one
  * member per entry, so a read costs time and space linear in the entries
  * of every such directory, whatever it reads below them; a level above the
  * subtree costs one key check. That is a cost of how the expansion is built
  * (`directoryUnit`), not of the term: a member stops being read at the first
  * bit of its key that differs from the key looked up.
  *
  * FIXME (2026-11-12): the error of a malformed file does not name the file: https://github.com/Atry/private-overlay/issues/1986
  * `Lambdalattice.termInScope` throws `LambdalatticeMalformed` with the
  * problem only, and this module catches nothing (no error is caught to be
  * recovered from or rethrown here). Candidate: `termInScope` takes a
  * description of the text's source and puts it in the exception it throws.
  *
  * SCHEMES. Only `file:` is read, a URL whose content is mutable: the reader
  * pins its expansion for one version of the contents by memoization (the
  * evaluator's `ReadingState.expansions`), and under a later version reads
  * the content again and builds the expansion only if it differs
  * (`expansionRead`). The rules that turn a `file:` URI into a
  * mixin path are the `file` scheme's own: the extension dropped, a
  * directory's key its name, dot entries and other files skipped (`keys`,
  * `entries`, `fileExpansionRead`); another scheme brings its own. A key may
  * stand for several URIs (a file and a directory of one key), so only a
  * directory's expansion knows the URIs under a key. A scheme is added as one more member of `root` and one more
  * case of `expansion`, which gives its URIs' mixin paths and expansions;
  * the evaluator, the IR and the
  * e-graph do not change. A source that is no plain file system, such as
  * sbt 2's `HashedVirtualFileRef`, would be such a scheme, its inputs hashed
  * by sbt. A scheme whose
  * content is immutable needs no memo; the reading state's memo of it then
  * only saves reading it again.
  */
object DirectoryTree:

  /** The name of the root's self, the first level of every scope, the
    * binder left of the schemes' keys: `λuri. λ"file". …`.
    */
  private val rootSelf: String = "uri"

  /** The root's key of the `file:` scheme, the first key of a `file:`
    * entry's mixin path and the second level of its scope.
    */
  private val fileScheme: String = "file"

  /** The tree's root, one entry per supported scheme, the scheme's name its
    * key and the first key of the mixin path: the root is not `file:///`,
    * `file` being one supported scheme among those to come, with only the visible
    * subtree's entries reachable under `file` (VISIBLE). For the visible
    * subtree /l1/…/lk:
    *
    * {{{
    * ⟦root⟧ = λuri. (λ"file". A_0 uri)
    * A_i    = λuri. λfile. λl1. … λli. (λ"l(i+1)". A_(i+1) uri file l1 … li)    for i < k
    * A_k    = U_file:///l1/…/lk/
    * }}}
    *
    * each A_i above the subtree a mixin unit of one member, the next level,
    * and the subtree itself its URI node, so nothing on disk is read until
    * the evaluator expands that node. A scheme added later is one more
    * member. Private: callers reach an entry by its path (`mixin`,
    * `instance`) and never build the root themselves.
    *
    * The root and the levels above the subtree are terms and no URI nodes.
    * The levels above it list one entry whatever the directory holds, so
    * they are no function of their URIs alone, which a URI node's expansion
    * must be; the subtree and every entry under it are URI nodes, each
    * a function of its URI. A URI node for the root would need a URI naming
    * the root, a scheme of its own, and no scheme is added for it.
    */
  private def root[C <: NativeSpecializer & Singleton](visible: Path)(using specializer: C): Configured[C] =
    val levels = segments(visible)
    def above(depth: Int): Configured[C] =
      if depth == levels.size then specializer.uri(visible.toAbsolutePath.normalize.toUri)
      else mixinUnit(Vector(levels(depth) -> above(depth + 1)), depth + 2)
    mixinUnit(Vector(fileScheme -> above(0)), 1)

  /** The mixin of the entry at the path, in the tree whose visible subtree
    * is `visible`: the projections of its keys off the tree's root
    * (`lookedUp`). Nothing is evaluated. Throws `IllegalArgumentException`
    * for a visible subtree that is no directory and for a path outside it.
    */
  def mixin[C <: NativeSpecializer & Singleton](visible: Path, path: Path)(using C): Configured[C] = lookedUp(visibleRoot(visible, path), keys(path))

  /** The root of the tree whose visible subtree is `visible`, for a reader
    * that joins other mixins with the tree at its root, as the Jupyter
    * kernel joins a notebook's cells. Nothing is evaluated. Throws `IllegalArgumentException` for a
    * visible subtree that is no directory.
    */
  def rootOf[C <: NativeSpecializer & Singleton](visible: Path)(using C): Configured[C] = visibleRoot(visible, visible)

  /** The root of the tree whose visible subtree is `visible`, after
    * checking that the path is under it.
    */
  private def visibleRoot[C <: NativeSpecializer & Singleton](visible: Path, path: Path)(using C): Configured[C] =
    val subtree = visible.toAbsolutePath.normalize
    if !Files.isDirectory(subtree) then throw IllegalArgumentException(s"a visible subtree that is no directory: $subtree")
    if !path.toAbsolutePath.normalize.startsWith(subtree) then
      throw IllegalArgumentException(s"$path is outside the visible subtree $subtree")
    root(subtree)

  /** The extension of a file entry. */
  val fileExtension: String = ".lambdalattice"

  /** The expansion of a URI node, the δ equation's right side: the unit of
    * the entry the URI locates, read now. A function of the URI alone; the
    * caller remembers it (the evaluator's reading state). Throws
    * `IllegalArgumentException` for a node that is no URI node, for a scheme
    * other than `file`, and for a path that is neither a directory nor a
    * file entry; and as reading a file does.
    */
  def expansion[C <: NativeSpecializer & Singleton](node: Configured[C])(using C): Configured[C] = expansionRead(node, None).expansion

  /** What the expansion of a URI node reads of the file system besides the
    * URI, the whole of its input: a directory's entries or a file's text.
    */
  enum ExpansionContent:
    case Listed(entries: Vector[Entry])
    case Written(text: String)

  /** A URI node's expansion with the content it was made from. */
  final case class ReadExpansion[C <: NativeSpecializer & Singleton](content: ExpansionContent, expansion: Configured[C])

  /** The expansion of the URI node read now, as `expansion` reads it, and
    * the content it is of. The content is always read; when it is the content
    * of `earlier`, an expansion of the same node, the expansion is a function
    * of what it was made from, so `earlier` itself is the answer and nothing
    * is built. Throws as `expansion` does.
    */
  def expansionRead[C <: NativeSpecializer & Singleton](node: Configured[C], earlier: Option[ReadExpansion[C]])(using C): ReadExpansion[C] =
    val uri = (node.layer: AnyRef) match
      case UriNode(address) => address
      case _                => throw IllegalArgumentException(s"no URI node: $node")
    uri.getScheme match
      case "file" => fileExpansionRead(uri, earlier)
      case _      => throw IllegalArgumentException(s"a URI of no scheme the front end reads: $uri")

  /** The enclosing names an entry's text is read under
    * (`Lambdalattice.termInScope`): the root's self `uri` and then the levels
    * of its mixin path (`keys`), each as a bound variable (`boundName`).
    * What a tool that respells a file reads it in, so that its names resolve
    * as the tree resolves them.
    */
  def scope(path: Path): Vector[String] =
    rootSelf +: keys(path).map(boundName)

  /** The expansion of a `file:` URI: its mixin path is `file` and then its
    * absolute path's levels from the file system's root (`keys`), and its
    * scope the root's self `uri` and then the mixin path's levels; a query
    * or a fragment is no part of it. `earlier` when its content is the one
    * read now (`expansionRead`).
    */
  private def fileExpansionRead[C <: NativeSpecializer & Singleton](uri: URI, earlier: Option[ReadExpansion[C]])(using C): ReadExpansion[C] =
    val path = Paths.get(uri.getPath)
    val content = fileContent(path).getOrElse(throw IllegalArgumentException(s"a URI that locates no entry: $uri"))
    earlier.filter(_.content == content).getOrElse {
      val scope = this.scope(path)
      ReadExpansion(
        content,
        content match
          case ExpansionContent.Listed(listed)  => directoryUnit(listed, scope)
          case ExpansionContent.Written(text) => fileUnit(text, scope)
      )
    }

  /** The content of the entry at the path now, none when it is no entry. */
  private def fileContent(path: Path): Option[ExpansionContent] =
    if Files.isDirectory(path) then Some(ExpansionContent.Listed(entries(path)))
    else if Files.isRegularFile(path) && path.getFileName.toString.endsWith(fileExtension) then
      Some(ExpansionContent.Written(Files.readString(path)))
    else None

  /** The keys looked up off the mixin by self-application,
    * `ω (… (ω (ω X k1) k2) …) kn` with `ω Y k` the application `Y Y k`, the
    * key a string literal spread into its elements (`Literals.arguments`).
    * Nothing is evaluated; X itself for no key.
    */
  def lookedUp[C <: NativeSpecializer & Singleton](mixin: Configured[C], keys: Vector[String])(using specializer: C): Configured[C] =
    keys.foldLeft(mixin)((current, key) =>
      val elements = Literals.arguments(Literal.text(key))
      // Each distinct element converted once, not once for each bit of the
      // key.
      val converted = elements.distinct.map(element => element -> Defunctionalization.thunkInstruction[C](element)).toMap
      elements.foldLeft(specializer.application(current, current))((function, element) =>
        specializer.application(function, converted.getOrElse(element, throw IllegalStateException(s"no conversion of $element")))
      )
    )

  /** The keys of the entry at the path off the root: the scheme `file`, then
    * the names of its absolute path's levels, a file's without the
    * extension.
    *
    * COST. Every level of the absolute path, from the file system's root
    * down, is a key looked up byte by byte at each member still alive, so a
    * read's cost
    * has two terms that depend on the checkout. MEASURED 2026-11-13 (a
    * scratch probe on 815c78ece, synthetic trees under the session's
    * scratchpad, an entry importing 0 to 8 files of a chain):
    *
    *  - the bytes term, 53 steps and 23 tables per byte of the visible
    *    subtree's path, all of it in the projection of the root to the
    *    visible subtree, which every entry and import of a read shares and
    *    which is read once, first, its cost reported apart
    *    (`gezi.standardlibrary.StandardLibrary.projected`); after it an
    *    entry read the same steps and tables at every length (1,749 and 763
    *    from 110 to 190 bytes, 9 levels, two imports);
    *  - the depth term, the design's cost: after the projection, about
    *    4 + 2 × (the imports) steps for each level above the visible
    *    subtree, the unit of each file reached being applied to the self of
    *    every level of its scope (`mixinUnit`): 1,749 steps at 9 levels and
    *    1,837 at 20 (two imports); 410 and 458 at 8 and 20 levels with no
    *    import; 4,411 and 4,651 with eight.
    *
    * Each import costs about 500 steps and 200 tables at a fixed path
    * (4,411 steps at eight imports against 410 at none, 8 levels).
    */
  private def keys(path: Path): Vector[String] =
    val levels = segments(path)
    fileScheme +: (if levels.isEmpty then levels else levels.init :+ levels.last.stripSuffix(fileExtension))

  /** The instance of the entry at the path: the projections of its keys
    * off the root (`mixin`) and one more
    * self-application, `new`. For a file, its content M with its scope bound
    * to the tree's mixins. The root is the whole tree, and an entry is its
    * projections along the path, each projection an instantiation by
    * self-application whose value is applied to a string: the entry
    * `library/my_directory/my_file` is
    * `new (new (new <root>.library).my_directory).my_file`, <root> the whole
    * source tree inlined. Nothing is evaluated. Throws as `mixin` does.
    */
  def instance[C <: NativeSpecializer & Singleton](visible: Path, path: Path)(using specializer: C): Configured[C] =
    val reached: Configured[C] = mixin(visible, path)
    specializer.application(reached, reached)

  /** The keys of the file entries of the directory, ordered. */
  def fileKeys(directory: Path): Vector[String] =
    entries(directory).filter(_.isFile).map(_.key)

  /** The content M of the file, read in its scope when M uses no name of
    * that scope: the file's term `U_e d1 … dn e` is then M by the β rule,
    * whatever the selves, so a data file is its content with no evaluation.
    * Throws `LambdaError` with `NotClosed` when M uses a name of its scope,
    * and as reading a file does.
    */
  def closedFile[C <: NativeSpecializer & Singleton](file: Path)(using C): Configured[C] =
    val scope = this.scope(file)
    Defunctionalization.thunkInstruction[C](bodyUnder(Lambdalattice.termInScope(scope, Files.readString(file)), scope.size))

  /** The term of a file whose content M names, of its scope, its directory
    * alone: the file's URI node applied to the directory's mixin at the
    * directory's level and to top at every other, which is M with that name
    * bound by the β rule. It reads nothing, and it is one term whatever the
    * file holds, the content being read when a reader expands the node, under
    * that reader's version of the contents. A content that uses another name
    * of the scope reads top there.
    */
  def entryOfItsDirectory[C <: NativeSpecializer & Singleton](file: Path)(using specializer: C): Configured[C] =
    val absolute = file.toAbsolutePath.normalize
    val directory = absolute.getParent
    val top = Defunctionalization.thunkInstruction[C](Literals.top)
    def appliedToTop(function: Configured[C], count: Int): Configured[C] =
      (1 to count).foldLeft(function)((applied, _) => specializer.application(applied, top))
    val directoryMixin = appliedToTop(specializer.uri(directory.toUri), scope(directory).size - 1)
    val belowDirectory = specializer.application(appliedToTop(specializer.uri(absolute.toUri), scope(absolute).size - 2), directoryMixin)
    specializer.application(belowDirectory, top)

  /** The names of the levels of the absolute path, from the file system's
    * root.
    */
  private def segments(path: Path): Vector[String] =
    val absolute = path.toAbsolutePath.normalize
    (0 until absolute.getNameCount).map(index => absolute.getName(index).toString).toVector

  /** The body under the term's first `count` abstractions. */
  @scala.annotation.tailrec
  private def bodyUnder(term: DeBruijnTerm, count: Int): DeBruijnTerm =
    if count == 0 then term
    else
      term match
        case DeBruijnTerm.Lambda(body) => bodyUnder(body, count - 1)
        case other => throw IllegalStateException(s"a file read in a scope of $count names is no abstraction: $other")

  /** An entry of a directory: its key, its path and whether it is a file. */
  final case class Entry(key: String, path: Path, isFile: Boolean)

  /** The entries of the directory, ordered by key, a file before a
    * directory of the same key, so that the directory's term is a function
    * of its contents and not of the order the file system lists them in.
    */
  private def entries(directory: Path): Vector[Entry] =
    val listed = Using.resource(Files.list(directory))(_.toScala(Vector))
    listed
      .flatMap { path =>
        val name = path.getFileName.toString
        if Files.isDirectory(path) then
          if name.startsWith(".") then None else Some(Entry(name, path, isFile = false))
        else if name.endsWith(fileExtension) then Some(Entry(name.stripSuffix(fileExtension), path, isFile = true))
        else None
      }
      .sortBy(entry => (entry.key, !entry.isFile))

  /** The name of a level as a bound variable of the files under it: the
    * name that spells the level's name (`NameSpelling.escaped`), the level's
    * name itself when the rule Name spells it.
    */
  private def boundName(key: String): String = NameSpelling.escaped(key)

  /** The unit of a file, `λd1. … λdn. λe. M`: the text read in the file's
    * scope.
    */
  private def fileUnit[C <: NativeSpecializer & Singleton](text: String, scope: Vector[String])(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](Lambdalattice.termInScope(scope, text))

  /** The unit of a directory of the entries:
    * `λd1. … λdn. λe. (λ"c1". U_c1 d1 … dn e) + … + (λ"ck". U_ck d1 … dn e)`,
    * each U_ci the URI node of the entry, or `λd1. … λdn. λe. top` for no
    * entry. The selves are passed on by position; the files read them by
    * their names.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/2156): this builds
    * the partial function of every entry to look up one key, though a look-up
    * reads a member only up to the first bit that differs, so the cost grows
    * with the bits of all the keys. Measured 2026-11-22
    * (`DirectoryExpansionBenchmarks`, `-prof gc`): the standard library's
    * directory, 32 entries of 3,464 bits, allocates 1.2 MB warmed up and
    * 40.8 MB in a fresh JVM. Candidate: build a member's bits when a reading
    * reaches them, with the term unchanged.
    */
  private def directoryUnit[C <: NativeSpecializer & Singleton](listed: Vector[Entry], scope: Vector[String])(using specializer: C): Configured[C] =
    mixinUnit(listed.map(entry => entry.key -> specializer.uri(entry.path.toAbsolutePath.normalize.toUri)), scope.size)

  /** The unit of a mixin whose members are the keys with their entries' URI
    * nodes, under `selves` abstractions:
    * `λd1. … λdn. λe. (λ"c1". U_c1 d1 … dn e) + … + (λ"ck". U_ck d1 … dn e)`,
    * or the abstractions over top for no member. Each `λ"c". …` is a curried
    * partial function (`Literals.partialFunction`), which takes the elements
    * of the key c one by one, so that a look-up (`lookedUp`) is a trie's: a
    * variable arguments partial function (`CONTRIBUTING.md`, "Terms").
    */
  private def mixinUnit[C <: NativeSpecializer & Singleton](members: Vector[(String, Configured[C])], selves: Int)(using C): Configured[C] =
    if members.size >= 2 then
      Defunctionalization.mixinInstruction(members.map((key, node) => Literal.text(key) -> node), selves)
    else
      val body =
        if members.isEmpty then Literals.top: DeBruijnTermOf[Configured[C]]
        else
          val partialFunctions = members.map { (key, node) =>
            // At the partial function's own depth, under the selves only, the
            // selves d1 … dn e are the indices selves − 1 down to 0.
            val applied = (selves - 1 to 0 by -1).foldLeft(DeBruijnTerm.Constant(node): DeBruijnTermOf[Configured[C]])((function, index) =>
              DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(index))
            )
            Literals.partialFunction(Literal.text(key), applied)
          }
          ChoiceSpine.nested[DeBruijnTermOf[Configured[C]]](partialFunctions, DeBruijnTerm.Choice(_, _))
      Defunctionalization.thunkInstruction[C]((1 to selves).foldLeft(body)((inner, _) => DeBruijnTerm.Lambda(inner)))
