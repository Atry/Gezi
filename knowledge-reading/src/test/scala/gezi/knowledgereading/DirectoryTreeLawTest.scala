package gezi.knowledgereading

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.net.URI
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.directorysugar.DirectoryTree
import gezi.frontend.Defunctionalization
import gezi.frontend.LambdaError
import gezi.frontend.Lambdalattice
import gezi.frontend.LambdalatticeMalformed
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import gezi.ir.Store
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead
import scala.jdk.StreamConverters.*
import scala.util.Try
import scala.util.Using
import gezi.ir

/** The laws of a directory tree read as one term (`DirectoryTree`), its
  * entries URI nodes the evaluator expands, on generated acyclic libraries
  * written to a fresh directory: a common directory `corpora` with groups
  * `group_g`, each holding modules `module_i.lambdalattice`. `corpora` is
  * reached by the projections of its absolute path off the tree's root
  * (`DirectoryTree.mixin`). A module binds the self-application locally, imports the first
  * member of earlier modules at its top through the common directory,
  * `omega (omega (omega corpora "group_h") "module_j") λd_j _.`, and
  * returns its members as a tuple (M18). A member is read under the tabled
  * evaluator that knows top, as knowledge is read.
  */
class DirectoryTreeLawTest extends GeneratedProperties:

  private type C = NoFacts.type

  private type Term = Configured[C]

  private given NoFacts.type = NoFacts

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of DirectoryTreeLawTest, "a member read through URI nodes is the member read off the whole tree", takes 7.485 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  /** A module: its group, the earlier modules it imports, its member count. */
  private final case class Module(group: Int, imports: Vector[Int], members: Int)

  private val libraries: Gen[Vector[Module]] =
    for
      groups <- Gen.int(Range.linear(1, 3))
      drawn <- (for
        group <- Gen.int(Range.linear(0, groups - 1))
        importMask <- Gen.int(Range.linear(0, 255))
        members <- Gen.int(Range.linear(1, 3))
      yield (group, importMask, members)).list(Range.linear(1, 6))
    yield drawn.toVector.zipWithIndex.map { case ((group, importMask, members), index) =>
      Module(group, (0 until index).toVector.filter(earlier => (importMask >> (earlier % 8) & 1) == 1), members)
    }

  private val limit: Long = 2000000

  private def groupName(group: Int): String = s"group_$group"

  private def moduleName(index: Int): String = s"module_$index"

  /** The binders of a tuple of the fields, the field of the position bound
    * to the name and the others to `_`.
    */
  private def binders(fields: Int, position: Int, name: String): String =
    (0 until fields).map(field => if field == position then name else "_").mkString(" ")

  private def importText(modules: Vector[Module], imported: Int): String =
    s"""omega (omega (omega corpora "${groupName(modules(imported).group)}") "${moduleName(imported)}") λ${binders(modules(imported).members, 0, s"d_$imported")}.\n"""

  private def moduleText(modules: Vector[Module], index: Int, imports: Vector[Int]): String =
    val module = modules(index)
    val body = imports.foldLeft("z")((inner, imported) => s"d_$imported ($inner)")
    val fields = (0 until module.members).map(member => s"(λz. ${"λy. " * member}$body)").mkString(" ")
    s"λexport. (λtuple. tuple λmixin. mixin mixin) λomega.\n${imports.map(importText(modules, _)).mkString}export $fields\n"

  /** The directory the libraries are written under: the forked test's
    * `target`, inside the build. Each library's `corpora` is the visible
    * subtree of its readings, so no directory above it is listed
    * (`DirectoryTree`, VISIBLE).
    */
  private val trees: Path = Files.createDirectories(Paths.get("target", "directory-tree-law").toAbsolutePath.normalize)

  /** The library written under a fresh directory, with the extra files given
    * by their paths under `corpora` and their texts; the path of `corpora`.
    */
  private def written(modules: Vector[Module], extra: Map[String, String]): Path =
    val common = Files.createTempDirectory(trees, "tree").resolve("corpora")
    val files = modules.indices.map(index =>
      s"${groupName(modules(index).group)}/${moduleName(index)}${DirectoryTree.fileExtension}" ->
        moduleText(modules, index, modules(index).imports)
    ) ++ extra
    files.foreach((relative, text) =>
      val path = common.resolve(relative)
      Files.createDirectories(path.getParent)
      Files.writeString(path, text)
    )
    common

  private def removed(common: Path): Unit =
    Using.resource(Files.walk(common.getParent))(_.toScala(Vector)).reverse.foreach(Files.delete)

  /** The modules a member of the module needs read: the module and, at its
    * top, the modules it imports, theirs in turn.
    */
  private def importClosure(modules: Vector[Module], index: Int): Set[Int] =
    modules(index).imports.toSet.flatMap(importClosure(modules, _)) + index

  /** The URIs of the URI nodes on the path to the common directory, which
    * is the visible subtree: the common directory's alone, since the levels
    * above it are no URI nodes (`DirectoryTree`, VISIBLE).
    */
  private def directoriesOnPath(common: Path): Set[URI] = Set(common.toUri)

  /** The reading of the field of the position of the module of the group,
    * whose tuple has the fields, off the common directory's mixin.
    */
  private def memberReading(corpora: Term, group: String, module: String, fields: Int, member: Int): Value[C] =
    val reader = Lambdalattice.term(
      s"""λcorpora. (λtuple. tuple λmixin. mixin mixin) λomega. omega (omega (omega corpora "$group") "$module") λ${binders(fields, member, "x")}. λq. q x"""
    )
    Value.Apply(Value.of(Defunctionalization.thunkInstruction(reader)(using NoFacts)), Value.of(corpora))

  /** The answers of the reading read back to the IR under the state, and
    * the state after it; nothing when the budget stops it.
    */
  private def answersFrom(reading: Value[C], state: ReadingState[C]): (Option[Set[Set[Term]]], ReadingState[C]) =
    WeakHead.heads(Mode.TablingWeakHead, reading).collected.result(state) match
      case Computed.Done(sets, after) =>
        (
          Some(
            sets
              .map(_.heads.map(head => Values.instruction(head.value)).toSet)
              .toSet
          ),
          after.nextReading(limit)
        )
      case Computed.Stopped(after) => (None, after.nextReading(limit))

  private def fresh: ReadingState[C] = ReadingState.knowing(limit, KnowledgeReading.knownExtremes, gezi.weakhead.ReadingConfiguration.withoutFacts)

  /** The answers of the reading under a fresh state. */
  private def answers(reading: Value[C]): Option[Set[Set[Term]]] = answersFrom(reading, fresh)._1

  /** The URIs of the URI nodes the state has expanded. */
  private def expandedUris(state: ReadingState[C]): Set[URI] = state.expansions.byNode.keySet.flatMap(_.uri)

  /** The readings read in order under one state, as the reads over one tree
    * share their tables and expansions, each with a fresh budget (no read
    * starts from a fresh state); each
    * reading's answers with the URIs it expanded that no earlier reading had.
    * Measured 2026-11-12 (scratch probe, one module of one member under
    * `target`): a read from a fresh state took 21,876 steps and 13,662
    * tables, about 0.6 to 0.9 s warm, almost all of it the directories on the
    * path from `/`; read again under the same state, 1 step.
    */
  private def readInOrder(
      readings: Vector[Value[C]],
      start: ReadingState[C]
  ): (Vector[(Option[Set[Set[Term]]], Set[URI])], ReadingState[C]) =
    readings.foldLeft((Vector.empty[(Option[Set[Set[Term]]], Set[URI])], start)) { case ((found, state), reading) =>
      val (read, after) = answersFrom(reading, state)
      (found :+ (read, expandedUris(after) -- expandedUris(state)), after)
    }

  /** Whether the URI is the common directory's or above or under it: the
    * URI nodes of the library and of the directories its path passes.
    */
  private def onPath(uri: URI, common: Path): Boolean =
    val commonUri = common.toUri.toString
    commonUri.startsWith(uri.toString) || uri.toString.startsWith(commonUri)

  /** The instruction with every URI node on the library's path replaced by
    * its expansion, all the way down; the other URI nodes (the other entries
    * of the directories above the library) left as they are, no reading
    * reaching them.
    */
  private def expandedWhole(term: Term, common: Path): Term =
    expandedSharing(term, common, Map.empty)._1

  /** `expandedWhole` with the terms already rewritten: a term is a graph
    * whose nodes are shared (`lookedUp` writes `X X k`, X twice), so a walk
    * that does not remember them rewrites a node once per path to it.
    * Measured 2026-11-12: without it, one library of one module under
    * `target` took 255,351 ms, the path's ten levels doubling the visits of
    * the directories above.
    */
  private def expandedSharing(
      term: Term,
      common: Path,
      rewritten: Map[Term, Term]
  ): (Term, Map[Term, Term]) =
    rewritten.get(term) match
      case Some(found) => (found, rewritten)
      case None =>
        def pair(
            left: Term,
            right: Term,
            make: (Term, Term) => Term
        ): (Term, Map[Term, Term]) =
          val (leftRewritten, afterLeft) = expandedSharing(left, common, rewritten)
          val (rightRewritten, afterRight) = expandedSharing(right, common, afterLeft)
          (make(leftRewritten, rightRewritten), afterRight)
        val (result, after) = term.uri match
          case Some(uri) if onPath(uri, common) => expandedSharing(DirectoryTree.expansion(term), common, rewritten)
          case Some(_)                          => (term, rewritten)
          case None =>
            term.layer match
              case gezi.ir.Apply(function, argument) => pair(function, argument, NoFacts.application(_, _))
              case gezi.ir.Parallel(left, right)     => pair(left, right, NoFacts.parallel(_, _))
              case gezi.ir.Choice(left, right)       => pair(left, right, NoFacts.choice(_, _))
              case gezi.ir.Thunk(code, holes, fillings) =>
                val (fillingsRewritten, afterFillings) =
                  fillings.foldLeft((Vector.empty[Term], rewritten)) { case ((done, current), filling) =>
                    val (fillingRewritten, next) = expandedSharing(filling, common, current)
                    (done :+ fillingRewritten, next)
                  }
                val present = NonEmptyHoles.of(holes).getOrElse(throw IllegalStateException(s"a thunk term has no hole: $term"))
                (NoFacts.thunk(code, present, fillingsRewritten), afterFillings)
              case _ => (term, rewritten)
        (result, after.updated(term, result))

  /** The URIs of the URI nodes the term holds, read as syntax. */
  private def urisIn(term: Term): Set[URI] =
    term.uri match
      case Some(uri) => Set(uri)
      case None =>
        term.layer match
          case gezi.ir.Apply(function, argument) => urisIn(function) ++ urisIn(argument)
          case gezi.ir.Parallel(left, right)     => urisIn(left) ++ urisIn(right)
          case gezi.ir.Choice(left, right)       => urisIn(left) ++ urisIn(right)
          case gezi.ir.Thunk(_, _, fillings)     => fillings.toSet.flatMap(urisIn)
          case _                                 => Set.empty

  /** Catches a reading through URI nodes that differs from the reading of
    * the same tree expanded whole: a URI node expanded to the wrong unit, a
    * directory term whose selves or units are passed in the wrong order, a
    * file read in the wrong scope. Each member of each module read off the
    * root of URI nodes has the answers it has off the tree with every URI
    * node on the library's path replaced by its expansion, and one parallel
    * set. Catches also a reading that expands more than it needs, which the
    * lazy tree exists to prevent, lest the whole file system be read: with
    * the members read in order under one state, each reading
    * newly expands only URIs it needs, the directories on the path to the
    * common directory and the groups and files of its module's import
    * closure, and all the readings together expand exactly the union of what
    * they need.
    */
  property("a member read through URI nodes is the member read off the whole tree", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val common = written(modules, Map.empty)
      val lazily: Term = DirectoryTree.mixin(common, common)
      val whole: Term = expandedWhole(lazily, common)
      val onPath = directoriesOnPath(common)
      val members = for
        index <- modules.indices.toVector
        member <- (0 until modules(index).members).toVector
      yield (index, member)
      def reading(corpora: Term, index: Int, member: Int): Value[C] =
        memberReading(corpora, groupName(modules(index).group), moduleName(index), modules(index).members, member)
      def needed(index: Int): Set[URI] =
        onPath ++ importClosure(modules, index).flatMap(imported =>
          val directory = common.resolve(groupName(modules(imported).group))
          Set(directory.toUri, directory.resolve(moduleName(imported) + DirectoryTree.fileExtension).toUri)
        )
      val (lazyReads, lazyState) = readInOrder(members.map(reading(lazily, _, _)), fresh)
      val (wholeReads, _) = readInOrder(members.map(reading(whole, _, _)), fresh)
      val results = members.zip(lazyReads.zip(wholeReads)).toList.map { case ((index, member), ((read, expanded), (readWhole, _))) =>
        Result
          .all(
            List(
              Result.diff(read, readWhole)(_ == _),
              Result.assert(read.exists(_.size == 1)),
              Result.assert(expanded.subsetOf(needed(index))).log(s"expanded: $expanded")
            )
          )
          .log(s"${groupName(modules(index).group)}/${moduleName(index)} member_$member")
      }
      // Before the tree is removed: a directory's URI ends in `/` only while
      // the directory exists (`Path.toUri`).
      val neededByAll = members.map(_._1).toSet.flatMap(needed)
      removed(common)
      Result.all(Result.diff(expandedUris(lazyState), neededByAll)(_ == _) :: results)
  }

  /** Catches a readback that reads through a URI node: a member whose body
    * captures the common directory `corpora`, the visible subtree, reads
    * back to a term whose one URI node is that of `corpora`, unexpanded; a
    * malformed file in the tree, which an expansion of `corpora`'s subtree
    * would parse, leaves the reading and the readback as they are; the
    * reading expands `corpora`, `group_capture` and the capturing file, and
    * nothing else.
    */
  property("a head that captures a directory reads back to the directory's URI node", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val common = written(
        modules,
        Map(
          s"group_capture/capturing${DirectoryTree.fileExtension}" -> """λexport. export (λz. corpora)""",
          s"${groupName(0)}/broken${DirectoryTree.fileExtension}" -> "λ"
        )
      )
      val (read, after) = answersFrom(memberReading(DirectoryTree.mixin(common, common), "group_capture", "capturing", 1, 0), fresh)
      val uris = read.toList.flatMap(_.toList.flatMap(_.toList.flatMap(urisIn)))
      val capturing = common.resolve("group_capture")
      // Before the tree is removed: a directory's URI ends in `/` only while
      // the directory exists (`Path.toUri`).
      val onPath = directoriesOnPath(common)
      val needed = onPath ++ Set(capturing.toUri, capturing.resolve(s"capturing${DirectoryTree.fileExtension}").toUri)
      val expanded = after.expansions.byNode.keySet.flatMap(_.uri)
      removed(common)
      Result.all(
        List(
          Result.assert(read.exists(_.size == 1)).log(s"read: $read"),
          Result.diff(expanded, needed)(_ == _),
          Result.diff(uris.toSet, onPath)(_ == _).log(s"URIs read back: $uris"),
          Result.assert(uris.forall(uri => !uri.getPath.endsWith(DirectoryTree.fileExtension))).log(s"URIs read back: $uris")
        )
      )
  }

  /** Catches a URI whose expansion is not pinned within a reading state:
    * with one state threaded through the readings, each member reads the
    * same after every module file is overwritten with malformed text, since
    * the state remembers each expansion (`ReadingState.expansions`) and its
    * tables.
    */
  property("a file's content is pinned for the reading state", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val common = written(modules, Map.empty)
      val corpora: Term = DirectoryTree.mixin(common, common)
      val readings = for
        index <- modules.indices.toVector
        member <- (0 until modules(index).members).toVector
      yield memberReading(corpora, groupName(modules(index).group), moduleName(index), modules(index).members, member)
      def readAll(start: ReadingState[C]): (Vector[Option[Set[Set[Term]]]], ReadingState[C]) =
        readings.foldLeft((Vector.empty[Option[Set[Set[Term]]]], start)) { case ((found, state), reading) =>
          val (read, after) = answersFrom(reading, state)
          (found :+ read, after)
        }
      val (before, state) = readAll(fresh)
      modules.indices.foreach(index =>
        Files.writeString(common.resolve(s"${groupName(modules(index).group)}/${moduleName(index)}${DirectoryTree.fileExtension}"), "λ")
      )
      val (after, _) = readAll(state)
      removed(common)
      Result.all(List(Result.diff(after, before)(_ == _), Result.assert(before.forall(_.exists(_.size == 1)))))
  }

  /** Catches a URI node the e-graph would read through, and two files of one
    * content whose expansions differ: the e-graph's store makes a URI node a
    * leaf (`Store.expanded`), and the expansions of a module and of its copy
    * under another group, the two sides of the δ equations that would relate
    * the two nodes, are one instruction.
    */
  property("files of one content at different URIs have one expansion", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val last = modules.size - 1
      val text = moduleText(modules, last, modules(last).imports)
      val common = written(modules, Map(s"group_copy/${moduleName(last)}${DirectoryTree.fileExtension}" -> text))
      val original = NoFacts.uri(common.resolve(s"${groupName(modules(last).group)}/${moduleName(last)}${DirectoryTree.fileExtension}").toUri)
      val copy = NoFacts.uri(common.resolve(s"group_copy/${moduleName(last)}${DirectoryTree.fileExtension}").toUri)
      val expansions = (DirectoryTree.expansion(original), DirectoryTree.expansion(copy))
      removed(common)
      Result.all(
        List(
          Result.assert(!Configured.same(original, copy)),
          Result.diff(expansions._1, expansions._2)(Configured.same(_, _)),
          Result.diff(Store(Set.empty[Term], gezi.ir.TermConstruction(NoFacts)).expanded(original), ir.NoinlineLeaf(original))(_ == _)
        )
      )
  }

  /** Catches a tree that reads more than a reading needs: a file no reading
    * reaches is never parsed, so a malformed one beside the library leaves
    * every member readable; reading that file's member throws.
    */
  property("a malformed file no reading reaches is never read", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val common = written(modules, Map(s"${groupName(0)}/broken${DirectoryTree.fileExtension}" -> "λ"))
      val corpora: Term = DirectoryTree.mixin(common, common)
      val (reads, state) =
        readInOrder(
          modules.indices.toVector.map(index => memberReading(corpora, groupName(modules(index).group), moduleName(index), modules(index).members, 0)),
          fresh
        )
      val members = reads.toList.map((read, _) => Result.assert(read.exists(_.nonEmpty)))
      val broken = Try(answersFrom(memberReading(corpora, groupName(0), "broken", 1, 0), state)._1).toEither
      removed(common)
      Result.all(
        Result.assert(broken.left.exists(_.isInstanceOf[LambdalatticeMalformed])).log(s"broken: $broken") :: members
      )
  }

  /** Catches a tree whose files are not one term by content: a module copied
    * under another group, its text the same, gives every member the same
    * answers read back to the IR as the original; and a copy under a group
    * whose name the rule Name does not spell is reached by projection all
    * the same.
    */
  property("a file of the same content under another directory gives the same members", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val last = modules.size - 1
      val text = moduleText(modules, last, modules(last).imports)
      val common = written(
        modules,
        Map(
          s"group_copy/${moduleName(last)}${DirectoryTree.fileExtension}" -> text,
          s"group-unnamed/${moduleName(last)}${DirectoryTree.fileExtension}" -> text
        )
      )
      val corpora: Term = DirectoryTree.mixin(common, common)
      val groups = Vector(groupName(modules(last).group), "group_copy", "group-unnamed")
      val (reads, _) = readInOrder(
        (0 until modules(last).members).toVector.flatMap(member =>
          groups.map(memberReading(corpora, _, moduleName(last), modules(last).members, member))
        ),
        fresh
      )
      val results = reads.map(_._1).grouped(groups.size).toList.flatMap {
        case Vector(original, copied, unnamed) =>
          List(Result.diff(copied, original)(_ == _), Result.diff(unnamed, original)(_ == _))
        case other => List(Result.failure.log(s"not three readings: $other"))
      }
      removed(common)
      Result.all(results)
  }

  /** Catches a data file read in the wrong scope or with its scope's
    * binders left on (`DirectoryTree.closedFile`): a module that imports
    * nothing uses no name of its scope and is the term of its text read
    * alone; a module that imports uses `corpora` and is refused.
    */
  property("a file that uses no name of its scope is its content", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val common = written(modules, Map.empty)
      val results = modules.indices.toList.map { index =>
        val read = Try[Term](
          DirectoryTree.closedFile(common.resolve(s"${groupName(modules(index).group)}/${moduleName(index)}${DirectoryTree.fileExtension}"))
        ).toEither
        if modules(index).imports.isEmpty then
          val expected = Defunctionalization.thunkInstruction(Lambdalattice.term(moduleText(modules, index, Vector.empty)))(using NoFacts)
          Result
            .assert(read.toOption.exists(Configured.same(_, expected)))
            .log(s"read: $read")
        else Result.assert(read.left.exists(_.isInstanceOf[LambdaError])).log(s"read: $read")
      }
      removed(common)
      Result.all(results)
  }

  /** Catches a cyclic import that does not stop: a module that imports its
    * own first member gives no parallel set within the budget, whether the
    * tables close the cycle or the budget stops it.
    */
  /** Catches an entry above the visible subtree that a reading still
    * reaches, when only the files under the visible subtree may be reached: a module
    * that imports a member of a file beside the common directory, through
    * the variable of the directory both stand in, gives no answer when the
    * common directory is the visible subtree, and that member when the
    * directory above it is; with the common directory visible, every URI
    * node expanded is under it.
    */
  property("an entry beside the visible subtree is not reached", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val common = written(modules, Map.empty)
      // The directory above corpora is a fresh temporary directory, `tree`
      // followed by digits, a name the files under it can refer to.
      val parent = common.getParent.getFileName.toString
      val reaching = common.resolve(s"group_beside/reaching${DirectoryTree.fileExtension}")
      Files.createDirectories(reaching.getParent)
      Files.writeString(reaching, s"""λexport. (λtuple. tuple λmixin. mixin mixin) λomega.\nomega (omega $parent "beside") λx.\nexport x\n""")
      Files.writeString(common.getParent.resolve(s"beside${DirectoryTree.fileExtension}"), """λexport. export (λz. z)""")
      val (hidden, afterHidden) = answersFrom(memberReading(DirectoryTree.mixin(common, common), "group_beside", "reaching", 1, 0), fresh)
      val shown = answers(memberReading(DirectoryTree.mixin(common.getParent, common), "group_beside", "reaching", 1, 0))
      val expanded = expandedUris(afterHidden)
      removed(common)
      Result.all(
        List(
          Result.assert(hidden.exists(_.isEmpty)).log(s"read with corpora visible: $hidden"),
          Result.assert(shown.exists(_.size == 1)).log(s"read with the directory above visible: $shown"),
          Result.assert(expanded.forall(_.toString.startsWith(common.toUri.toString))).log(s"expanded: $expanded")
        )
      )
  }

  property("a module that imports itself gives no answer", _.copy(testLimit = 8)) {
    for modules <- libraries.forAll
    yield
      val last = modules.size - 1
      val module = modules(last)
      val cyclic = s"${groupName(module.group)}/${moduleName(last)}${DirectoryTree.fileExtension}"
      val common = written(modules, Map(cyclic -> moduleText(modules, last, module.imports :+ last)))
      val read = answers(memberReading(DirectoryTree.mixin(common, common), groupName(module.group), moduleName(last), module.members, 0))
      removed(common)
      Result.assert(read.forall(_.isEmpty)).log(s"read: $read")
  }
