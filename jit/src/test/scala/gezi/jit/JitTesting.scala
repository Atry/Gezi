package gezi.jit

import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import gezi.frontend.Term
import gezi.frontend.TermOf
import java.nio.file.Files
import java.nio.file.LinkOption
import java.nio.file.Path
import gezi.weakhead.Bounded
import gezi.weakhead.Computed
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.JitEvaluator
import gezi.weakhead.ParallelSet
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingConfiguration
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead
import gezi.standardlibrary.SplitMix
import gezi.standardlibrary.StandardLibraryIndex
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import scala.jdk.CollectionConverters.*
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** A bounded reading's outcome and the JIT state it left, which the next
  * reading of a suite starts from.
  */
final case class Read[C <: NativeSpecializer & Singleton, Result](outcome: Bounded[Result], jitState: JitState[C])

/** The verdicts of the comparison protocol of `gezi/tests/jit.plt`
  * (compared_with/5).
  */
enum Verdict:
  case Agreed
  case AgreedWithMore
  case ReferenceOnly
  case JitOnly
  case NeitherFinished

/** What the tests of the JIT share: bounded readings under the reference
  * and the JIT, the JIT's state kept from one reading to the next or not,
  * the comparison protocol, the random closed terms with choices and
  * parallels, and the files of a tree.
  *
  * A reading is of one configuration `C`: the native specializer of a
  * `StorageEncoding` (`BackendFacts.storageEncoding`), whose singleton type a
  * test names by binding the encoding to a `val` and writing `encoding.type`.
  * A term, a value and a JIT state of a reading are all of that `C`.
  */
object JitTesting:

  /** The pool's object of a storage the encoding made. */
  def interned[E <: StorageEncoding & Singleton](encoding: E)(storage: RepresentedStorage[JitValue[E]] | GroupStorage[JitValue[E]]): JitValue[E] =
    given E = encoding
    Value.of(encoding.operations.stored(storage))

  /** The storage of the value in the representation under the encoding (`RepresentedStorage.apply`). */
  def storageOf[E <: StorageEncoding & Singleton](encoding: E)(representation: Representation[JitValue[E]], value: NativeValue[JitValue[E]]): RepresentedStorage[JitValue[E]] =
    RepresentedStorage[E](encoding, representation, value)

  /** The pool's value of the native value in the representation under the encoding: its storage interned. */
  def valueOfNative[E <: StorageEncoding & Singleton](encoding: E)(representation: Representation[JitValue[E]], value: NativeValue[JitValue[E]]): JitValue[E] =
    interned(encoding)(storageOf(encoding)(representation, value))

  /** The parallel of the two values, converted into its storage when it is the unique spelling of one. */
  def parallelOfValues[E <: StorageEncoding & Singleton](encoding: E)(left: JitValue[E], right: JitValue[E]): JitValue[E] =
    Value.parallel(encoding)(left, right)

  /** The criterion the representation names under the encoding's facts. */
  def criterionOf[E <: StorageEncoding & Singleton](encoding: E)(representation: Representation[JitValue[E]]): JitValue[E] =
    encoding.operations.criterionOf(representation)

  /** The facts of no library: no native and no backend fact, the index of
    * the Prolog tests' empty library.
    */
  val noFacts: BackendFacts =
    BackendFacts(StandardLibraryIndex(Vector.empty, Vector.empty, Vector.empty, Vector.empty))

  /** The encoding of `noFacts`, whose singleton type is the configuration of the tests that read no facts. */
  lazy val noFactsEncoding: StorageEncoding = noFacts.storageEncoding

  /** The data file of the library terms the JIT's tests build their
    * programs from, under Gezi's directory (`TermTables.jitLibraryTerms`):
    * a Scott tuple of library files' members, each imported at the file's
    * top. Only these tests read it.
    */
  val libraryTermsFile: String = TermTables.jitLibraryTerms.file

  /** The members of `libraryTermsFile`, each a closed term read with no facts by
    * projection (`StandardLibrary.entryMembers`).
    */
  lazy val libraryTerms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary.entryMembers(LibraryFiles.buildRoot, TermTables.jitLibraryTerms, Expansions.none)._1

  /** The library term of the key as a closed HOAS term (`Term.Closed`): no
    * name, the term itself in the configuration.
    */
  def libraryTerm[C <: NativeSpecializer & Singleton](key: String)(using C): TermOf[Configured[C]] =
    Term.closed(libraryInstruction[C](key))

  /** The library term of the key in the configuration, its parallels converted by the specializer. Throws
    * `IllegalArgumentException` for a key `libraryTermsFile` has no member
    * of.
    */
  def libraryInstruction[C <: NativeSpecializer & Singleton](key: String)(using specializer: C): Configured[C] =
    val read = libraryTerms.getOrElse(key, throw IllegalArgumentException(s"$libraryTermsFile has no member $key"))
    specializer.crossedAllFromNoFacts(Vector(read))(read)

  /** The library terms of the native route's library (native_types and
    * native_arithmetic) that a generated program of the dispatch tests is
    * built over (`HoasGenerators.openTermOver`): the naturals, booleans,
    * lists and combinators.
    */
  def nativeRouteLeaves[C <: NativeSpecializer & Singleton](using C): Vector[TermOf[Configured[C]]] = Vector(
    "zero", "successor", "nat_fold", "nat_type", "true", "false", "boolean_type", "boolean_not", "nil", "cons",
    "list_type", "list_fold", "konstant", "fixpoint", "compose", "double", "even"
  ).map(libraryTerm[C])

  /** Whether the two sequences of terms hold the same terms in the same order, each compared by `Configured.same`. */
  def sameTerms[C <: NativeSpecializer & Singleton](left: Vector[Configured[C]], right: Vector[Configured[C]])(using C): Boolean =
    left.size == right.size && left.zip(right).forall((first, second) => Configured.same(first, second))

  /** Whether two bounded readings of normal forms ended alike: both stopped the same way, or both finished with the
    * same terms in the same order.
    */
  def sameOutcomes[C <: NativeSpecializer & Singleton](left: Bounded[Vector[Configured[C]]], right: Bounded[Vector[Configured[C]]])(using C): Boolean =
    (left, right) match
      case (Bounded.Finished(first), Bounded.Finished(second)) => sameTerms(first, second)
      case (Bounded.Finished(_), _) | (_, Bounded.Finished(_)) => false
      case _                                                   => left.productPrefix == right.productPrefix

  /** The term of no facts in the encoding's configuration: its parallels converted by the encoding. */
  def instructionCrossed[E <: StorageEncoding & Singleton](encoding: E)(term: Configured[NoFacts.type]): Configured[E] =
    encoding.crossedAllFromNoFacts(Vector(term))(term)

  /** The configuration of the encoding under the budget and the strategy. */
  def configured[E <: StorageEncoding & Singleton](encoding: E, budget: Int, strategy: GenerationStrategy = PredicatePerCode): JitConfiguration[E] =
    JitConfiguration[E](encoding, budget, strategy, ClosureBackend, DispatchMode.NoDispatch, instanceTable = false, storageAccess = gezi.ir.StorageAccess.granted())

  /** The plain values of the instructions, every code interned. */
  def valuesOf[C <: NativeSpecializer & Singleton](instructions: Vector[Configured[C]])(using C): Vector[Value[C]] =
    instructions.map(Values.ofInstruction(_, Set.empty))

  /** The IR of a closed de Bruijn term with no library name. */
  def instructionOf[C <: NativeSpecializer & Singleton](term: DeBruijnTerm)(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](term)

  /** The plain value of a closed HOAS term, whose library terms are
    * `Term.Closed` instructions (`libraryTerm`), so that no name is resolved: the
    * term converted to one thunk. Throws as the conversion does for a term with a free name.
    */
  def termValue[C <: NativeSpecializer & Singleton](term: TermOf[Configured[C]])(using C): Value[C] =
    instructionValue(termInstruction(term))

  /** The IR of a closed HOAS term as written, neither tagged nor typed: the
    * term converted to one thunk, its library terms (`libraryTerm`) the
    * instructions they hold. Throws as the conversion does for a term with a free
    * name.
    */
  def termInstruction[C <: NativeSpecializer & Singleton](term: TermOf[Configured[C]])(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](term.deBruijnTerm(Map.empty))

  /** The plain value of an instruction. */
  def instructionValue[C <: NativeSpecializer & Singleton](instruction: Configured[C])(using C): Value[C] =
    Values.ofInstruction(instruction, Set.empty)

  /** The configuration of the readings of the encoding that run no JIT: the encoding's specializer and a capability. */
  def plainConfiguration[E <: StorageEncoding & Singleton](encoding: E): ReadingConfiguration[E] =
    ReadingConfiguration[E](encoding, gezi.ir.StorageAccess.granted())

  /** The configuration of the readings that run no JIT: the reference's, under the JIT's specializer and capability. */
  def referenceConfiguration[C <: NativeSpecializer & Singleton](evaluator: Jit[C]): ReadingConfiguration[C] =
    ReadingConfiguration[C](evaluator.configuration.specializer, evaluator.configuration.storageAccess)

  /** Every parallel set of the value under the mode, its heads plain, within
    * the limit, the reading under the configuration starting from the JIT state given.
    */
  def headsRead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      configuration: ReadingConfiguration[C],
      value: Value[C],
      limit: Long,
      jitState: JitState[C] = NoJitState
  )(using C): Read[C, Vector[ParallelSet[C]]] =
    WeakHead.heads(mode, value).collected.result(ReadingState.fresh(limit, configuration).copy(jitState = jitState)) match
      case Computed.Done(heads, after) => Read(Bounded.Finished(heads), after.jitState)
      case Computed.Stopped(after)     => Read(EvaluatorTesting.stopped(after), after.jitState)

  /** `headsRead` under the JIT's own reading configuration (`Mode.Jit`). */
  def headsRead[C <: NativeSpecializer & Singleton](evaluator: Jit[C], value: Value[C], limit: Long)(using C): Read[C, Vector[ParallelSet[C]]] =
    headsRead(Mode.Jit, evaluator.readingConfiguration, value, limit)

  /** `headsRead` under the JIT's own reading configuration (`Mode.Jit`), from the JIT state given. */
  def headsRead[C <: NativeSpecializer & Singleton](evaluator: Jit[C], value: Value[C], limit: Long, jitState: JitState[C])(using C): Read[C, Vector[ParallelSet[C]]] =
    headsRead(Mode.Jit, evaluator.readingConfiguration, value, limit, jitState)

  /** The distinct normal forms of the value under the mode, sorted by their
    * text, within the limit, the reading under the configuration starting from the JIT state given.
    */
  def normalFormsRead[C <: NativeSpecializer & Singleton](
      mode: Mode,
      configuration: ReadingConfiguration[C],
      value: Value[C],
      limit: Long,
      jitState: JitState[C] = NoJitState
  )(using C): Read[C, Vector[Configured[C]]] =
    NormalForms.normalForms(mode, value).result(ReadingState.fresh(limit, configuration).copy(jitState = jitState)) match
      case Computed.Done(normalForms, after) => Read(Bounded.Finished(normalForms.sorted(gezi.ir.ContentComparison.ordering)), after.jitState)
      case Computed.Stopped(after)           => Read(EvaluatorTesting.stopped(after), after.jitState)

  /** `normalFormsRead` under the JIT's own reading configuration (`Mode.Jit`). */
  def normalFormsRead[C <: NativeSpecializer & Singleton](evaluator: Jit[C], value: Value[C], limit: Long)(using C): Read[C, Vector[Configured[C]]] =
    normalFormsRead(Mode.Jit, evaluator.readingConfiguration, value, limit)

  /** `normalFormsRead` under the JIT's own reading configuration (`Mode.Jit`), from the JIT state given. */
  def normalFormsRead[C <: NativeSpecializer & Singleton](evaluator: Jit[C], value: Value[C], limit: Long, jitState: JitState[C])(using C): Read[C, Vector[Configured[C]]] =
    normalFormsRead(Mode.Jit, evaluator.readingConfiguration, value, limit, jitState)

  /** A reading of a question: its reference reading and its JIT reading. */
  trait Question[C <: NativeSpecializer & Singleton, Result]:
    def reference(limit: Long): Bounded[Result]
    def jit(limit: Long, jitState: JitState[C]): Read[C, Result]

  /** The heads of the value as the question, compared as a set of parallel
    * sets: a weak head's answer is a set of sets of abstractions, each
    * parallel set once, so a reader that gives one parallel set twice gives the same answer.
    */
  def headsQuestion[C <: NativeSpecializer & Singleton](evaluator: Jit[C], value: Value[C])(using C): Question[C, Set[ParallelSet[C]]] = new Question[C, Set[ParallelSet[C]]]:
    def reference(limit: Long) = asSet(headsRead(Mode.TablingWeakHead, referenceConfiguration(evaluator), value, limit).outcome)
    def jit(limit: Long, jitState: JitState[C]) =
      val read = headsRead(evaluator, value, limit, jitState)
      Read(asSet(read.outcome), read.jitState)

  private def asSet[C <: NativeSpecializer & Singleton](outcome: Bounded[Vector[ParallelSet[C]]]): Bounded[Set[ParallelSet[C]]] = outcome match
    case Bounded.Finished(sets)      => Bounded.Finished(sets.toSet)
    case Bounded.Exceeded            => Bounded.Exceeded
    case Bounded.Exhausted(resource) => Bounded.Exhausted(resource)

  /** The normal forms of the value as the question. */
  def normalFormsQuestion[C <: NativeSpecializer & Singleton](evaluator: Jit[C], value: Value[C])(using C): Question[C, Vector[Configured[C]]] =
    new Question[C, Vector[Configured[C]]]:
      def reference(limit: Long) = normalFormsRead(Mode.TablingWeakHead, referenceConfiguration(evaluator), value, limit).outcome
      def jit(limit: Long, jitState: JitState[C]) = normalFormsRead(evaluator, value, limit, jitState)

  /** The outcome of the protocol on one question: the verdict, the two
    * answers when both finished and differ (the JIT's, then the
    * reference's), and the JIT state the last JIT reading left.
    */
  final case class Comparison[C <: NativeSpecializer & Singleton, Result](verdict: Verdict, disagreement: Option[(Result, Result)], jitState: JitState[C])

  /** The JIT's reading of the question against the reference's within the
    * limit, by the protocol of jit.plt (compared_with/5): both finished,
    * their answers are compared; one finished, the other is read again
    * within four times the limit plus 100,000 and compared when it finishes
    * then. A disagreement is returned, not thrown, for a property that
    * reports it as its result (`compared` throws it).
    */
  def comparison[C <: NativeSpecializer & Singleton, Result](
      question: Question[C, Result],
      limit: Long,
      jitState: JitState[C],
      cacheDropped: Boolean
  ): Comparison[C, Result] =
    val start: JitState[C] = if cacheDropped then NoJitState else jitState
    val reference = question.reference(limit)
    val jitRead = question.jit(limit, start)
    val larger = 4 * limit + 100000
    def judged(verdict: Verdict, answers: Result, expected: Result, after: JitState[C]): Comparison[C, Result] =
      Comparison(verdict, Option.when(answers != expected)((answers, expected)), after)
    (reference, jitRead.outcome) match
      case (Bounded.Finished(expected), Bounded.Finished(answers)) =>
        judged(Verdict.Agreed, answers, expected, jitRead.jitState)
      case (Bounded.Finished(expected), _) =>
        val again = question.jit(larger, if cacheDropped then NoJitState else jitRead.jitState)
        again.outcome match
          case Bounded.Finished(answers) => judged(Verdict.AgreedWithMore, answers, expected, again.jitState)
          case _                         => Comparison(Verdict.ReferenceOnly, None, again.jitState)
      case (_, Bounded.Finished(answers)) =>
        question.reference(larger) match
          case Bounded.Finished(expected) => judged(Verdict.AgreedWithMore, answers, expected, jitRead.jitState)
          case _                          => Comparison(Verdict.JitOnly, None, jitRead.jitState)
      case _ => Comparison(Verdict.NeitherFinished, None, jitRead.jitState)

  /** `comparison`, the one check that fails a test: a disagreement throws
    * `AssertionError` with the two answers. The verdict, and the JIT state
    * the last JIT reading left.
    */
  def compared[C <: NativeSpecializer & Singleton, Result](
      question: Question[C, Result],
      limit: Long,
      jitState: JitState[C],
      cacheDropped: Boolean
  ): (Verdict, JitState[C]) =
    val found = comparison(question, limit, jitState, cacheDropped)
    found.disagreement.foreach((answers, expected) =>
      throw AssertionError(s"the JIT read $answers where the reference read $expected")
    )
    (found.verdict, found.jitState)

  /** The verdicts of the questions in order, the JIT state kept from one to
    * the next unless the cache is dropped before each.
    */
  def allCompared[C <: NativeSpecializer & Singleton, Result](questions: Vector[Question[C, Result]], limit: Long, cacheDropped: Boolean): Vector[Verdict] =
    allComparedAndState(questions, limit, cacheDropped)._1

  /** `allCompared`, with the JIT state the last question left. */
  def allComparedAndState[C <: NativeSpecializer & Singleton, Result](
      questions: Vector[Question[C, Result]],
      limit: Long,
      cacheDropped: Boolean
  ): (Vector[Verdict], JitState[C]) =
    questions
      .foldLeft((Vector.empty[Verdict], NoJitState: JitState[C])) { case ((verdicts, jitState), question) =>
        val (verdict, after) = compared(question, limit, jitState, cacheDropped)
        (verdicts :+ verdict, after)
      }

  /** The codes the JIT state holds compiled, in the order compiled. */
  def compiledCodes(jitState: JitState[?]): Vector[gezi.ir.Code] = jitState match
    case run: JitRunState[?] => run.compilationOrder
    case _                   => Vector.empty

  /** The costs the JIT state counted. */
  def counts(jitState: JitState[?]): JitCounts = jitState match
    case run: JitRunState[?] => run.counts
    case _                   => JitCounts.empty

  // ---- random closed terms with choices and parallels ----

  /** A random closed application of about the size like
    * `EvaluatorTesting.randomApplication`, whose subterms may also be
    * choices of none to three members and parallels
    * (random_lattice_application/2).
    */
  def randomLatticeApplication(size: Int, random: SplitMix): (DeBruijnTerm, SplitMix) =
    val smaller = size - 1
    val (functionSize, afterFunctionSize) = random.between(1, smaller)
    val argumentSize = 1.max(smaller - functionSize)
    val (function, afterFunction) = randomLatticeTerm(functionSize, 0, afterFunctionSize)
    val (argument, afterArgument) = randomLatticeTerm(argumentSize, 0, afterFunction)
    (DeBruijnTerm.Apply(function, argument), afterArgument)

  private def randomLatticeTerm(size: Int, bound: Int, random: SplitMix): (DeBruijnTerm, SplitMix) =
    if size <= 1 then leaf(bound, random)
    else
      val (kind, afterKind) = random.between(1, 20)
      val smaller = size - 1
      if kind <= 7 then
        val (body, afterBody) = randomLatticeTerm(smaller, bound + 1, afterKind)
        (DeBruijnTerm.Lambda(body), afterBody)
      else if kind <= 15 then
        val (functionSize, afterFunctionSize) = afterKind.between(1, smaller)
        val argumentSize = 1.max(smaller - functionSize)
        val (function, afterFunction) = randomLatticeTerm(functionSize, bound, afterFunctionSize)
        val (argument, afterArgument) = randomLatticeTerm(argumentSize, bound, afterFunction)
        (DeBruijnTerm.Apply(function, argument), afterArgument)
      else if kind <= 17 then
        val (count, afterCount) = afterKind.between(0, 3)
        val memberSize = 1.max(smaller / 1.max(count))
        (0 until count).foldLeft((Vector.empty[DeBruijnTerm], afterCount)) { case ((members, current), _) =>
          val (member, next) = randomLatticeTerm(memberSize, bound, current)
          (members :+ member, next)
        } match
          case (members, after) =>
            // A choice of no member is top (`Literals.top`), the term of no answer.
            (if members.isEmpty then gezi.frontend.Literals.top else DeBruijnTerm.nestedChoice(members), after)
      else if kind <= 19 then
        val (leftSize, afterLeftSize) = afterKind.between(1, smaller)
        val rightSize = 1.max(smaller - leftSize)
        val (left, afterLeft) = randomLatticeTerm(leftSize, bound, afterLeftSize)
        val (right, afterRight) = randomLatticeTerm(rightSize, bound, afterLeft)
        (DeBruijnTerm.Parallel(left, right), afterRight)
      else leaf(bound, afterKind)

  private def leaf(bound: Int, random: SplitMix): (DeBruijnTerm, SplitMix) =
    if bound == 0 then (DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)), random)
    else
      val (index, after) = random.between(0, bound - 1)
      (DeBruijnTerm.Variable(index), after)

  // ---- files ----

  /** The directory of Gezi, the build's root. */
  def subprojectDirectory: Path = gezi.standardlibrary.LibraryFiles.buildRoot

  /** The main class run in a child JVM whose working directory is a fresh
    * temporary directory (`readInAFreshDirectory`): what it printed, the
    * files it left in that directory, and the tree of Gezi
    * (`treeFiles`) before and after it ran.
    */
  final case class FreshDirectoryRun(output: String, written: Vector[String], before: Vector[String], after: Vector[String])

  /** The main class run with the arguments in a child JVM, -Xmx256m as the
    * test JVMs, on this JVM's class path and with its `gezi.*` system properties, whose
    * working directory is a fresh temporary directory, deleted afterwards
    * when the run left it empty; a run that exits with a failure throws. A
    * JVM cannot change its own working directory, and the forked test JVM
    * runs in its module's directory inside the tree of Gezi, where a
    * relative write into a directory `treeFiles` leaves out (`target`)
    * would not be seen: in the fresh directory every relative write is, as
    * the Prolog tests saw it by running in a fresh working directory
    * (jit.plt's the_jit_writes_no_file, jit_natives.plt's
    * the_natives_write_no_file).
    */
  def readInAFreshDirectory(mainClass: String, arguments: Vector[String] = Vector.empty): FreshDirectoryRun =
    val before = treeFiles(subprojectDirectory)
    val fresh = Files.createTempDirectory("jit_working_directory")
    val javaExecutable = java.nio.file.Paths.get(System.getProperty("java.home"), "bin", "java").toString
    val properties = sys.props.toVector.filter(_._1.startsWith("gezi.")).sorted.map((key, value) => s"-D$key=$value")
    val command = Vector(javaExecutable, "-Xmx256m") ++ properties ++ Vector("-cp", System.getProperty("java.class.path"), mainClass) ++ arguments
    val output = scala.sys.process.Process(command, fresh.toFile).!!
    val written = treeFiles(fresh)
    if written.isEmpty then Files.delete(fresh)
    FreshDirectoryRun(output, written, before, treeFiles(subprojectDirectory))

  /** Every file under the directory with its size and modification time,
    * sorted, symbolic links as their targets and not followed
    * (tree_files/2); the build's output directories `target` and the
    * dev shell's caches are left out, since sbt writes them while tests run,
    * and so are the editor's build server caches `.bloop` and `.metals`,
    * which Metals of a session working in the same checkout writes while
    * tests run (2026-11-12: theNativesWriteNoFile read a changed
    * .bloop tree); a write into a left-out directory goes unseen, as one
    * into `target` does.
    */
  def treeFiles(directory: Path): Vector[String] =
    val skipped = Set("target", ".bsp", ".direnv", ".devenv", ".bloop", ".metals")
    def walked(path: Path): Vector[String] =
      if Files.isSymbolicLink(path) then Vector(s"link $path -> ${Files.readSymbolicLink(path)}")
      else if Files.isDirectory(path, LinkOption.NOFOLLOW_LINKS) then
        if skipped.contains(path.getFileName.toString) then Vector.empty
        else
          val entries = scala.util.Using.resource(Files.list(path))(_.toList.asScala.toVector)
          entries.sortBy(_.toString).flatMap(walked)
      else Vector(s"file $path ${Files.size(path)} ${Files.getLastModifiedTime(path, LinkOption.NOFOLLOW_LINKS)}")
    walked(directory)
