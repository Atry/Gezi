package com.yang_bo.gezi.contest.entry

import java.nio.file.Paths
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.Justification
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.hotspot.ArtifactKey
import com.yang_bo.gezi.hotspot.CompilationUnit
import com.yang_bo.gezi.hotspot.ExecutionDependencies
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Closed
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.jit.BackendChecks
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.NativeValue
import com.yang_bo.gezi.jit.Representation
import com.yang_bo.gezi.narrowblocks.BoundFunctionUnit
import com.yang_bo.gezi.narrowblocks.ClosureArtifacts
import com.yang_bo.gezi.narrowblocks.ClosureUnitCompilation
import com.yang_bo.gezi.narrowblocks.ClosureUnits
import com.yang_bo.gezi.narrowblocks.ProgramCompilation
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTables
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.ScottADTChoices
import scala.util.Random

/** The laws of a closure unit's compilation and replacement
  * (`com.yang_bo.gezi.narrowblocks.ClosureUnits`), over the library of
  * tests/library_fixtures/constant_storage_stop.lambdalattice (the Prolog
  * backend's preset, `double` bound to the native `natural_double` with a
  * declared result filter, and the lemma `constant_storage_stop_judged_double`
  * rooted at an application of `double`) under the converting construction.
  * Each program is a let, `(λf. f a + f b) F`, a and b generated natural
  * storages, so that its unit is F (`BoundFunctionUnit`). The fixtures fix by
  * construction where the rounds rewrite:
  *   - the folding fixture, F = `λx. double s + x`, s a generated natural's
  *     storage, rounds with the rule β alone: `double s` folds into the storage
  *     `Natural(2k)`, so the artifact differs from F;
  *   - the opened-body fixture, F = `λx. double x`, rounds with the rule β and
  *     the lemma alone, the round's own opening off: F's thunk holds `double`
  *     applied to its slot as code, which no lemma reads, so the lemma's one
  *     instance is at `double v`, the β reduct of the opened body `F v`;
  *   - the write-back fixtures, `λx. (λz. double x) x` and, at arity 2,
  *     `λx y. (λz. double y) x`, rounds with the rule β alone: the opened
  *     bodies reduce to `double v`, whose abstraction `λx. double x` is a node
  *     the graph did not hold, so the abstraction rule's union is a union.
  * The expectations follow from the construction, as each test says. Their
  * purpose is to catch a unit compilation that does not read its opened bodies
  * by the β rule, does not open the η-expansion, writes back nothing, unites
  * the levels otherwise than by the abstraction rule and the η rule, leaves an
  * eigenvariable in its artifact, keys the cache by more or less than the unit
  * and its configuration, depends on anything but its key, or a replacement
  * that spells the program otherwise than with the unit's artifact or adds an
  * answer.
  */
class ClosureUnitsLawTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(120, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve(
        "tests/library_fixtures/constant_storage_stop.lambdalattice"
      ),
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val double: Configured[encoding.type] =
    Configured.fromPure(encoding)(
      Pure.required(
        StandardLibrary
          .entryMembers(buildRoot, TermTables.jitLibraryTerms, Expansions.none)
          ._1
          .getOrElse(
            "double",
            throw IllegalArgumentException("no member double")
          )
      )
    )

  /** A round's settings: the opening and the rules given, the rest the fixture
    * entry's.
    */
  private def settings(rules: Set[BuiltInRule]): RoundSettings =
    RoundSettings(
      opening = false,
      builtInRules = rules,
      IndexerImplementation.Standard,
      OrientationCompilerImplementation.Standard,
      SaturatorImplementation.HigherOrder,
      ExtractorImplementation.NarrowBlock(256, 1),
      LemmaEncodingImplementation.Baseline,
      EmatchingImplementation.Closures,
      MemoRetentionOption.Kept,
      WriteBackSpellingsOption.KeptWithinAPass,
      OpeningCriterionOption.CallsAHead
    )

  /** A configuration of one round of the lemmas named and the rules given,
    * under the converting construction of the library's facts.
    */
  private lazy val encoding: com.yang_bo.gezi.jit.StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: StorageAccess = StorageAccess.granted()

  private lazy val crossedIndex =
    com.yang_bo.gezi.standardlibrary.StandardLibraryIndex.crossed(library.index, encoding)

  private def configuration(
      lemmas: Vector[String],
      rules: Set[BuiltInRule]
  ): ProgramCompilation[encoding.type] =
    val round = Defaults
      .lemmaCompilation(
        lemmas.map(library.index.lemmaIdentifier),
        settings(rules),
        200,
        facts.nativeBackend,
        ExtractorModules(Map.empty),
        com.yang_bo.gezi.ir.TermConstruction(encoding),
        com.yang_bo.gezi.weakhead.ReadingConfiguration(encoding, access)
      )
      .prepared(crossedIndex)
    ProgramCompilation(
      crossedIndex,
      Vector(round),
      facts.nativeBackend,
      encoding
    )

  private lazy val folding = configuration(Vector.empty, Set(BuiltInRule.Beta))

  private lazy val openedBody = configuration(
    Vector("constant_storage_stop_judged_double"),
    Set(BuiltInRule.Beta)
  )

  private def natural(value: Int): Configured[encoding.type] =
    Closed
      .configured(
        encoding.operations.storageOf(
          Representation.BigInteger,
          NativeValue.Natural(BigInt(value))
        )
      )
      .getOrElse(throw IllegalStateException(s"a storage is closed: $value"))

  /** A thunk of one hole over the code: the hole at slot 1, the one filling at
    * slot 0.
    */
  private def thunk(
      code: com.yang_bo.gezi.ir.CodeLayer[Code],
      filling: Configured[encoding.type]
  ): Configured[encoding.type] =
    encoding.thunkOrInstance(Code(code), Vector(Hole.Bound(1)), Vector(filling))

  /** The folding fixture's F, `λx. double s + x`. */
  private def foldingFunction(value: Int): Configured[encoding.type] =
    thunk(
      com.yang_bo.gezi.ir.Choice(Code(com.yang_bo.gezi.ir.Slot(0)), Code(com.yang_bo.gezi.ir.Slot(1))),
      encoding.application(double, natural(value))
    )

  /** The opened-body fixture's F, `λx. double x`. */
  private lazy val doubleFunction: Configured[encoding.type] =
    thunk(com.yang_bo.gezi.ir.Apply(Code(com.yang_bo.gezi.ir.Slot(0)), Code(com.yang_bo.gezi.ir.Slot(1))), double)

  /** The inner thunk of the write-back fixtures, `λz. double w`, z ignored, as
    * a code whose fillings are the outer code's slots of `double` and of w:
    * open in w, so that the e-graph's canonical spelling of the outer thunk
    * keeps it in the code, where the β rule reads its application.
    */
  private def innerDouble(doubleSlot: Int, argumentSlot: Int): Code =
    Code(
      com.yang_bo.gezi.ir.Thunk(
        Code(com.yang_bo.gezi.ir.Apply(Code(com.yang_bo.gezi.ir.Slot(0)), Code(com.yang_bo.gezi.ir.Slot(1)))),
        Vector(Hole.Ignored),
        Vector(Code(com.yang_bo.gezi.ir.Slot(doubleSlot)), Code(com.yang_bo.gezi.ir.Slot(argumentSlot)))
      )
    )

  /** The write-back fixture of arity 1, `λx. (λz. double x) x`: x at slot 0,
    * `double` filling slot 1.
    */
  private lazy val redexFunction: Configured[encoding.type] =
    encoding.thunkOrInstance(
      Code(com.yang_bo.gezi.ir.Apply(innerDouble(1, 0), Code(com.yang_bo.gezi.ir.Slot(0)))),
      Vector(Hole.Bound(0)),
      Vector(double)
    )

  /** The write-back fixture of arity 2, `λx y. (λz. double y) x`: x and y at
    * slots 0 and 1, `double` filling slot 2.
    */
  private lazy val pairFunction: Configured[encoding.type] =
    encoding.thunkOrInstance(
      Code(com.yang_bo.gezi.ir.Apply(innerDouble(2, 1), Code(com.yang_bo.gezi.ir.Slot(0)))),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(double)
    )

  /** The configuration of the write-back fixtures: the rule β alone. */
  private lazy val reducing = configuration(Vector.empty, Set(BuiltInRule.Beta))

  /** Whether every opaque leaf of the graph that is no noinline name of the
    * library, the eigenvariables, is alone in its class.
    */
  private def eigenvariablesAlone(graph: EGraph[encoding.type]): Boolean =
    graph.liveNodes.forall {
      case com.yang_bo.gezi.egraph.LiveNode(node, _, com.yang_bo.gezi.ir.NoinlineLeaf(leaf))
          if leaf.layer.isInstanceOf[com.yang_bo.gezi.ir.Opaque] && !crossedIndex.noinline
            .contains(leaf) =>
        graph.classMembers(node).size == 1
      case _ => true
    }

  /** The let `(λf. f a + f b) F`. */
  private def letProgram(
      function: Configured[encoding.type],
      first: Int,
      second: Int
  ): Configured[encoding.type] =
    val body = Code(
      com.yang_bo.gezi.ir.Choice(
        Code(com.yang_bo.gezi.ir.Apply(Code(com.yang_bo.gezi.ir.Slot(0)), Code(com.yang_bo.gezi.ir.Slot(1)))),
        Code(com.yang_bo.gezi.ir.Apply(Code(com.yang_bo.gezi.ir.Slot(0)), Code(com.yang_bo.gezi.ir.Slot(2))))
      )
    )
    encoding.application(
      encoding.thunkOrInstance(
        body,
        Vector(Hole.Bound(0)),
        Vector(natural(first), natural(second))
      ),
      function
    )

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = false,
    instanceTableTrial = com.yang_bo.gezi.jit.TableCost.trial,
    instanceRetention = InstanceRetentionOption.Generations(
      com.yang_bo.gezi.jit.JitConfiguration.defaultInstanceTableGeneration
    ),
    budget = com.yang_bo.gezi.jit.JitConfiguration.defaultBudget,
    checkpoints = CheckpointOption.Profitable,
    nativeBlocks = NativeBlocksOption.None,
    lookahead = LookaheadOption.Lazily,
    instanceReuse = InstanceReuseOption.WithinVersion
  )

  private val readingOptions =
    ReadingOptions(
      ApplicationOption.ByLayer,
      TableSharingOption.Local,
      TableRetentionOption.NoneKept,
      ContinuationOption.Substituted,
      ParallelOption.BothSides
    )

  private def unionsBy(
      graph: EGraph[encoding.type],
      chosen: Justification => Boolean
  ): Int = graph.unions.count(union => chosen(union.justification))

  /** The law of the folding fixture's compilation. Derived from the
    * construction: F at arity 1 gives one level, T1 = `λx. F x`, opened at v;
    * no lemma reads v, so v's class holds its leaf alone; the body `F v`, read
    * by the β rule, reduces to `double s + v`, and `double s` folds into
    * `Natural(2k)` before any delta, a leaf smaller than the application, so
    * the body's extraction is `Natural(2k) + v`. Its abstraction over v is
    * `λx. Natural(2k) + x`, a thunk layer over the class of `double s`: F's own
    * node, so the abstraction rule's union joins T1 to F's class and the η
    * rule's then joins nothing; abstraction and η unions are 1 together, and
    * the artifact, F's class spelled, is `λx. Natural(2k) + x`, not F. On the
    * same F twice with no cache the artifact is one interned object. Through
    * the cache service, two lets of one F and other literals compile once: the
    * first call leaves the key in `ClosureArtifacts` and has the unit's graph,
    * the second reads the key and has none; and `ProgramCompiler.compiled` of
    * the unit `Closure(F)` with a third let reads it too, spending nothing.
    */
  stoppableTest(
    "the folding fixture's unit is written back once per level, cached by its function, and deterministic"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261147)
    (1 to 3).foreach { round =>
      val value = random.nextInt(30)
      val function = foldingFunction(value)
      val compiled =
        ClosureUnits.compiledUnit(folding, function, 1, explained = false, stop)
      val graph = compiled.graph.getOrElse(
        fail("a compilation that ran leaves its graph")
      )
      val again =
        ClosureUnits.compiledUnit(folding, function, 1, explained = false, stop)
      val caches = Defaults.caches()
      val source = ExpansionSource.fresh()
      val dependencies = ExecutionDependencies(caches, source)
      val key = ArtifactKey[encoding.type, Configured[encoding.type]](
        CompilationUnit.Closure(function),
        ClosureUnitCompilation(folding, source, 1)
      )
      val before = caches.locked(ClosureArtifacts(encoding))(_.tryGet(key))
      val first = ClosureUnits.cached(
        folding,
        letProgram(function, random.nextInt(30), random.nextInt(30)),
        dependencies,
        false,
        stop
      )
      val written = caches.locked(ClosureArtifacts(encoding))(_.tryGet(key))
      val second = ClosureUnits.cached(
        folding,
        letProgram(function, 30 + random.nextInt(30), random.nextInt(30)),
        dependencies,
        false,
        stop
      )
      val (_, _, compiledSpent) = com.yang_bo.gezi.narrowblocks
        .ProgramCompiler(folding)
        .compiled(
          letProgram(function, 60 + random.nextInt(30), random.nextInt(30)),
          CompilationUnit.Closure(function),
          dependencies,
          stop
        )
      assertEquals(
        (
          unionsBy(
            graph,
            {
              case Justification.Abstraction(_, _, _) | Justification.Eta(_) =>
                true
              case _ => false
            }
          ),
          compiled.kept,
          Configured.same(again.artifact, compiled.artifact),
          before.isEmpty,
          written.exists(Configured.same(_, compiled.artifact)),
          first.map((unit, unitCompiled) =>
            (
              Configured.same(unit.function, function),
              unitCompiled.graph.isDefined
            )
          ),
          second.map((unit, unitCompiled) =>
            (
              Configured.same(unit.function, function),
              unitCompiled.graph.isDefined,
              Configured.same(unitCompiled.artifact, compiled.artifact)
            )
          ),
          compiledSpent.instances,
          eigenvariablesAlone(graph)
        ),
        (
          1,
          false,
          true,
          true,
          true,
          Some((true, true)),
          Some((true, false, true)),
          0L,
          true
        ),
        s"round $round, natural $value"
      )
    }
  }

  /** The law of the opened-body fixture. Derived from the construction: the
    * round's own opening is off, so F's thunk, whose code applies `double` to
    * its slot, is never opened, and no lemma reads a code; T1's body `F v`,
    * read by the β rule, takes one β step to `double v` (one β union), where
    * the lemma has its one instance, adding `(double v ∥ v) + double v` to the
    * body's class. The extraction keeps the smaller `double v`, whose
    * abstraction over v is `λx. double x`, F's own node: the abstraction rule's
    * union joins T1 to F's class (1), and the η rule's joins nothing (0). F's
    * class then holds F and T1, whose spelling holds F, so the extraction keeps
    * F.
    */
  stoppableTest(
    "the opened-body fixture's lemma instance is at the opened body alone, and its unit keeps F"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val compiled = ClosureUnits.compiledUnit(
      openedBody,
      doubleFunction,
      1,
      explained = false,
      stop
    )
    val graph =
      compiled.graph.getOrElse(fail("a compilation that ran leaves its graph"))
    val lemma =
      library.index.lemmaIdentifier("constant_storage_stop_judged_double")
    val lemmaRoots = graph.unions.collect(union =>
      union.justification match
        case Justification.Lemma(found, _) if found == lemma =>
          graph.root(union.first)
    )
    // The body's class: the class of the one application of `double`.
    val bodyRoot = graph
      .instructionNode(double)
      .flatMap(doubleNode =>
        graph.liveNodes.collectFirst {
          case com.yang_bo.gezi.egraph.LiveNode(_, root, com.yang_bo.gezi.ir.Apply(function, _))
              if function == graph.root(doubleNode) =>
            root
        }
      )
    assertEquals(
      (
        lemmaRoots.size,
        lemmaRoots.headOption == bodyRoot,
        unionsBy(
          graph,
          { case Justification.Beta(_) => true; case _ => false }
        ),
        unionsBy(
          graph,
          { case Justification.Abstraction(_, _, _) => true; case _ => false }
        ),
        unionsBy(graph, { case Justification.Eta(_) => true; case _ => false }),
        eigenvariablesAlone(graph),
        compiled.kept
      ),
      (1, true, 1, 1, 0, true, true)
    )
  }

  /** The law of the write-back fixtures. Derived from the construction, at
    * arity 1 (`λx. (λz. double x) x`): the inner thunk is open in x, so the
    * e-graph's canonical spelling keeps it in F's code; the body `F v`, read by
    * the β rule, reduces to `(λz. double v) v`, an application whose function
    * the code writes as a thunk, which the β rule reads and reduces to
    * `double v`. The extraction of the body's class is `double v`, the smallest
    * of its members, and its abstraction over v, `λx. double x`, is a node the
    * graph did not hold: the abstraction rule's union joins T1 to it (1), and
    * the η rule's joins T1's class to F's (1). At arity 2 (`λx y. (λz. double
    * y) x`): the outer body `F v1` reduces to a closure of one hole, which the
    * inner level's body `(F v1) v2` takes a β step with, then the inner redex,
    * down to `double v2`; the inner level writes back `λx. double x` into its T
    * and joins it to the outer body's class; the outer level writes back that
    * class's spelling, `λx. double x`, which holds no v1 and is the smallest
    * member, abstracted over v1, a new node: an abstraction and an η union at
    * each level (2 and 2). No lemma joins an eigenvariable's class, so each is
    * alone, and the artifact, whichever member of F's class the extractor
    * spells (the spellings of F and of the written-back thunk tie in the
    * extractor's size, its order deciding, which these laws do not derive),
    * holds no eigenvariable (`ClosureUnits.compiledUnit` asserts it).
    */
  stoppableTest(
    "the write-back fixtures unite each level by the abstraction rule and the η rule"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val single = ClosureUnits.compiledUnit(
      reducing,
      redexFunction,
      1,
      explained = false,
      stop
    )
    val pair = ClosureUnits.compiledUnit(
      reducing,
      pairFunction,
      2,
      explained = false,
      stop
    )
    def counted(compiled: com.yang_bo.gezi.narrowblocks.CompiledUnit) =
      val graph = compiled.graph.getOrElse(
        fail("a compilation that ran leaves its graph")
      )
      (
        unionsBy(
          graph,
          { case Justification.Abstraction(_, _, _) => true; case _ => false }
        ),
        unionsBy(graph, { case Justification.Eta(_) => true; case _ => false }),
        eigenvariablesAlone(graph)
      )
    assertEquals((counted(single), counted(pair)), ((1, 1, true), (2, 2, true)))
  }

  /** The Scott natural of the value, written out as its βη normal form: zero is
    * `λz s. z`, a successor `λz s. s n`.
    */
  /** The term as the Scott ADT value it is. */
  private def scottADT(
      term: Configured[encoding.type]
  ): ScottADTChoices[encoding.type] =
    ScottADTChoices
      .ofNormalForm(term)
      .getOrElse(
        throw IllegalStateException(
          s"a Scott natural is a Scott ADT value: $term"
        )
      )

  private def scottNatural(value: Int): DeBruijnTerm =
    (1 to value).foldLeft(
      DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))
    ) { (predecessor, _) =>
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(
          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), predecessor)
        )
      )
    }

  /** The law of the replacement on the folding fixture. Derived from the
    * construction: the replacement round unites F's node with the artifact's
    * node, its one union justified `Compiled`, and makes no lemma instance; the
    * cost model has no repeller production on these terms, so the extraction is
    * the program with F spelled by the artifact. Read by the framework's JIT,
    * its normal forms are among {2k, a, b}, the values of `f a + f b` with
    * `f x = 2k + x` computed here, the reader's answers written out as Scott
    * naturals independently of the reader; and 2k is among them, the choice's
    * first operand, a storage the reader decodes at once, so that the law is
    * not met by a reading with no answer.
    */
  stoppableTest(
    "the replacement spells the program with the unit's artifact and adds no answer"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val random = Random(20261148)
    (1 to 3).foreach { round =>
      val (value, first, second) =
        (random.nextInt(10), random.nextInt(10), random.nextInt(10))
      val function = foldingFunction(value)
      val program = letProgram(function, first, second)
      val dependencies =
        ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh())
      val (output, result) = ClosureUnits.compiledProgram(
        folding,
        program,
        dependencies,
        explained = false,
        stop
      )
      val artifact = result
        .flatMap(_.units.headOption)
        .map(_.artifact)
        .getOrElse(fail("one unit compiled"))
      val graph = result.map(_.graph).getOrElse(fail("a replacement graph"))
      val letThunk = program.layer match
        case com.yang_bo.gezi.ir.Apply(function, _) => function
        case other                      =>
          throw IllegalStateException(s"a let is an application, not $other")
      val jit =
        Defaults.jit(encoding, jitOptions, GroupBlocksOption.None, access)
      val executor = Defaults.executor(jit, readingOptions)
      val reading = Judgments
        .read(
          executor,
          dependencies,
          output,
          1000000L,
          stop,
          jit.readingConfiguration
        )
        .read
      val members = reading.map(found => ScottADTChoices.members(found.choices))
      def scottValue(value: Int): Configured[encoding.type] =
        com.yang_bo.gezi.frontend.Defunctionalization
          .thunkInstruction[encoding.type](scottNatural(value))
      assertEquals(
        (
          Configured.same(output, encoding.application(letThunk, artifact)),
          unionsBy(
            graph,
            { case Justification.Compiled(_) => true; case _ => false }
          ),
          unionsBy(
            graph,
            { case Justification.Lemma(_, _) => true; case _ => false }
          ),
          members.map(
            _.forall(member =>
              Vector(2 * value, first, second).exists(wanted =>
                ScottADTChoices.same(member, scottADT(scottValue(wanted)))
              )
            )
          ),
          members.map(
            _.exists(member =>
              ScottADTChoices.same(member, scottADT(scottValue(2 * value)))
            )
          )
        ),
        (true, 1, 0, Some(true), Some(true)),
        s"round $round: natural $value, literals $first and $second"
      )
    }
  }
