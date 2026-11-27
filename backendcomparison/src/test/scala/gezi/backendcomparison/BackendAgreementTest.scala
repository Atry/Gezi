package gezi.backendcomparison

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.ematching.indexing.Indexing
import gezi.orientation.LemmaSides
import gezi.orientation.Orientation
import gezi.orientation.OrientationCompilation
import gezi.orientation.Orientations
import gezi.ematching.Building
import gezi.ematching.CompiledProgram
import gezi.ematching.LayerTemplate
import gezi.ematching.Program
import gezi.ematching.Step
import gezi.saturation.Run
import gezi.saturation.Saturation
import gezi.ir.BuiltInRule
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.NonEmptyHoles
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.GeneratedStore
import gezi.generatedinputs.OrientationGenerators
import gezi.generatedinputs.StandInStorages
import gezi.generatedinputs.StoreGenerators
import gezi.ir.{Apply, Slot, Thunk}

/** The law of the backend interface (`gezi.ematching.Backend`): every backend
  * runs a program the same way. On generated stores (`StoreGenerators.store`)
  * and generated lemmas over them, compiled by the orientation compiler and the
  * index into a program, each backend of `Backends` saturates the same inputs
  * to an equal run (the graph with its nodes, unions, counts, matches found and
  * entries read, and the End), and on the graph the closure backend reached
  * gives an equal `Matching` (the matches, their order, the entries read) for
  * every node under every key of the program. Each iteration also runs a
  * program that holds every kind of step and building by construction
  * (`everyKindLemmas`, `withShapes`), so that every way a backend runs a
  * program is reached. Its purpose is to catch a backend that finds another
  * match, in another order, reads another number of entries, or builds other
  * nodes or builds them in another order.
  */
class BackendAgreementTest extends GeneratedProperties:

  private type C = StandInStorages.type
  private type Term = StandInStorages.Term

  private given StandInStorages.type = StandInStorages

  /** A pattern over the store, of at most the depth, with metavariables below
    * the arity: a metavariable, an instruction of the store, an application, a
    * parallel, a binary choice, a thunk of the shape of one of the store's
    * thunks, or an eta-shaped lambda `\x. M x` over the code `slot 0 slot 1`,
    * which the orientation compiler reads as a closure.
    */
  private def pattern(
      store: GeneratedStore,
      arity: Int,
      depth: Int
  ): Gen[Pattern[C]] =
    val instructions = store.instructions
    val metavariable =
      Gen.int(Range.constant(0, arity - 1)).map(Pattern.Metavariable[C](_))
    val reference = Gen
      .element(instructions.head, instructions.tail.toList)
      .map(Pattern.InstructionReference(_))
    val leaves = List(3 -> metavariable, 2 -> reference)
    if depth <= 0 then Gen.frequency1(leaves.head, leaves.tail*)
    else
      val below = pattern(store, arity, depth - 1)
      val thunks = instructions.map(store.store.expanded).collect {
        case thunk @ Thunk(_, _, _) => thunk
      }
      val thunkShaped =
        if thunks.isEmpty then Nil
        else
          List(1 -> (for
            Thunk(code, holes, fillings) <- Gen
              .element(thunks.head, thunks.tail.toList)
            patterns <- below.list(Range.singleton(fillings.size))
          yield Pattern.Thunk(code, holes, patterns.toVector)))
      val compounds = List(
        4 -> (for function <- below; argument <- below
        yield Pattern.Apply(function, argument)),
        1 -> (for left <- below; right <- below
        yield Pattern.Parallel(left, right)),
        1 -> (for left <- below; right <- below
        yield Pattern.Choice(left, right)),
        1 -> metavariable.map(inner =>
          Pattern.Thunk(application, Vector(Hole.Bound(1)), Vector(inner))
        )
      ) ++ thunkShaped
      val all = leaves ++ compounds
      Gen.frequency1(all.head, all.tail*)

  /** The code `slot 0 slot 1`. */
  private val application =
    Code(Apply(Code(Slot(0)), Code(Slot(1))))

  private def lemmas(store: GeneratedStore): Gen[Vector[LemmaSides[C]]] =
    for
      count <- Gen.int(Range.linear(1, 4))
      sides <- (for
        arity <- Gen.int(Range.linear(1, 3))
        left <- pattern(store, arity, 3)
        right <- pattern(store, arity, 2)
      yield (arity, left, right)).list(Range.singleton(count))
    yield sides.toVector.zipWithIndex.map {
      case ((arity, left, right), index) =>
        LemmaSides(LemmaIdentifier(index), arity, left, right)
    }

  /** One or two inputs among the store's instructions. */
  private def inputs(store: GeneratedStore): Gen[Vector[Term]] =
    val instructions = store.instructions
    Gen
      .element(instructions.head, instructions.tail.toList)
      .list(Range.linear(1, 2))
      .map(_.toVector)

  private val budget = 40

  stoppableProperty(
    "every backend saturates to the same run and finds the same matching on every node"
  ) { stopped =>
    val generated = for
      store <- StoreGenerators.store
      sides <- lemmas(store)
      inputInstructions <- inputs(store)
      head <- Gen.element(
        store.instructions.head,
        store.instructions.tail.toList
      )
    yield (store, sides, inputInstructions, head)
    for (store, sides, inputInstructions, head) <- generated.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val compiled = OrientationCompilation.compiled(sides, store.store)
      val everyKind = withShapes(store)
      val everyKindCompiled =
        OrientationCompilation.compiled(everyKindLemmas(head), everyKind.store)
      val everyKindProgram =
        Indexing.program(everyKindCompiled.orientations, everyKind.codes)
      Result.all(
        List(
          agreement(
            store,
            compiled.orientations,
            compiled.patternInstructions,
            inputInstructions,
            stop
          ),
          Result.all(
            stepCoverage.toList.map((name, holds) =>
              Result
                .assert(holds(everyKindProgram))
                .log(s"the constructed program has no $name")
            )
          ),
          agreement(
            everyKind,
            everyKindCompiled.orientations,
            everyKindCompiled.patternInstructions,
            everyKind.instructions,
            stop
          )
        )
      )
  }

  stoppableProperty(
    "every backend agrees on orientations that abstract stored terms"
  ) { stopped =>
    val generated = for
      store <- StoreGenerators.store
      orientations <- OrientationGenerators.orientationsOver(store)
    yield (store, orientations)
    for (store, orientations) <- generated.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      // The constructed store holds (l ∥ l) l, which `(M0 ∥ M0) M0`
      // abstracts; its seed at `M0 ∥ M0` binds M0, so the application is
      // looked up by signature.
      val withLookup = withShapes(store)
      val lookupCompiled = OrientationCompilation.compiled(
        Vector(
          LemmaSides(
            LemmaIdentifier(0),
            1,
            Pattern.Apply(Pattern.Parallel(first, first), first),
            first
          )
        ),
        withLookup.store
      )
      val lookedUp = steps(
        Indexing.program(lookupCompiled.orientations, withLookup.codes)
      ).exists {
        case Step.Lookup(_, _, _) => true
        case _                    => false
      }
      Result.all(
        List(
          agreement(
            store,
            orientations,
            Vector.empty,
            store.instructions,
            stop
          ),
          Result.assert(lookedUp).log("the constructed program has no lookup"),
          agreement(
            withLookup,
            lookupCompiled.orientations,
            lookupCompiled.patternInstructions,
            withLookup.instructions,
            stop
          )
        )
      )
  }

  private val first: Pattern[C] = Pattern.Metavariable(0)
  private val second: Pattern[C] = Pattern.Metavariable(1)

  /** The generated store with three more instructions over its first, l: the
    * thunk `λx. x l` (the code `slot 0 slot 1`, its hole bound to slot 0),
    * `l ∥ l`, and `(l ∥ l) l`.
    */
  private def withShapes(generated: GeneratedStore): GeneratedStore =
    val leaf = generated.instructions.head
    val paralleled = StandInStorages.parallel(leaf, leaf)
    val added = Vector(
      StandInStorages.thunk(
        application,
        NonEmptyHoles(Hole.Bound(0), Vector.empty),
        Vector(leaf)
      ),
      paralleled,
      StandInStorages.application(paralleled, leaf)
    )
    generated.copy(instructions = (generated.instructions ++ added).distinct)

  /** One lemma for each kind of `stepCoverage`, derived from the seeds
    * (`gezi.ematching.indexing.Seeding`), the head an instruction of the store:
    * `(M0 ∥ M0) M1 = M0`, matched from `M0 ∥ M0` through the users of its class
    * and from the root through the members of a class; `M0 M0 + M1 = M1`, a
    * choice's layer, and from `M0 M0` the users at a position;
    * `(λx. M0 x) M1 = M1`, a lambda pattern, a closure state;
    * `M0 (M1 ∥ M1) = M0`, M1 inessential and only in its one copy, a witness;
    * `λx. x M0 = M0`, a thunk's layer; `head M0 ∥ M1 = M1`, the members of a
    * class under the head; `head M0 = λx. x M0`, a thunk built;
    * `head M0 M1 = (λx. x M0) M1`, an application of a thunk pattern, which the
    * β rule reads (a matched side headed by the instruction, since the
    * orientation compiler orients no side whose head is a metavariable).
    */
  private def everyKindLemmas(head: Term): Vector[LemmaSides[C]] =
    val eta =
      Pattern.Thunk[C](application, Vector(Hole.Bound(1)), Vector(first))
    val applying =
      Pattern.Thunk[C](application, Vector(Hole.Bound(0)), Vector(first))
    Vector(
      (2, Pattern.Apply(Pattern.Parallel(first, first), second), first),
      (2, Pattern.Choice(Pattern.Apply(first, first), second), second),
      (2, Pattern.Apply(eta, second), second),
      (2, Pattern.Apply(first, Pattern.Parallel(second, second)), first),
      (1, applying, first),
      (
        2,
        Pattern.Parallel(
          Pattern.Apply(Pattern.InstructionReference(head), first),
          second
        ),
        second
      ),
      (1, Pattern.Apply(Pattern.InstructionReference(head), first), applying),
      (
        2,
        Pattern.Apply(
          Pattern.Apply(Pattern.InstructionReference(head), first),
          second
        ),
        Pattern.Apply(applying, second)
      )
    ).zipWithIndex.map { case ((arity, left, right), index) =>
      LemmaSides(LemmaIdentifier(index), arity, left, right)
    }

  /** The runs of every backend on the program of the orientations equal the
    * closure backend's, and so do their matchings on the graph it reached.
    */
  private def agreement(
      generated: GeneratedStore,
      orientations: Vector[Orientation[C]],
      patternInstructions: Vector[Term],
      inputInstructions: Vector[Term],
      stop: StopSignal
  ): Result =
    val store = generated.store
    val program = Indexing.program(orientations, generated.codes)
    val bounds = Orientations.headArityBounds(orientations)
    val compiledPrograms =
      Backends.byName.map((name, backend) => (name, backend.compiled(program)))
    def run(compiledProgram: CompiledProgram[C]): Run[C] =
      Saturation.run(
        program,
        compiledProgram,
        BuiltInRule.beforeOptIn,
        store,
        bounds,
        patternInstructions,
        inputInstructions,
        budget,
        explained = false,
        stop
      )
    val referenceProgram = compiledPrograms
      .collectFirst { case (Backends.defaultName, compiledProgram) =>
        compiledProgram
      }
      .getOrElse(
        throw IllegalStateException(s"no backend named ${Backends.defaultName}")
      )
    val reference = run(referenceProgram)
    val runsEqual = Result.all(
      compiledPrograms.toList.collect {
        case (name, compiledProgram) if name != Backends.defaultName =>
          Result
            .diff(run(compiledProgram), reference)(_ == _)
            .log(s"the run of $name")
      }
    )
    runsEqual.and(
      matchingsEqual(
        program,
        compiledPrograms,
        referenceProgram,
        reference.graph
      )
    )

  private def steps(program: Program[C]): Vector[Step[C]] =
    def within(step: Step[C]): Vector[Step[C]] = step match
      case Step.Once(inner) => step +: inner.flatMap(within)
      case other            => Vector(other)
    program.seeds.values.toVector.flatten.flatMap(_.steps.flatMap(within))

  private def within(building: Building[C]): Vector[Building[C]] =
    building +: (building match
      case Building.Apply(function, argument, _) =>
        within(function) ++ within(argument)
      case Building.Parallel(left, right) => within(left) ++ within(right)
      case Building.Choice(left, right)   => within(left) ++ within(right)
      case Building.Thunk(_, _, fillings) => fillings.flatMap(within)
      case _                              => Vector.empty)

  /** The buildings of the added sides and shared subterms, and of the codes. */
  private def orientationBuildings(program: Program[C]): Vector[Building[C]] =
    program.orientations
      .flatMap(plan => plan.added +: plan.shared)
      .flatMap(within)

  private def codeBuildings(program: Program[C]): Vector[Building[C]] =
    program.codes.values.toVector.flatMap(within)

  /** Each kind of step and building a backend runs, each held by the program of
    * `everyKindLemmas` by construction.
    */
  private val stepCoverage: Vector[(String, Program[C] => Boolean)] =
    def stepExists(holds: Step[C] => Boolean): Program[C] => Boolean =
      program => steps(program).exists(holds)
    Vector(
      (
        "users read",
        stepExists { case Step.EachUser(_, _, _) => true; case _ => false }
      ),
      (
        "members read",
        stepExists { case Step.EachMember(_, _, _) => true; case _ => false }
      ),
      (
        "a closure state checked",
        stepExists { case Step.HasClosure(_) => true; case _ => false }
      ),
      ("a witness", stepExists { case Step.Once(_) => true; case _ => false }),
      (
        "a choice's layer read",
        stepExists {
          case Step.Layer(_, LayerTemplate.Choice, _) => true; case _ => false
        }
      ),
      (
        "a thunk's layer read",
        stepExists {
          case Step.Layer(_, LayerTemplate.Thunk(_, _), _) => true;
          case _                                           => false
        }
      ),
      (
        "head members read",
        stepExists {
          case Step.EachHeadMember(_, _, _) => true; case _ => false
        }
      ),
      (
        "position users read",
        stepExists {
          case Step.EachPositionUser(_, _, _, _) => true; case _ => false
        }
      ),
      (
        "a thunk built",
        program =>
          orientationBuildings(program).exists {
            case Building.Thunk(_, _, _) => true; case _ => false
          }
      ),
      (
        "an application the β rule reads",
        program =>
          (orientationBuildings(program) ++ codeBuildings(program)).exists {
            case Building.Apply(_, _, true) => true; case _ => false
          }
      )
    )

  /** On the graph, every backend's matching of every node under every key of
    * the program equals the closure backend's, each backend's program compiled
    * once by the caller.
    */
  private def matchingsEqual(
      program: Program[C],
      compiledPrograms: Vector[(String, CompiledProgram[C])],
      referenceProgram: CompiledProgram[C],
      graph: EGraph[C]
  ): Result =
    Result.all(
      (for
        (kind, key) <- program.seeds.keySet.toList.sortBy(_.toString)
        node <- (0 until graph.nodeCount).toList
        (name, compiledProgram) <- compiledPrograms.toList
      yield Result
        .diff(
          compiledProgram.matches(kind, key, graph, node),
          referenceProgram.matches(kind, key, graph, node)
        )(_ == _)
        .log(s"$name, kind $kind, key $key, node $node"))
    )
