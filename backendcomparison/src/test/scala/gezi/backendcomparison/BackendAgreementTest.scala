package gezi.backendcomparison

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
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
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.GeneratedStore
import gezi.generatedinputs.OrientationGenerators
import gezi.generatedinputs.StoreGenerators
import gezi.ir.{Apply, Slot, Thunk}

/** The law of the backend interface (`gezi.ematching.Backend`): every
  * backend runs a program the same way. On generated stores
  * (`StoreGenerators.store`) and generated lemmas over them, compiled by the
  * orientation compiler and the index into a program, each backend of
  * `Backends` saturates the same inputs to an equal run (the graph with its
  * nodes, unions, counts, matches found and entries read, and the End), and
  * on the graph the closure backend reached gives an equal `Matching` (the
  * matches, their order, the entries read) for every node under every key
  * of the program. Its purpose is to catch a backend that finds another
  * match, in another order, reads another number of entries, or builds
  * other nodes or builds them in another order.
  */
class BackendAgreementTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of BackendAgreementTest, "every backend saturates to the same run and finds the same matching on every node", takes 9.309 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  /** A pattern over the store, of at most the depth, with metavariables
    * below the arity: a metavariable, an instruction of the store, an
    * application, a parallel, a binary choice, a thunk of the shape of one
    * of the store's thunks, or an eta-shaped lambda `\x. M x` over the code
    * `slot 0 slot 1`, which the orientation compiler reads as a closure.
    */
  private def pattern(store: GeneratedStore, arity: Int, depth: Int): Gen[Pattern] =
    val instructions = store.instructions
    val metavariable = Gen.int(Range.constant(0, arity - 1)).map(Pattern.Metavariable(_))
    val reference = Gen.element(instructions.head, instructions.tail.toList).map(Pattern.InstructionReference(_))
    val leaves = List(3 -> metavariable, 2 -> reference)
    if depth <= 0 then Gen.frequency1(leaves.head, leaves.tail*)
    else
      val below = pattern(store, arity, depth - 1)
      val thunks = instructions.map(store.store.expanded).collect { case thunk @ Thunk(_, _, _) => thunk }
      val thunkShaped =
        if thunks.isEmpty then Nil
        else
          List(1 -> (for
            Thunk(code, holes, fillings) <- Gen.element(thunks.head, thunks.tail.toList)
            patterns <- below.list(Range.singleton(fillings.size))
          yield Pattern.Thunk(code, holes, patterns.toVector)))
      val compounds = List(
        4 -> (for function <- below; argument <- below yield Pattern.Apply(function, argument)),
        1 -> (for left <- below; right <- below yield Pattern.Parallel(left, right)),
        1 -> (for left <- below; right <- below yield Pattern.Choice(left, right)),
        1 -> metavariable.map(inner =>
          Pattern.Thunk(application, Vector(Hole.Bound(1)), Vector(inner))
        )
      ) ++ thunkShaped
      val all = leaves ++ compounds
      Gen.frequency1(all.head, all.tail*)

  /** The code `slot 0 slot 1`. */
  private val application =
    Code(Apply(Code(Slot(0)), Code(Slot(1))))

  private def lemmas(store: GeneratedStore): Gen[Vector[LemmaSides]] =
    for
      count <- Gen.int(Range.linear(1, 4))
      sides <- (for
        arity <- Gen.int(Range.linear(1, 3))
        left <- pattern(store, arity, 3)
        right <- pattern(store, arity, 2)
      yield (arity, left, right)).list(Range.singleton(count))
    yield sides.toVector.zipWithIndex.map { case ((arity, left, right), index) =>
      LemmaSides(LemmaIdentifier(index), arity, left, right)
    }

  /** One or two inputs among the store's instructions. */
  private def inputs(store: GeneratedStore): Gen[Vector[Instruction]] =
    val instructions = store.instructions
    Gen.element(instructions.head, instructions.tail.toList).list(Range.linear(1, 2)).map(_.toVector)

  private val budget = 40

  stoppableProperty(
    "every backend saturates to the same run and finds the same matching on every node",
    _.copy(testLimit = SuccessCount(300))
  ) { stopped =>
    val generated = for
      store <- StoreGenerators.store
      sides <- lemmas(store)
      inputInstructions <- inputs(store)
    yield (store, sides, inputInstructions)
    val covered = stepCoverage.foldLeft(generated.forAll) { case (property, (name, percentage, holds)) =>
      property.cover(percentage, name, (store, sides, _) => holds(programOf(store, sides)))
    }
    for (store, sides, inputInstructions) <- covered
    yield
      val compiled = OrientationCompilation.compiled(sides, store.store)
      agreement(store, compiled.orientations, compiled.patternInstructions, inputInstructions, StopSignal.completedWith(stopped))
  }

  stoppableProperty(
    "every backend agrees on orientations that abstract stored terms",
    // Lookups (determined subpatterns below a seed's delta) are in 16% of
    // the generated programs (measured on 2026-10-31, 100 cases; the
    // threshold is about a third); IndexedMatchingTest runs 300 cases for the
    // same reason.
    _.copy(testLimit = SuccessCount(300))
  ) { stopped =>
    val generated = for
      store <- StoreGenerators.store
      orientations <- OrientationGenerators.orientationsOver(store)
    yield (store, orientations)
    val covered = generated.forAll
      .cover(5.0, "a lookup", (store, orientations) =>
        steps(Indexing.program(orientations, store.codes)).exists {
          case Step.Lookup(_, _, _) => true
          case _                    => false
        }
      )
    for (store, orientations) <- covered
    yield
      agreement(store, orientations, Vector.empty, store.instructions, StopSignal.completedWith(stopped))
  }

  /** The runs of every backend on the program of the orientations equal the
    * closure backend's, and so do their matchings on the graph it reached.
    */
  private def agreement(
      generated: GeneratedStore,
      orientations: Vector[Orientation],
      patternInstructions: Vector[Instruction],
      inputInstructions: Vector[Instruction],
      stop: StopSignal
  ): Result =
    val store = generated.store
    val program = Indexing.program(orientations, generated.codes)
    val bounds = Orientations.headArityBounds(orientations)
    val compiledPrograms = Backends.byName.map((name, backend) => (name, backend.compiled(program)))
    def run(compiledProgram: CompiledProgram): Run =
      Saturation.run(
        program,
        compiledProgram,
        BuiltInRule.all,
        store,
        bounds,
        patternInstructions,
        inputInstructions,
        budget,
        explained = false,
        stop
      )
    val referenceProgram = compiledPrograms.collectFirst { case (Backends.defaultName, compiledProgram) => compiledProgram }
      .getOrElse(throw IllegalStateException(s"no backend named ${Backends.defaultName}"))
    val reference = run(referenceProgram)
    val runsEqual = Result.all(
      compiledPrograms.toList.collect {
        case (name, compiledProgram) if name != Backends.defaultName =>
          Result.diff(run(compiledProgram), reference)(_ == _).log(s"the run of $name")
      }
    )
    runsEqual.and(matchingsEqual(program, compiledPrograms, referenceProgram, reference.graph))

  private def programOf(store: GeneratedStore, sides: Vector[LemmaSides]): Program =
    Indexing.program(OrientationCompilation.compiled(sides, store.store).orientations, store.codes)

  private def steps(program: Program): Vector[Step] =
    def within(step: Step): Vector[Step] = step match
      case Step.Once(inner) => step +: inner.flatMap(within)
      case other            => Vector(other)
    program.seeds.values.toVector.flatten.flatMap(_.steps.flatMap(within))

  private def within(building: Building): Vector[Building] = building +: (building match
    case Building.Apply(function, argument, _) => within(function) ++ within(argument)
    case Building.Parallel(left, right)        => within(left) ++ within(right)
    case Building.Choice(left, right)          => within(left) ++ within(right)
    case Building.Thunk(_, _, fillings)        => fillings.flatMap(within)
    case _                                     => Vector.empty)

  /** The buildings of the added sides and shared subterms, and of the codes. */
  private def orientationBuildings(program: Program): Vector[Building] =
    program.orientations.flatMap(plan => plan.added +: plan.shared).flatMap(within)

  private def codeBuildings(program: Program): Vector[Building] =
    program.codes.values.toVector.flatMap(within)

  /** The share of generated cases whose program holds each kind of step and
    * building, at least the percentage given, so that the generator keeps
    * reaching every way a backend runs a program. The shares measured on
    * 2026-10-31 after the seed trees and lookups were merged (thresholds of
    * 100%, which made Hedgehog report them, 100 cases): a closure state
    * checked 38%, members read 37%, users read 31%, a choice's layer read
    * 21%, a thunk's layer read 17%, an application the β rule reads 11%, a
    * thunk built 9%, a witness and head members read 7%, position users read
    * 2%. Each threshold is about a third of its share, so that a fresh seed
    * falls below it rarely; the property runs 300 cases so that position
    * users, whose third is one case in 300, are reached.
    */
  private val stepCoverage: Vector[(String, Double, Program => Boolean)] =
    def stepExists(holds: Step => Boolean): Program => Boolean = program => steps(program).exists(holds)
    Vector(
      ("users read", 10.0, stepExists { case Step.EachUser(_, _, _) => true; case _ => false }),
      ("members read", 12.0, stepExists { case Step.EachMember(_, _, _) => true; case _ => false }),
      ("a closure state checked", 12.0, stepExists { case Step.HasClosure(_) => true; case _ => false }),
      ("a witness", 2.0, stepExists { case Step.Once(_) => true; case _ => false }),
      ("a choice's layer read", 7.0, stepExists { case Step.Layer(_, LayerTemplate.Choice, _) => true; case _ => false }),
      ("a thunk's layer read", 5.0, stepExists { case Step.Layer(_, LayerTemplate.Thunk(_, _), _) => true; case _ => false }),
      ("head members read", 2.0, stepExists { case Step.EachHeadMember(_, _, _) => true; case _ => false }),
      ("position users read", 0.34, stepExists { case Step.EachPositionUser(_, _, _, _) => true; case _ => false }),
      ("a thunk built", 3.0, program => orientationBuildings(program).exists { case Building.Thunk(_, _, _) => true; case _ => false }),
      (
        "an application the β rule reads",
        3.0,
        program => (orientationBuildings(program) ++ codeBuildings(program)).exists { case Building.Apply(_, _, true) => true; case _ => false }
      )
    )

  /** On the graph, every backend's matching of every node under every key
    * of the program equals the closure backend's, each backend's program
    * compiled once by the caller.
    */
  private def matchingsEqual(
      program: Program,
      compiledPrograms: Vector[(String, CompiledProgram)],
      referenceProgram: CompiledProgram,
      graph: EGraph
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
