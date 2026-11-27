package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.weakhead.oldcorpora.ConstructorTree
import com.yang_bo.gezi.weakhead.oldcorpora.ScottDataType
import com.yang_bo.gezi.weakhead.oldcorpora.ScottDecoding
import com.yang_bo.gezi.standardlibrary.SplitMix
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.DeBruijnTermOf
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.NativeSpecializer

/** How a bounded run ended (evaluator_testing.pl's outcomes): within its
  * budget, with its value; past its budget of steps; or out of a resource
  * first, the tabled mode's tables (`ReadingState.tableLimit`). The last two
  * carry no value: a run that stopped answered nothing.
  */
enum Bounded[+Result]:
  case Finished(value: Result)
  case Exceeded
  case Exhausted(resource: Resource)

  /** Whether the run finished. */
  def finished: Boolean = this match
    case Finished(_) => true
    case _           => false

/** The port of `gezi/tests/evaluator_testing.pl`: what the tests of the
  * evaluator and its readers share. They convert HOAS terms to the thunk IR and
  * back, draw random closed terms from a fixed seed, and bound every run by a
  * budget of steps, never by a clock. A bounded run is one reading from an
  * empty store and no table.
  */
object EvaluatorTesting:

  /** The closed de Bruijn term of a HOAS term with no library name. */
  def lambdaTerm[Constant](term: TermOf[Constant]): DeBruijnTermOf[Constant] =
    term.deBruijnTerm(Map.empty)

  /** The terms of these helpers are read under no facts. */
  private given NoFacts.type = NoFacts

  /** The thunk IR of a closed HOAS term with no library name, under no facts.
    */
  def instructionOf(
      term: TermOf[Configured[NoFacts.type]]
  ): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[NoFacts.type](lambdaTerm(term))

  /** The plain value of a closed HOAS term, its codes interned. */
  def valueOf(term: TermOf[Configured[NoFacts.type]]): Value[NoFacts.type] =
    Values.ofInstruction(instructionOf(term), Set.empty)

  /** The de Bruijn readback of a closed instruction. */
  def instructionTerm(
      instruction: Configured[NoFacts.type]
  ): DeBruijnTermOf[Configured[NoFacts.type]] =
    Defunctionalization.instructionTerm[NoFacts.type](instruction)

  /** The de Bruijn readback of a plain head. */
  def headTerm(
      head: Head[NoFacts.type]
  ): DeBruijnTermOf[Configured[NoFacts.type]] =
    instructionTerm(Values.instruction(head.value))

  /** The de Bruijn readback of a parallel set of plain heads: its head's, or
    * the parallel of its heads' nested to the right. Throws for the empty
    * parallel set, which no term of the calculus spells.
    */
  def setTerm(
      set: ParallelSet[NoFacts.type]
  ): DeBruijnTermOf[Configured[NoFacts.type]] =
    val value = set
      .value(NoFacts)
      .getOrElse(throw AssertionError("the empty parallel set has no readback"))
    instructionTerm(Values.instruction(value))

  /** Every parallel set of the value under the mode, its heads expanded to
    * plain values, in the order found, within the limit of steps and under the
    * known extremes.
    */
  def plainHeadsWithin(
      mode: Mode,
      value: Value[NoFacts.type],
      limit: Long,
      extremes: KnownExtremes = KnownExtremes.none
  ): Bounded[Vector[ParallelSet[NoFacts.type]]] =
    WeakHead
      .heads(mode, value)
      .collected
      .result(
        ReadingState.knowing(
          limit,
          extremes,
          com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
        )
      ) match
      case Computed.Done(heads, _) => Bounded.Finished(heads)
      case Computed.Stopped(after) => stopped(after)

  /** Whether the two vectors of instructions are one in order, instruction by
    * instruction the same object.
    */
  def sameInstructions(
      left: Vector[Configured[NoFacts.type]],
      right: Vector[Configured[NoFacts.type]]
  ): Boolean =
    left.size == right.size && left.lazyZip(right).forall(Configured.same(_, _))

  /** Whether the run finished with exactly the instructions, in order, each the
    * same object.
    */
  def finishedInstructions(
      bounded: Bounded[Vector[Configured[NoFacts.type]]],
      expected: Vector[Configured[NoFacts.type]]
  ): Boolean =
    bounded match
      case Bounded.Finished(found) => sameInstructions(found, expected)
      case _                       => false

  /** Whether the two runs ended alike, the instructions they finished with the
    * same objects in order.
    */
  def sameBounded(
      left: Bounded[Vector[Configured[NoFacts.type]]],
      right: Bounded[Vector[Configured[NoFacts.type]]]
  ): Boolean =
    (left, right) match
      case (Bounded.Finished(leftFound), Bounded.Finished(rightFound)) =>
        sameInstructions(leftFound, rightFound)
      case (Bounded.Exceeded, Bounded.Exceeded) => true
      case (
            Bounded.Exhausted(leftResource),
            Bounded.Exhausted(rightResource)
          ) =>
        leftResource == rightResource
      case _ => false

  /** How a run that stopped ended: out of a resource, or past its budget. */
  def stopped[C <: NativeSpecializer & Singleton](
      after: ReadingState[C]
  ): Bounded[Nothing] = after.exhausted match
    case Some(resource) => Bounded.Exhausted(resource)
    case None           => Bounded.Exceeded

  /** Every parallel set of the value under the mode, read back to de Bruijn
    * terms, in the order found, within the limit of steps.
    */
  def headsWithin(
      mode: Mode,
      value: Value[NoFacts.type],
      limit: Long
  ): Bounded[Vector[DeBruijnTermOf[Configured[NoFacts.type]]]] =
    plainHeadsWithin(mode, value, limit) match
      case Bounded.Finished(heads)     => Bounded.Finished(heads.map(setTerm))
      case Bounded.Exceeded            => Bounded.Exceeded
      case Bounded.Exhausted(resource) => Bounded.Exhausted(resource)

  /** The heads of a closed HOAS term under the mode, read back, within a limit
    * no test of a few nodes reaches.
    */
  def surfaceHeads(
      mode: Mode,
      term: TermOf[Configured[NoFacts.type]]
  ): Vector[DeBruijnTermOf[Configured[NoFacts.type]]] =
    val value = valueOf(term)
    finishedValue(headsWithin(mode, value, smallTermLimit))

  /** The distinct normal forms of the value under the mode, within the limit of
    * steps and under the known extremes.
    */
  def normalFormsWithin(
      mode: Mode,
      value: Value[NoFacts.type],
      limit: Long,
      extremes: KnownExtremes = KnownExtremes.none
  ): Bounded[Vector[Configured[NoFacts.type]]] =
    NormalForms
      .normalForms(mode, value)
      .result(
        ReadingState.knowing(
          limit,
          extremes,
          com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
        )
      ) match
      case Computed.Done(normalForms, _) => Bounded.Finished(normalForms)
      case Computed.Stopped(after)       => stopped(after)

  /** The distinct normal forms of a closed HOAS term under the mode, read back,
    * as a set.
    */
  def surfaceNormalForms(
      mode: Mode,
      term: TermOf[Configured[NoFacts.type]]
  ): Set[DeBruijnTermOf[Configured[NoFacts.type]]] =
    val value = valueOf(term)
    finishedValue(normalFormsWithin(mode, value, smallTermLimit))
      .map(instructionTerm)
      .toSet

  /** Every tree decoded of the value at the data type under the mode, in the
    * order found, within the limit of steps.
    */
  def treesWithin(
      mode: Mode,
      value: Value[NoFacts.type],
      dataType: ScottDataType,
      limit: Long
  ): Bounded[Vector[ConstructorTree]] =
    ScottDecoding
      .decoded(mode, value, dataType)
      .collected
      .result(
        ReadingState
          .fresh(limit, com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(trees, _) => Bounded.Finished(trees)
      case Computed.Stopped(after) => stopped(after)

  /** The limit of the readings of terms of a few nodes that must finish: far
    * above what any of them takes (the largest, the Church arithmetic of
    * `NormalFormsTest`, takes a few hundred steps), so that reaching it is a
    * defect.
    */
  val smallTermLimit: Long = 100000

  /** The value of a run of a small term, which must finish. */
  def finishedValue[Result](bounded: Bounded[Result]): Result = bounded match
    case Bounded.Finished(value) => value
    case stopped                 =>
      throw AssertionError(s"a reading of a small term stopped: $stopped")

  // ---- random closed terms ----

  /** A random closed application of about the size, the root of a cross-checked
    * term (random_application/2).
    */
  def randomApplication(size: Int, random: SplitMix): (DeBruijnTerm, SplitMix) =
    val smaller = size - 1
    val (functionSize, afterFunctionSize) = random.between(1, smaller)
    val argumentSize = 1.max(smaller - functionSize)
    val (function, afterFunction) =
      randomTerm(functionSize, 0, afterFunctionSize)
    val (argument, afterArgument) = randomTerm(argumentSize, 0, afterFunction)
    (DeBruijnTerm.Apply(function, argument), afterArgument)

  /** A random term of about the size whose free variables are among the bound
    * ones, the binders around it (random_surface/3): an abstraction four draws
    * in ten, an application five, a leaf one.
    */
  private def randomTerm(
      size: Int,
      bound: Int,
      random: SplitMix
  ): (DeBruijnTerm, SplitMix) =
    if size <= 1 then leaf(bound, random)
    else
      val (kind, afterKind) = random.between(1, 10)
      val smaller = size - 1
      if kind <= 4 then
        val (body, afterBody) = randomTerm(smaller, bound + 1, afterKind)
        (DeBruijnTerm.Lambda(body), afterBody)
      else if kind <= 9 then
        val (functionSize, afterFunctionSize) = afterKind.between(1, smaller)
        val argumentSize = 1.max(smaller - functionSize)
        val (function, afterFunction) =
          randomTerm(functionSize, bound, afterFunctionSize)
        val (argument, afterArgument) =
          randomTerm(argumentSize, bound, afterFunction)
        (DeBruijnTerm.Apply(function, argument), afterArgument)
      else leaf(bound, afterKind)

  private def leaf(bound: Int, random: SplitMix): (DeBruijnTerm, SplitMix) =
    if bound == 0 then (DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)), random)
    else
      val (index, after) = random.between(0, bound - 1)
      (DeBruijnTerm.Variable(index), after)

  /** A random term of about the size in β normal form whose free variables are
    * among the bound ones, closed when there is none (random_normal_form/3): an
    * abstraction, or a bound variable applied to none to three random β normal
    * forms. It may hold an η redex.
    */
  def randomNormalForm(
      size: Int,
      bound: Int,
      random: SplitMix
  ): (DeBruijnTerm, SplitMix) =
    val (abstraction, afterChoice) =
      if bound == 0 then (true, random)
      else if size > 1 then
        val (kind, afterKind) = random.between(1, 10)
        (kind <= 4, afterKind)
      else (false, random)
    if abstraction then
      val (body, afterBody) =
        randomNormalForm(1.max(size - 1), bound + 1, afterChoice)
      (DeBruijnTerm.Lambda(body), afterBody)
    else
      val (index, afterHead) = afterChoice.between(0, bound - 1)
      val (count, afterCount) =
        if size <= 1 then (0, afterHead) else afterHead.between(0, 3)
      val argumentSize = 1.max((size - 1) / 1.max(count))
      (0 until count).foldLeft(
        (DeBruijnTerm.Variable(index): DeBruijnTerm, afterCount)
      ) { case ((spine, current), _) =>
        val (argument, next) = randomNormalForm(argumentSize, bound, current)
        (DeBruijnTerm.Apply(spine, argument), next)
      }

  /** The term holds no η redex `\x. M x` with x not free in M. */
  def etaContracted(term: DeBruijnTerm): Boolean = term match
    case DeBruijnTerm.Lambda(body) =>
      !etaRedexBody(body) && etaContracted(body)
    case DeBruijnTerm.Apply(function, argument) =>
      etaContracted(function) && etaContracted(argument)
    case _ => true

  private def etaRedexBody(body: DeBruijnTerm): Boolean = body match
    case DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(0)) =>
      !Reference.occursFree(function, 0)
    case _ => false

  /** Each distinct verdict with the number of its occurrences, in the order the
    * verdicts' strings sort.
    */
  def clumpedCounts[Verdict](
      verdicts: Vector[Verdict]
  ): Vector[(Verdict, Int)] =
    verdicts
      .groupBy(identity)
      .toVector
      .map((verdict, found) => (verdict, found.size))
      .sortBy(_._1.toString)

  /** The draws of the generator, each from the generator the previous one left.
    */
  def draws[Drawn](count: Int, seed: Long)(
      draw: SplitMix => (Drawn, SplitMix)
  ): Vector[Drawn] =
    drawn(count, SplitMix(seed), Vector.empty)(draw)

  @tailrec
  private def drawn[Drawn](count: Int, random: SplitMix, found: Vector[Drawn])(
      draw: SplitMix => (Drawn, SplitMix)
  ): Vector[Drawn] =
    if found.size >= count then found
    else
      val (next, after) = draw(random)
      drawn(count, after, found :+ next)(draw)
