package com.yang_bo.gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Property
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.PropertyT
import scala.annotation.tailrec

/** A state machine test (`CONTRIBUTING.md`, "Tests"): a sequence of commands is
  * generated, folded over the implementation (the system) and over a model much
  * simpler than it, and after each command the two must agree. Everything is a
  * value: the system and the model are immutable, each command returns the next
  * of each, and the run is a fold; there is no stateful runner.
  *
  * A command is generated from the model as it stands after the commands before
  * it (`commandGenerator`), so it meets its precondition: a union names only
  * nodes that exist. Hedgehog's integrated shrinking keeps this when it shrinks
  * a failing sequence: the length shrinks towards 0, which keeps a prefix, and
  * a shrunk command regenerates the commands after it from the model that the
  * shrunk command leaves. Neither removes a command from the middle, so the
  * sequences also shrink by removing any one command whose removal leaves every
  * later command's precondition met (the positions a later command names may
  * then name other things, which is still a sequence the machine accepts). The
  * fold checks the precondition of every command anyway, so a generator that
  * breaks it fails the test with that reason rather than with a disagreement.
  */
trait StateMachine[Command, Model, System]:

  /** The model before any command. */
  def initialModel: Model

  /** The system before any command. */
  def initialSystem: System

  /** Whether the command may run in the model's state. */
  def precondition(model: Model, command: Command): Boolean

  /** The commands that may run in the model's state, each meeting the
    * precondition.
    */
  def commandGenerator(model: Model): Gen[Command]

  /** The model after the command. */
  def modelAfter(model: Model, command: Command): Model

  /** The system after the command. */
  def systemAfter(system: System, command: Command): System

  /** Whether the system agrees with the model after the command, as a Hedgehog
    * result whose failure says on what they disagree.
    */
  def agreement(model: Model, system: System, command: Command): Result

/** The generation and the fold of a state machine test. */
object StateMachine:

  /** The sequences of 0 to `maximumLength` commands, each generated from the
    * model after the ones before it; the length shrinks towards 0, and a
    * sequence shrinks by the removal of one command where the rest stays
    * acceptable.
    */
  def commands[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      maximumLength: Int
  ): Gen[Vector[Command]] =
    require(maximumLength >= 0, s"a negative length: $maximumLength")
    val generated = for
      length <- Gen.int(Range.linear(0, maximumLength))
      commands <- commandsFrom(machine, machine.initialModel, length)
    yield commands.toVector
    generated.shrink(sequence =>
      sequence.indices.toList
        .map(position => sequence.patch(position, Nil, 1))
        .filter(accepted(machine, _))
    )

  /** Whether every command of the sequence meets its precondition in the model
    * the commands before it leave.
    */
  def accepted[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      commands: Vector[Command]
  ): Boolean =
    commands
      .foldLeft(Option(machine.initialModel))((model, command) =>
        model
          .filter(machine.precondition(_, command))
          .map(machine.modelAfter(_, command))
      )
      .isDefined

  /** `remaining` commands from the model's state. The recursion is as deep as
    * the sequence is long, which the maximum length bounds.
    */
  private def commandsFrom[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      model: Model,
      remaining: Int
  ): Gen[List[Command]] =
    if remaining == 0 then Gen.constant(Nil)
    else
      for
        command <- machine.commandGenerator(model)
        rest <- commandsFrom(
          machine,
          machine.modelAfter(model, command),
          remaining - 1
        )
      yield command :: rest

  /** The fold: each command run over the model and the system, its precondition
    * checked first and the agreement after; the first failure stops the fold
    * and names the command's position.
    */
  def run[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      commands: Vector[Command]
  ): Result =
    folded(
      machine,
      commands.toList,
      0,
      machine.initialModel,
      machine.initialSystem
    )

  @tailrec
  private def folded[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      commands: List[Command],
      position: Int,
      model: Model,
      system: System
  ): Result = commands match
    case Nil             => Result.success
    case command :: rest =>
      if !machine.precondition(model, command) then
        Result.failure.log(
          s"command $position, $command, breaks its precondition"
        )
      else
        val nextModel = machine.modelAfter(model, command)
        val nextSystem = machine.systemAfter(system, command)
        val agreed = machine.agreement(nextModel, nextSystem, command)
        if agreed.success then
          folded(machine, rest, position + 1, nextModel, nextSystem)
        else agreed.log(s"after command $position, $command")

  /** The generated sequences of at most `maximumLength` commands as the input
    * of a property, logged one command per line, so that a failure's report
    * lists the shrunk sequence. A test adds coverage to it (`PropertyT.cover`)
    * and yields `run` of the sequence.
    */
  def forAll[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      maximumLength: Int
  ): PropertyT[Vector[Command]] =
    commands(machine, maximumLength).forAllWithLog(sequence =>
      sequence.zipWithIndex
        .map((command, position) => s"$position: $command")
        .mkString("commands:\n", "\n", "")
    )

  /** The property that every generated sequence of at most `maximumLength`
    * commands folds without a disagreement.
    */
  def property[Command, Model, System](
      machine: StateMachine[Command, Model, System],
      maximumLength: Int
  ): Property =
    forAll(machine, maximumLength).map(run(machine, _))
