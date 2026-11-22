package gezi.ir

import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StoreGenerators

/** Every term is interned (`gezi.ir.Interned`): a term built again from fresh constructor
  * objects, each part built again too and each atom a fresh string, is the
  * very object of the generated term (`eq`). Its purpose is to catch a term
  * made around the pool, and a hash code or an equality of a constructor that
  * is not its content's, either of which gives one content two objects.
  */
class InterningLawTest extends GeneratedProperties:

  /** The code built again from fresh layers. */
  private def rebuiltCode(code: Code): Code = code.layer match
    case Slot(index)                  => Code(Slot(index))
    case Apply(function, argument)    => Code(Apply(rebuiltCode(function), rebuiltCode(argument)))
    case Parallel(left, right)        => Code(Parallel(rebuiltCode(left), rebuiltCode(right)))
    case Choice(left, right)          => Code(Choice(rebuiltCode(left), rebuiltCode(right)))
    case Thunk(inner, holes, fillings) => Code(Thunk(rebuiltCode(inner), holes, fillings.map(rebuiltCode)))

  /** The instruction built again from fresh layers. */
  private def rebuilt(instruction: Instruction): Instruction = instruction.layer match
    case Opaque(name)              => Instruction.opaque(String(name.toCharArray))
    case UriNode(uri)              => Instruction.uri(java.net.URI(uri.toString))
    case Apply(function, argument) => Instruction(Apply(rebuilt(function), rebuilt(argument)))
    case Parallel(left, right)     => Instruction(Parallel(rebuilt(left), rebuilt(right)))
    case Choice(left, right)       => Instruction(Choice(rebuilt(left), rebuilt(right)))
    case Thunk(code, holes, fillings) =>
      Instruction(Thunk(rebuiltCode(code), holes, fillings.map(rebuilt)))

  property("aTermBuiltAgainFromFreshLayersIsTheSameObject") {
    for generated <- StoreGenerators.store.forAll
    yield Result.all(
      generated.instructions.toList.map(instruction => Result.assert(rebuilt(instruction) eq instruction).log(s"rebuilt $instruction")) ++
        generated.codes.toList.map(code => Result.assert(rebuiltCode(code) eq code).log(s"rebuilt code $code"))
    )
  }
