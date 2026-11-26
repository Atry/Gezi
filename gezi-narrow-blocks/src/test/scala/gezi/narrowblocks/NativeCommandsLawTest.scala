package gezi.narrowblocks

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Instruction
import gezi.rewritetrace.Positions
import gezi.rewritetrace.Trace
import gezi.rewritetrace.TraceCommand

/** The law of the lemma route's native commands
  * (`LemmaRoute.nativeCommands`, the trace's `native`): on a generated term, with values for some of its
  * subterms and names among the others, the term replayed through the
  * commands is the term the route reads from, `LemmaRoute.substituted`, and
  * each command's position holds a subterm whose value it puts. Its purpose
  * is to catch a trace whose native round replays to another program than
  * the one the reading starts from: an occurrence left out, a position under
  * a name or under another occurrence, a role misnamed.
  */
class NativeCommandsLawTest extends GeneratedProperties:

  /** Every subterm of the term, the root first, in preorder, each once. */
  private def subterms(term: Instruction): Vector[Instruction] =
    (term +: term.layer.children.flatMap(subterms)).distinct

  property("a term replayed through its native commands is the term with its values substituted") {
    for
      term <- HoasGenerators.evaluatorInstruction(4).forAll
      all = subterms(term)
      // For each subterm: 0 a value, 1 a name, 2 or 3 neither.
      kinds <- Gen.list(Gen.int(Range.constant(0, 3)), Range.singleton(all.size)).forAll
      values <- Gen.list(HoasGenerators.instruction, Range.singleton(all.size)).forAll
    yield
      val chosen = all.zip(kinds).zip(values)
      val valueOf = chosen.collect { case ((subterm, 0), value) => subterm -> value }.toMap
      val names = chosen.collect { case ((subterm, 1), _) => subterm }.toSet
      val commands = LemmaRoute.nativeCommands(term, valueOf, names)
      val replayed = Trace(Vector.empty, Vector.empty, Vector(commands)).output(term)
      val placed = commands.forall {
        case TraceCommand.Native(position, value) => valueOf.get(Positions.subterm(term, position)).contains(value)
        case _                                    => false
      }
      Result
        .all(
          List(
            Result.assert(replayed == LemmaRoute.substituted(term, valueOf, names)).log("the replay differs"),
            Result.assert(placed).log("a command puts a value where its subterm is not")
          )
        )
        .log(s"${commands.size} commands")
  }
