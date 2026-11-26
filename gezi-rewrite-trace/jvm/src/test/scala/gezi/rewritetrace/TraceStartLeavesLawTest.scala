package gezi.rewritetrace

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction

/** Law: the text of a trace's start that holds opaque instructions, opaque
  * terms and URI nodes, reads back as the start (`TraceStart.written`,
  * `TraceStart.readLocated`), each leaf bound at TERM's start to the literal
  * that says which instruction it is. The starts are generated closed λ-terms
  * whose leaves include two opaque terms, one named with a double quote and a
  * backslash, and two URI nodes, one with a space. Its purpose is to catch a
  * leaf written as a name the text binds nowhere, which the front end rejects,
  * a literal that reads
  * back as another instruction, and a leaf binding the reader takes for a
  * shared instruction's.
  */
class TraceStartLeavesLawTest extends GeneratedProperties:

  private val leaves: Vector[Instruction] = Vector(
    Instruction.opaque("first"),
    Instruction.opaque("quoted \" and \\ name"),
    Instruction.uri(java.net.URI("file:///tmp/a%20b/notebook.ipynb")),
    Instruction.uri(java.net.URI("gezi:/cell/1"))
  )

  private def terms(depth: Int, binders: Int): Gen[DeBruijnTerm] =
    val leaf = Gen.elementUnsafe(
      (leaves.map(DeBruijnTerm.Constant(_)) ++ (0 until binders).map(DeBruijnTerm.Variable(_))).toList
    )
    if depth <= 0 then leaf
    else
      Gen.frequency1(
        2 -> leaf,
        2 -> terms(depth - 1, binders + 1).map(DeBruijnTerm.Lambda(_)),
        3 -> (for
          function <- terms(depth - 1, binders)
          argument <- terms(depth - 1, binders)
        yield DeBruijnTerm.Apply(function, argument))
      )

  private val starts: Gen[Instruction] =
    terms(5, 0).map(term => Defunctionalization.thunkInstruction(DeBruijnTerm.Lambda(term)))

  property("a start that holds opaque instructions reads back as itself") {
    for start <- starts.forAll
    yield
      val text = TraceStart.written(start, None)
      Result
        .assert(TraceStart.readLocated(text, java.net.URI("trace:start")).start eq start)
        .log(text)
  }
