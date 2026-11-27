package gezi.frontend

import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.StorageAccess

/** Generated programs are thousands of nodes deep: every conversion of the
  * front end takes a right-nested chain of 100,000 applications,
  * `λx. f (f (... (f x)))`, without overflowing the JVM stack. Measured on
  * 2026-11-16 with every term interned: the occurrence tagging, whose tagged
  * chain has 600,001 nodes and 100,000 distinct closed subterms, runs out of a
  * 256 MB heap and passes in 320 MB (the frontend's `build.sbt` has the
  * readings).
  */
class DeepTermsTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private type NoFactsTerm = Configured[NoFacts.type]

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of DeepTermsTest, "theOccurrenceTaggingOfADeepChain", takes 12.111 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. The body runs on the JVM's default stack, as the test thread of the framework did. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(20, "s")

  import DeBruijnTerm.*

  private val length = 100000

  private val functionPure = Defunctionalization.pure(Lambda(Variable(0)))

  private val function: NoFactsTerm = Configured.fromPure(NoFacts)(functionPure)

  private val definitions: Map[String, NoFactsTerm] = Map("f" -> function)

  /** The chain as a de Bruijn term, built by a fold. */
  private val expected: DeBruijnTermOf[NoFactsTerm] =
    Lambda(
      (1 to length).foldLeft(Variable(0): DeBruijnTermOf[NoFactsTerm])(
        (inner, _) => Apply(Constant(function), inner)
      )
    )

  /** The written form of a deep term (`DeBruijnTerm.written`) is its case
    * names, atoms and subterms in order: the derived `toString` overflowed the
    * stack on a deep term in an assertion's message (judge tests, 2026-10-31).
    */
  test("theWrittenFormOfADeepChain") {
    val written = DeBruijnTerm.written(expected)
    val call = s"Apply(Constant($function), "
    assertEquals(
      written,
      "Lambda(" + call * length + "Variable(0)" + ")" * length + ")"
    )
  }

  // TODO: theHigherOrderSyntaxOfADeepChain stood here. Its purpose: the HOAS conversion takes the deep chain
  // `λx. f (f (... (f x)))` without overflowing the JVM stack. It named library terms by Term.define("f"), a free
  // variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
  // Its replacement reads the library terms it needs
  // as members of a fixture file under tests/ by projection and composes them with the HOAS case of a closed
  // instruction. The deleted code: git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/DeepTermsTest.scala.

  test("theLambdalatticeTextOfADeepChain") {
    val text = "λx." + "f (" * length + "x" + ")" * length
    val parsed = Lambdalattice.term(text, FreeNames.Allowed)
    assertEquals(
      parsed,
      Lambda(
        (1 to length).foldLeft(Variable(0): DeBruijnTerm)((inner, _) =>
          Apply(Free("f"), inner)
        )
      )
    )
    assert(
      Configured.same(
        Defunctionalization.thunkInstruction[NoFacts.type](parsed, definitions),
        Defunctionalization.thunkInstruction[NoFacts.type](expected)
      )
    )
    assertEquals(Lambdalattice.freeNames(text), Vector("f"))
  }

  test("theDefunctionalizationInterningAndReadbackOfADeepChain") {
    val instruction =
      Defunctionalization.thunkInstruction[NoFacts.type](expected)
    // The chain with the literal of f in place of each reference: one instruction,
    // whose readback writes every reference out.
    val literal = Lambda(
      (1 to length).foldLeft(Variable(0): DeBruijnTerm)((inner, _) =>
        Apply(Lambda(Variable(0)), inner)
      )
    )
    val literalInstruction =
      Defunctionalization.thunkInstruction[NoFacts.type](literal)
    assert(Configured.same(literalInstruction, instruction))
    assertEquals(Defunctionalization.instructionTerm(instruction), literal)
    // The respelling on the IR walks the chain without the stack, the
    // function's instruction a name or not, and gives back the front end's
    // instruction.
    assert(
      Configured.same(
        Respelling.respelled(instruction, Set(function)),
        instruction
      )
    )
    val closed = Defunctionalization.thunkInstruction[NoFacts.type](
      Apply(expected, Constant(function))
    )
    assert(Configured.same(Respelling.respelled(closed, Set.empty), closed))
  }

  test("theOccurrenceTaggingOfADeepChain") {
    // The role next_tag is a define of its own: were it f, the marking
    // `name tag` of an occurrence would be the next tag's term, one instruction.
    val nextTag = Defunctionalization.pure(Lambda(Lambda(Variable(1))))
    val markers =
      OccurrenceMarkers(functionPure, functionPure, functionPure, nextTag)
    val Counted(tagged, operations) =
      Occurrences.taggedCounted(expected, markers)
    // One tag interned after each of the length + 1 occurrences (the chain
    // and each constant), and 2 * length + 3 nodes visited: the lambda twice
    // (as an occurrence and as its chain), each application, constant and
    // the variable once.
    assertEquals(operations, (2L * length + 3) + (length + 1))
    val taggedInstruction =
      Defunctionalization.thunkInstruction[NoFacts.type](tagged)
    assert(
      Configured.same(
        Respelling.respelled(taggedInstruction, Set.empty),
        taggedInstruction
      )
    )
  }
