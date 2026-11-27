package gezi.proofs

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.LayerWith
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import gezi.ir.Thunk
import gezi.standardlibrary.StandardLibraryIndex

/** The laws of a thunk constant of thousands of fillings: its type nests one
  * function type per filling (`ThunkDefinitions.thunkType`), and a writer
  * that recurses on that depth overflows the stack
  * (2,468 fillings on
  * the direct point of `repeated_library_hotspots_calls_1000`, seed
  * 20261116, overflowed in `HolType.Function.hashCode`).
  *
  * The thunk of a generated arity applies its hole to one generated
  * filling, `apply(slot(arity), slot(read))` over the hole `slot(arity)`,
  * every filling the identity `λx. x`: `λx. x f_read`, which is not
  * eta-shaped (the writer states the defunctionalized η rule of a thunk of
  * one filling only, `Statements.eta`).
  */
class ThunkConstantArityLawTest extends GeneratedProperties:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private given NoFacts.type = NoFacts
  import ThunkConstantArityLawTest.*

  private val index: StandardLibraryIndex[NoFacts.type] = StandardLibraryIndex(NoFacts, Vector.empty, Vector.empty, Vector.empty, Vector.empty)

  /** An arity of thousands, above the 2,468 measured, with a slot
    * the code reads, below `smallArity`.
    */
  private val shapes: Gen[(Int, Int)] =
    for
      arity <- Gen.int(Range.linear(3000, 4000))
      read <- Gen.int(Range.linear(0, smallArity - 1))
    yield (arity, read)

  /** Two inputs, so that each law stays well within the 3 s deadline: each
    * input writes an article of tens of thousands of lines. Measured
    * 2026-11-17 on CPUs 10 and 11 at nice 10, 1-minute load 5.5: 1.47 s and
    * 0.98 s for the two laws (2.2 s and 1.5 s with three inputs).
    */
  private def few(configuration: hedgehog.core.PropertyConfig): hedgehog.core.PropertyConfig =
    configuration.copy(testLimit = hedgehog.core.SuccessCount(2))

  /** Purpose: catch a recursion on the depth of a function type in the
    * article writer (the dictionary's hashing and equality of types, the
    * writing of a type): the article of `t = t` for the thunk `t` is written
    * on the default thread stack, and has as many more `opType` lines than
    * the article of the thunk of `smallArity` fillings as it has more
    * fillings: one more function type in the constant's type for each, each
    * type of the spine written once.
    */
  property("an article of a thunk constant of thousands of fillings writes one function type per filling", few) {
    shapes.forAllWithLog((arity, read) => s"arity $arity, read $read").map { (arity, read) =>
      val difference = opTypeLines(articleOf(arity, read)) - opTypeLines(articleOf(smallArity, read))
      Result
        .assert(difference == arity - smallArity)
        .log(s"$difference more opType lines for ${arity - smallArity} more fillings")
    }
  }

  /** Purpose: catch a recursion on the depth of a function type in the
    * encoding of a type (`Encoding.typeEncoded`) or in its text
    * (`HolTermText`): the text of the thunk constant, the head of the
    * thunk's HOL term, holds one function type per filling. The head alone:
    * the text of the whole term, its constant applied to thousands of
    * fillings, costs time quadratic in their number.
    */
  property("the text of a thunk constant of thousands of fillings holds one function type per filling", few) {
    shapes.forAllWithLog((arity, read) => s"arity $arity, read $read").map { (arity, read) =>
      val ThunkDefinitions.NamedTerms(Vector(encoded), _) =
        OpentheoryArticle.termEncoded(index, thunk(arity, read)): @unchecked
      val functionTypes = HolTermText.text(head(encoded)).split(java.util.regex.Pattern.quote(functionTypeText), -1).length - 1
      Result.assert(functionTypes == arity).log(s"$functionTypes function types for $arity fillings")
    }
  }

  private def articleOf(arity: Int, read: Int): String =
    val term = thunk(arity, read)
    OpentheoryArticle.text(
      index,
      term,
      term,
      // Node 0 is the identity thunk every filling is, node 1 the thunk constant over them.
      StrategyProof[NoFacts.type](Vector(identityLayer, thunkLayer(arity, read)), Vector.empty, Vector(ProofEquation(1, 1)), Vector.empty)
    )

object ThunkConstantArityLawTest:

  /** The arity of the article an article of thousands of fillings is
    * compared with: at two fillings or more the article's function types are
    * those of the thunk's arity and of one more (its constant without the
    * hole, which its defunctionalized β rule states), each with the type of
    * its defining constant, so their number grows by one per filling.
    */
  private val smallArity = 10

  /** The text of the function type operator in `HolTermText`. */
  private val functionTypeText = "type([\"->\"]"

  /** `λx. x`, a thunk of no filling. */
  private given NoFacts.type = NoFacts

  private val identityThunk: Configured[NoFacts.type] =
    NoFacts.thunk(Code.Slot(0), NonEmptyHoles(Hole.Bound(0), Vector.empty), Vector.empty)

  private val identityLayer: LayerWith[Int, Configured[NoFacts.type]] =
    Thunk(Code.Slot(0), Vector(Hole.Bound(0)), Vector.empty[Int])

  /** The node layer of the thunk constant, its fillings the node 0 each. */
  private def thunkLayer(arity: Int, read: Int): LayerWith[Int, Configured[NoFacts.type]] =
    Thunk(Code(gezi.ir.Apply(Code.Slot(arity), Code.Slot(read))), Vector(Hole.Bound(arity)), Vector.fill(arity)(0))

  private def thunk(arity: Int, read: Int): Configured[NoFacts.type] =
    NoFacts.thunk(
      Code(gezi.ir.Apply(Code.Slot(arity), Code.Slot(read))),
      NonEmptyHoles(Hole.Bound(arity), Vector.empty),
      Vector.fill(arity)(identityThunk)
    )

  @scala.annotation.tailrec
  private def head(term: HolTerm): HolTerm = term match
    case HolTerm.Application(function, _) => head(function)
    case _                                => term

  private def opTypeLines(article: String): Int = article.split('\n').count(_ == "opType")
