package gezi.narrowblocks

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Apply
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Slot

private given graphNodesLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of `PreparedLemmaCompilation.graphNodes`, by which a
  * round's budget scales with its program: on a chain of a generated depth d
  * whose every part is an application of the part before it to itself, the
  * count is d + 1 when the chain is of instructions over an opaque leaf, and
  * d + 2 when it is the code of a thunk, d + 1 codes over a slot and the
  * thunk itself, though either read as a tree has 2^d leaves. Their purpose
  * is to catch a count that walks the program as a tree, counting a shared
  * part once for each reference, which would make the budget of a program
  * with sharing exponential in its size; a count that misses the program
  * itself or its leaf; and a count that reads a thunk by its children alone,
  * its fillings, missing its body's nodes, so that a program whose content
  * sits in one closure body counts as a few instructions.
  */
class GraphNodesLawTest extends GeneratedProperties:

  property("a chain of self-applications of depth d has d + 1 graph nodes") {
    for depth <- Gen.int(Range.linear(0, 200)).forAll
    yield
      val leaf = NoFacts.opaque("leaf")
      val chain = (1 to depth).foldLeft(leaf)((part, _) => NoFacts.application(part, part))
      Result.diff(PreparedLemmaCompilation.graphNodes(chain), depth + 1)(_ == _)
  }

  property("a thunk whose code is a chain of self-applications of depth d counts d + 2") {
    for depth <- Gen.int(Range.linear(0, 200)).forAll
    yield
      val code = (1 to depth).foldLeft(Code(Slot(0)))((part, _) => Code(Apply(part, part)))
      val thunk = NoFacts.thunkOrInstance(code, Vector(Hole.Bound(0)), Vector.empty)
      Result.diff(PreparedLemmaCompilation.graphNodes(thunk), depth + 2)(_ == _)
  }
