package gezi.frontend

import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.StorageAccess

/** A deep shared graph is printed and read back as an exchange line with no
  * continuation nested once per binding: `ExchangeText.line` of 20,000 nodes,
  * each `λk. k next afterNext` over the two nodes after it, so that every
  * node is shared by two others, returns, and `ExchangeText.term` of the line
  * reads the same interned instruction. Its purpose is to catch a printer or a
  * reader whose fold binds every step onto the accumulated `TailCalls`
  * computation, which nests one continuation per binding and overflows the
  * JVM stack (1,024 frames of `TailCalls`' `flatMap` at 16,000 nodes).
  */
class DeepSharedLineLawTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  // Measured 2026-11-21 on 2 CPUs (nice 10, 1-minute load 18): the test takes 10.9 s and 14.2 s in two cold JVMs printing and reading a 20,000 node graph of about 1.3 MB of text; the bound is about twice the slower. Smaller graphs overflow nothing, so the size is what the law needs.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(30, "s")

  /** The root of the graph of `count` nodes: the node `i` applies its
    * binder to the nodes `i + 1` and `i + 2`, and the last two nodes apply it
    * to nothing.
    */
  private def root(count: Int): Configured[NoFacts.type] =
    import DeBruijnTerm.*
    val last = Defunctionalization.thunkInstruction[NoFacts.type](Lambda(Variable(0)))
    (0 until count).foldLeft((last, last)) { case ((next, afterNext), _) =>
      val node = Defunctionalization.thunkInstruction[NoFacts.type](
        Lambda(Apply(Apply(Variable(0), Constant(next)), Constant(afterNext)))
      )
      (node, next)
    }._1

  test("theLineOfADeepSharedGraphIsWrittenAndReadBack") {
    val graph = root(20000)
    val line = ExchangeText.line(graph)
    assert(ExchangeText.term[NoFacts.type](line).toOption.exists(Configured.same(_, graph)))
  }
