package com.yang_bo.gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import com.yang_bo.gezi.orientation.StandardOrientationCompiler
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.LemmaSides
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex

/** The law of `UnionRecord.built` on saturations of generated programs under
  * the lemmas of `RewriteTraceLawTest` (the choice's commutativity,
  * associativity and idempotence, K applied to two) and the built-in rules: a
  * union's built node is one of its two nodes, and its id is above every node
  * an earlier union of a lemma instance or a step names, as a node the union's
  * own instance or β step made is: such an earlier union was made, or queued,
  * before the node, so each node it names was in the graph then, its id below
  * the node count of that time. An earlier congruence may name the node: a node
  * that duplicates another has its congruence recorded when it is made
  * (`EGraph`'s made duplicates), before the step's own union is worked off the
  * agenda (HEDGEHOG_SEED 177134381559808: on
  * `(λx_0. x_0) + (λx_0. λx_1. x_0) + (λx_0. x_0)` union 29 built node 32,
  * which union 28, a congruence, names).
  *
  * Purpose: catch a `built` filled with the matched node, with a node outside
  * the union, or with a node the graph already held (a hash-consed hit), any of
  * which would make a trace take a step back along the wrong edge.
  */
class UnionBuiltLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts
  import RewriteTraceLawTest.closed
  import RewriteTraceLawTest.equation

  private val lemmas: Vector[LemmaSides[NoFacts.type]] = Vector(
    equation(0, "λa. λb. (a + b)", "λa. λb. (b + a)"),
    equation(1, "λa. λb. λc. ((a + b) + c)", "λa. λb. λc. (a + (b + c))"),
    equation(2, "λa. (a + a)", "λa. a"),
    equation(3, "λa. λb. (λx. λy. x) a b", "λa. λb. a")
  )

  private val index: StandardLibraryIndex[NoFacts.type] = StandardLibraryIndex(
    NoFacts,
    Vector.empty,
    lemmas,
    Vector.empty,
    Vector.empty
  )

  /** `RewriteTraceLawTest`'s budget for the same lemmas and programs. */
  private val budget: Int = 24

  private val saturator: StandardSaturator[NoFacts.type] = StandardSaturator(
    SaturationOptions(
      lemmas.map(_.lemma),
      BuiltInRule.beforeOptIn,
      budget,
      BaselineLemmaEncoding,
      ClosureCompilation,
      StandardIndexer.of[com.yang_bo.gezi.ir.NoFacts.type],
      StandardOrientationCompiler,
      MemoRetention.Kept,
      com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts)
    )
  )

  private val closedText: Gen[String] =
    HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** A choice of two to four closed terms, or a closed term in choice with K
    * applied to two, so that the lemma instances and the β rule both make
    * nodes.
    */
  private val programs: Gen[String] =
    Gen.choice1(
      closedText
        .list(Range.linear(2, 4))
        .map(_.map(member => s"($member)").mkString(" + ")),
      for
        context <- closedText
        first <- closedText
        second <- closedText
      yield s"($context) + (λk. λl. k) ($first) ($second)"
    )

  /** The choice of two distinct closed terms: the commutativity's instance adds
    * `second + first`, a node the input does not hold. (K applied to two is no
    * such program: on `(λx_0. x_0) + (λk. λl. k) (λx_0. x_0) (λx_0. x_0)` every
    * union's added side was a node the graph held, HEDGEHOG_SEED
    * 178098943363618.)
    */
  private val swappedChoices: Gen[String] =
    for
      first <- closedText
      second <- closedText.filter(_ != first)
    yield s"($first) + ($second)"

  /** Purpose: catch a `built` never filled, under which the law below holds
    * vacuously.
    */
  stoppableProperty(
    "a choice of two distinct terms records a union with a built node"
  ) { stopped =>
    swappedChoices
      .forAllWithLog(identity)
      .map(program =>
        val run = saturator.saturated(
          index,
          Vector(closed(program)),
          true,
          StopSignal.completedWith(stopped)
        )
        Result
          .assert(run.graph.unions.exists(_.built.isDefined))
          .log(s"${run.graph.unions.size} unions, none built")
      )
  }

  stoppableProperty(
    "a union's built node is one of its nodes and newer than every node an earlier step's union names"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val run = saturator.saturated(
          index,
          Vector(closed(program)),
          true,
          StopSignal.completedWith(stopped)
        )
        val unions = run.graph.unions
        val (problems, _) = unions.zipWithIndex.foldLeft(
          (Vector.empty[String], -1)
        ) { case ((found, newestNamed), (union, place)) =>
          val problem = union.built.flatMap(node =>
            if node != union.first && node != union.second then
              Some(
                s"union $place: built $node is neither ${union.first} nor ${union.second}"
              )
            else if node <= newestNamed then
              Some(
                s"union $place: built $node is not above $newestNamed, a node an earlier step's union names"
              )
            else None
          )
          val named = union.justification match
            case com.yang_bo.gezi.egraph.Justification.Congruence => newestNamed
            case _ => newestNamed.max(union.first).max(union.second)
          (found ++ problem, named)
        }
        val built = unions.count(_.built.isDefined)
        Result
          .assert(problems.isEmpty)
          .log(problems.mkString("\n"))
          .log(s"${unions.size} unions, $built built")
      )
  }

  /** Purpose: catch a union's made nodes (`UnionRecord.made`) that are not what
    * its step built: a range whose first node is a node an earlier step's union
    * names (a node the step was given, not one it made), or one holding a node
    * the built root does not reach through the range, either of which would
    * make a trace take a node's term from a step that did not make it.
    */
  stoppableProperty(
    "a union's made nodes are what its built node reaches through them, above every node an earlier step's union names"
  ) { stopped =>
    programs
      .forAllWithLog(identity)
      .map(program =>
        val run = saturator.saturated(
          index,
          Vector(closed(program)),
          true,
          StopSignal.completedWith(stopped)
        )
        val graph = run.graph
        val (problems, _) = graph.unions.zipWithIndex.foldLeft(
          (Vector.empty[String], -1)
        ) { case ((found, newestNamed), (union, place)) =>
          val problem = union.made.flatMap(made =>
            // The nodes of the range the built node reaches through it, its children before it.
            val reached =
              (made.first to made.last).reverse.foldLeft(Set(made.last)) {
                (reaching, node) =>
                  if reaching.contains(node) then
                    reaching ++ graph
                      .madeLayer(node)
                      .children
                      .filter(child => child >= made.first)
                  else reaching
              }
            if made.first > made.last then
              Some(s"union $place: made ${made.first} to ${made.last}")
            else if made.first <= newestNamed then
              Some(
                s"union $place: made from ${made.first}, not above $newestNamed, a node an earlier step's union names"
              )
            else
              (made.first to made.last)
                .find(node => !reached.contains(node))
                .map(node =>
                  s"union $place: made node $node of ${made.first} to ${made.last} is not reached from ${made.last}"
                )
          )
          val named = union.justification match
            case com.yang_bo.gezi.egraph.Justification.Congruence => newestNamed
            case _ => newestNamed.max(union.first).max(union.second)
          (found ++ problem, named)
        }
        val ranges =
          graph.unions.flatMap(_.made).map(made => made.last - made.first + 1)
        Result
          .assert(problems.isEmpty)
          .log(problems.mkString("\n"))
          .log(s"${ranges.size} ranges, ${ranges.sum} nodes made")
      )
  }
