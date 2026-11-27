package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily

import gezi.frontend.Term
import gezi.frontend.Term.λ

/** The points of the hard contest corpus and the pieces they are built from:
  * the port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_hard_clauses.pl`), which
  * `contest_hard` included into its module. Each point's comment, intended
  * answer and target algorithm are in that file, whose facts are the data of
  * `problems/hard_clauses`; the facts this code uses (the constructors of graph
  * nodes, trees and objects, the certificates, `same_order/8`,
  * `period_fields/3` and `repmin_values/2`) are read from
  * `problems/hard_clauses`. The sizes drawn for the sized points are read from
  * `problems/hard_parameters`.
  */
final class HardClauses(corpora: Corpora):

  import corpora.prelude.*

  private def contest = corpora.contest

  private def clausesFile: ProblemFamily = corpora.contestHardClauses

  /** `contest_hard_parameters:drawn_size(Point, Parameter, Size)`. */
  def drawnSize(point: String, parameter: String): Int =
    ProblemData.small(
      corpora.contestHardParameters
        .row("drawn_size", Map(0 -> point, 1 -> parameter))(2)
    )

  def numeral(count: Int): ProblemTerm = contest.numeral(count)

  /** `ones(Count)`. */
  def ones(count: Int): Vector[Int] = Vector.fill(count)(1)

  /** `natural_plus`: m + n by recursion on n. */
  val naturalPlus: ProblemTerm =
    fixpoint(λ(self => λ(m => λ(n => n(m)(λ(n1 => successor(self(m)(n1))))))))

  // ==== H1. streams of coprime periods ====

  val streamEqual: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            left(right(trueValue)(λ(_ => λ(_ => falseValue))))(
              λ(leftHead =>
                λ(leftTail =>
                  right(falseValue)(
                    λ(rightHead =>
                      λ(rightTail =>
                        naturalEqual(leftHead)(rightHead)(
                          self(leftTail)(rightTail)
                        )(falseValue)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  def periodic(labels: Seq[Int]): ProblemTerm = contest.cyclicLabels(labels)

  def streamPeriodsEqualSmall: ProblemTerm =
    streamEqual(periodic(ones(5)))(periodic(ones(7)))
  def streamPeriodsEqualMedium: ProblemTerm =
    streamEqual(periodic(ones(23)))(periodic(ones(29)))
  def streamPeriodsEqualLarge: ProblemTerm =
    streamEqual(periodic(ones(61)))(periodic(ones(67)))
  def streamPeriodsDifferLarge: ProblemTerm =
    streamEqual(periodic(ones(61)))(periodic(ones(66) :+ 2))
  def streamPeriodsEqualUnrolled: ProblemTerm =
    streamEqual(contest.labelsList(ones(35), nil))(
      contest.labelsList(ones(35), nil)
    )

  // ==== H2. recursive types of coprime periods ====

  /** `period_fields(Kind, Next)`; the fact of `next_only` is read from the
    * file, the other two kinds are rules.
    */
  private def periodFields(
      kind: String,
      next: ProblemTerm
  ): Vector[(String, ProblemTerm)] = kind match
    case "with_value" => Vector("value" -> contest.typeNatural, "next" -> next)
    case "next_only"  => periodFieldsFact(next)
    case "wants_boolean" =>
      Vector("value" -> contest.typeBoolean, "next" -> next)
    case other => throw IllegalArgumentException(s"no kind $other")

  /** The row `period_fields(next_only, Next, [next-Next])`, its list of named
    * fields read from the table: the row names its parameter by the text of its
    * second field, and each field is the plain pair of its name and that
    * parameter, `λtuple. tuple Name Parameter`.
    */
  private def periodFieldsFact(
      next: ProblemTerm
  ): Vector[(String, ProblemTerm)] =
    val arguments = clausesFile.row("period_fields", Map(0 -> "next_only"))
    val parameter = ProblemData.text(arguments(1))
    ProblemData
      .list(arguments(2))
      .map(field =>
        ProblemData.alternative(field, 1) match
          case (0, Vector(name, value))
              if ProblemData.text(value) == parameter =>
            ProblemData.text(name) -> next
          case other =>
            throw IllegalArgumentException(s"period_fields: field $other")
      )

  /** `period_record(Kinds)`. */
  def periodRecord(kinds: Seq[String]): ProblemTerm =
    fixpoint(λ(self => periodRecords(kinds, self)))

  private def periodRecords(
      kinds: Seq[String],
      self: ProblemTerm
  ): ProblemTerm =
    kinds.foldRight(self)((kind, inner) =>
      contest.recordNamed(periodFields(kind, inner)*)
    )

  /** `kinds(Count, Kind)`. */
  def kinds(count: Int, kind: String): Vector[String] = Vector.fill(count)(kind)

  /** `unrolled_period_record(Depth, FieldsOf)`. */
  def unrolledPeriodRecord(depth: Int, fieldsOf: String): ProblemTerm =
    (1 to depth).foldLeft(contest.typeRecord(Vector.empty))((inner, _) =>
      contest.recordNamed(periodFields(fieldsOf, inner)*)
    )

  def typePeriodsSubtypeSmall: ProblemTerm =
    contest.subtype(periodRecord(kinds(5, "with_value")))(
      periodRecord(kinds(7, "next_only"))
    )
  def typePeriodsSubtypeLarge: ProblemTerm =
    contest.subtype(periodRecord(kinds(17, "with_value")))(
      periodRecord(kinds(19, "next_only"))
    )
  def typePeriodsNotSubtype: ProblemTerm =
    contest.subtype(periodRecord(kinds(17, "with_value")))(
      periodRecord(kinds(18, "next_only") :+ "wants_boolean")
    )
  def typePeriodsSubtypeUnrolled: ProblemTerm =
    contest.subtype(unrolledPeriodRecord(35, "with_value"))(
      unrolledPeriodRecord(35, "next_only")
    )

  // ==== H3. exponential call by name ====

  /** `conjunction_chain(Depth)`. */
  def conjunctionChain(depth: Int): ProblemTerm =
    (1 to depth).foldLeft(trueValue)((inner, _) =>
      λ(shared => contest.conjunction(shared)(shared))(inner)
    )

  def sharingConjunctionChain: ProblemTerm = conjunctionChain(26)
  def sharingConjunctionChainUnrolled: ProblemTerm = conjunctionChain(8)

  // ==== H4. safety games on cyclic graphs ====

  /** `graph_node(Bad, Successors)`, the fact read from the file. */
  def graphNode(bad: ProblemTerm, successors: ProblemTerm): ProblemTerm =
    clausesFile.program("graph_node", bad, successors)

  def graphNodeList(nodes: Seq[ProblemTerm]): ProblemTerm =
    nodes.foldRight(nil)((node, rest) => cons(node)(rest))

  val safe: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(node =>
          node(
            λ(bad =>
              λ(successors =>
                bad(falseValue)(
                  fixpoint(
                    λ(any =>
                      λ(list =>
                        list(falseValue)(
                          λ(head => λ(tail => or(self(head))(any(tail))))
                        )
                      )
                    )
                  )(successors)
                )
              )
            )
          )
        )
      )
    )

  def goodNode(successors: Seq[ProblemTerm]): ProblemTerm =
    graphNode(falseValue, graphNodeList(successors))

  def badLeaf: ProblemTerm = graphNode(trueValue, nil)

  /** `diamond(Depth, Bottom)`. */
  def diamond(depth: Int, bottom: ProblemTerm): ProblemTerm =
    λ(bottomVariable => diamondLayers(depth, bottomVariable))(bottom)

  private def diamondLayers(depth: Int, below: ProblemTerm): ProblemTerm =
    if depth == 0 then safe(below)
    else
      λ(node => diamondLayers(depth - 1, node))(goodNode(Vector(below, below)))

  def selfLoop: ProblemTerm = fixpoint(λ(self => goodNode(Vector(self))))

  def safetyDiamondTrapped: ProblemTerm = diamond(22, badLeaf)
  def safetyDiamondTrappedUnrolled: ProblemTerm = diamond(6, badLeaf)

  /** `escape_behind_traps(Traps, TrapDepth)`. */
  def escapeBehindTraps(traps: Int, trapDepth: Int): ProblemTerm =
    λ(trap => safe(trapChain(traps, trap, selfLoop)))(
      diamondNode(trapDepth, badLeaf)
    )

  /** `trap_chain(Traps, Trap, Loop)`. */
  def trapChain(traps: Int, trap: ProblemTerm, loop: ProblemTerm): ProblemTerm =
    (1 to traps).foldLeft(loop)((next, _) => goodNode(Vector(trap, next)))

  /** `diamond_node(Depth, Bottom)`. */
  def diamondNode(depth: Int, bottom: ProblemTerm): ProblemTerm =
    λ(bottomVariable => diamondNodeLayers(depth, bottomVariable))(bottom)

  private def diamondNodeLayers(depth: Int, below: ProblemTerm): ProblemTerm =
    if depth == 0 then below
    else
      λ(node => diamondNodeLayers(depth - 1, node))(
        goodNode(Vector(below, below))
      )

  def safetyEscapeBehindTraps: ProblemTerm = escapeBehindTraps(12, 16)

  def safetyEscapeBehindTrapsUnrolled: ProblemTerm =
    λ(trapVariable => safe(trapChain(3, trapVariable, badLeaf)))(
      diamondNode(4, badLeaf)
    )

  // ==== H5. an infinite path whose nodes are rebuilt ====

  def generatedPath(rebuild: ProblemTerm): ProblemTerm =
    safe(
      fixpoint(
        λ(self => λ(argument => goodNode(Vector(self(rebuild(argument))))))
      )(zero)
    )

  def plusMinus(constant: Int): ProblemTerm =
    λ(argument =>
      naturalDifference(naturalPlus(argument)(numeral(constant)))(
        numeral(constant)
      )
    )

  def boundedGeneratedPath(rebuild: ProblemTerm, count: Int): ProblemTerm =
    safe(
      fixpoint(
        λ(self =>
          λ(argument =>
            λ(remaining =>
              remaining(badLeaf)(
                λ(fewer => goodNode(Vector(self(rebuild(argument))(fewer))))
              )
            )
          )
        )
      )(zero)(numeral(count))
    )

  def pathRebuiltByIdentity: ProblemTerm = generatedPath(identity)
  def pathRebuiltByPlusMinusSmall: ProblemTerm = generatedPath(plusMinus(3))
  def pathRebuiltByPlusMinusLarge: ProblemTerm = generatedPath(plusMinus(40))
  def pathRebuiltUnrolled: ProblemTerm = boundedGeneratedPath(plusMinus(40), 5)

  // ==== H6. laziness guards ====

  val diverge: ProblemTerm = fixpoint(
    λ(self => λ(natural => self(successor(natural))))
  )

  val endsCarrying: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(node =>
          λ(_ =>
            node(trueValue)(λ(head => λ(tail => self(tail)(diverge(head)))))
          )
        )
      )
    )

  def lassoEndsCarryingJunk: ProblemTerm =
    endsCarrying(contest.lasso(30, 30))(zero)
  def acyclicEndsCarryingJunk: ProblemTerm =
    endsCarrying(contest.acyclic(120))(zero)
  def acyclicEndsCarryingJunkUnrolled: ProblemTerm =
    endsCarrying(contest.acyclic(20))(zero)

  // ==== H7. cost guards ====

  def lassoLongPrefixEnds: ProblemTerm = contest.ends(contest.lasso(120, 3))
  def acyclicLongEnds: ProblemTerm = contest.ends(contest.acyclic(120))

  // ==== H8. a period against a growing spelling ====

  def streamPeriodAgainstMap: ProblemTerm =
    streamEqual(periodic(ones(3)))(contest.streamOnesByMap)
  def streamPeriodAgainstMapDiffer: ProblemTerm =
    streamEqual(periodic(Vector(1, 1, 2)))(contest.streamOnesByMap)

  // ==== H9. circular programs ====

  /** `tree_leaf(Natural)`, read from the file. */
  def treeLeaf(natural: ProblemTerm): ProblemTerm =
    clausesFile.program("tree_leaf", natural)

  /** `tree_node(Left, Right)`, read from the file. */
  def treeNode(left: ProblemTerm, right: ProblemTerm): ProblemTerm =
    clausesFile.program("tree_node", left, right)

  val naturalMinimum: ProblemTerm = λ(m => λ(n => naturalAtLeast(m)(n)(n)(m)))

  val repminGo: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(tree =>
          λ(minimum =>
            tree(
              λ(natural =>
                pair(λ(leafConstructor => λ(_ => leafConstructor(minimum))))(
                  natural
                )
              )
            )(
              λ(left =>
                λ(right =>
                  λ(leftResult =>
                    λ(rightResult =>
                      pair(
                        λ(_ =>
                          λ(nodeConstructor =>
                            nodeConstructor(first(leftResult))(
                              first(rightResult)
                            )
                          )
                        )
                      )(naturalMinimum(second(leftResult))(second(rightResult)))
                    )(self(right)(minimum))
                  )(self(left)(minimum))
                )
              )
            )
          )
        )
      )
    )

  val repmin: ProblemTerm =
    λ(tree => first(fixpoint(λ(knot => repminGo(tree)(second(knot))))))

  val leafSum: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(tree =>
          tree(λ(natural => natural))(
            λ(left => λ(right => naturalPlus(self(left))(self(right))))
          )
        )
      )
    )

  /** `balanced_tree(Values)`. */
  def balancedTree(values: Vector[Int]): ProblemTerm = values match
    case Vector(value) => treeLeaf(numeral(value))
    case _             =>
      val (front, back) = values.splitAt(values.length / 2)
      treeNode(balancedTree(front), balancedTree(back))

  /** `repmin_values(Size)`, read from the file. */
  def repminValues(size: String): Vector[Int] =
    ProblemData.smalls(clausesFile.row("repmin_values", Map(0 -> size))(1))

  def repminCheck(values: Vector[Int]): ProblemTerm =
    naturalEqual(leafSum(repmin(balancedTree(values))))(
      numeral(values.length * values.min)
    )

  def repminSumSmall: ProblemTerm = repminCheck(repminValues("small"))
  def repminSumLarge: ProblemTerm = repminCheck(repminValues("large"))

  // ==== H10. the Fibonacci stream modulo 2 ====

  val bitExclusiveOr: ProblemTerm =
    λ(a => λ(b => a(b)(λ(_ => b(numeral(1))(λ(_ => zero))))))

  val zipWith: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(function =>
          λ(left =>
            λ(right =>
              left(nil)(
                λ(leftHead =>
                  λ(leftTail =>
                    right(nil)(
                      λ(rightHead =>
                        λ(rightTail =>
                          cons(function(leftHead)(rightHead))(
                            self(function)(leftTail)(rightTail)
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  val streamTail: ProblemTerm =
    λ(stream => stream(nil)(λ(_ => λ(tail => tail))))

  val fibonacciParity: ProblemTerm =
    fixpoint(
      λ(stream =>
        cons(zero)(
          cons(numeral(1))(zipWith(bitExclusiveOr)(stream)(streamTail(stream)))
        )
      )
    )

  def fibonacciParityNth: ProblemTerm =
    contest.streamNth(numeral(30))(fibonacciParity)
  def fibonacciParityNthUnrolled: ProblemTerm =
    contest.streamNth(numeral(7))(fibonacciParity)
  def fibonacciParityPeriodic: ProblemTerm =
    streamEqual(fibonacciParity)(periodic(Vector(0, 1, 1)))
  def fibonacciParityNotPeriodic: ProblemTerm =
    streamEqual(fibonacciParity)(periodic(Vector(0, 1, 1, 0, 1, 0)))

  // ==== H11. the infinite natural ====

  val omega: ProblemTerm = fixpoint(λ(self => successor(self)))
  val omegaByTwo: ProblemTerm = fixpoint(λ(self => successor(successor(self))))
  val naturalCopy: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          natural(zero)(λ(predecessor => successor(self(predecessor))))
        )
      )
    )
  val omegaByCopy: ProblemTerm = fixpoint(
    λ(self => successor(naturalCopy(self)))
  )

  def omegaEqualByTwo: ProblemTerm = naturalEqual(omega)(omegaByTwo)
  def omegaEqualByCopy: ProblemTerm = naturalEqual(omega)(omegaByCopy)
  def omegaNotForty: ProblemTerm = naturalEqual(omegaByCopy)(numeral(40))
  def omegaAtLeastForty: ProblemTerm = naturalAtLeast(omegaByCopy)(numeral(40))

  // ==== H12. unproductive streams ====

  val streamUnproductive: ProblemTerm = fixpoint(
    λ(stream => cons(numeral(1))(streamTail(stream)))
  )
  val streamUnproductiveByMap: ProblemTerm =
    fixpoint(λ(stream => cons(numeral(1))(map(identity)(streamTail(stream)))))

  def streamUnproductiveSecond: ProblemTerm =
    contest.streamNth(numeral(1))(streamUnproductive)
  def streamUnproductiveByMapSecond: ProblemTerm =
    contest.streamNth(numeral(1))(streamUnproductiveByMap)
  def streamUnproductiveByMapFirst: ProblemTerm =
    contest.streamNth(zero)(streamUnproductiveByMap)

  def pathRebuiltByPlusMinusTiny: ProblemTerm = generatedPath(plusMinus(1))

  // ==== H13. accumulators recomputed to the same value ====

  val endsWithFlag: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(node =>
          λ(flag =>
            node(flag)(
              λ(_ =>
                λ(tail => self(tail)(contest.conjunction(flag)(trueValue)))
              )
            )
          )
        )
      )
    )

  def lassoEndsWithFlag: ProblemTerm =
    endsWithFlag(contest.lasso(8, 8))(trueValue)
  def acyclicEndsWithFlag: ProblemTerm =
    endsWithFlag(contest.acyclic(60))(trueValue)

  val reverseOnto: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(list =>
          λ(accumulated =>
            list(accumulated)(
              λ(head => λ(tail => self(tail)(cons(head)(accumulated))))
            )
          )
        )
      )
    )

  val listReverse: ProblemTerm = λ(list => reverseOnto(list)(nil))

  val endsWithList: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(node =>
          λ(accumulated =>
            node(trueValue)(
              λ(_ =>
                λ(tail => self(tail)(listReverse(listReverse(accumulated))))
              )
            )
          )
        )
      )
    )

  def lassoEndsWithReversedList: ProblemTerm =
    endsWithList(contest.lasso(8, 8))(
      contest.labelsList(Vector(1, 2, 3, 4, 5, 6), nil)
    )
  def acyclicEndsWithReversedList: ProblemTerm =
    endsWithList(contest.acyclic(60))(
      contest.labelsList(Vector(1, 2, 3, 4, 5, 6), nil)
    )

  // ==== H14. extensional growth ====

  def etaGeneratedPath: ProblemTerm =
    safe(
      fixpoint(
        λ(self =>
          λ(continuation =>
            goodNode(Vector(self(λ(argument => continuation(argument)))))
          )
        )
      )(identity)
    )

  def etaGeneratedPathBounded: ProblemTerm =
    safe(
      fixpoint(
        λ(self =>
          λ(continuation =>
            λ(remaining =>
              remaining(badLeaf)(
                λ(fewer =>
                  goodNode(
                    Vector(self(λ(argument => continuation(argument)))(fewer))
                  )
                )
              )
            )
          )
        )
      )(identity)(numeral(6))
    )

  def pathEtaExpanded: ProblemTerm = etaGeneratedPath
  def pathEtaExpandedUnrolled: ProblemTerm = etaGeneratedPathBounded

  // ==== H15. the answer, not the truth ====

  def treeBranch(
      label: ProblemTerm,
      left: ProblemTerm,
      right: ProblemTerm
  ): ProblemTerm =
    clausesFile.program("tree_branch", label, left, right)

  def treeLeafLabelled(label: ProblemTerm): ProblemTerm =
    clausesFile.program("tree_leaf_labelled", label)

  /** `same_tree(Order)`; the conjunction of the subtrees' comparisons is the
    * fact `same_order(Order, ...)` read from the file.
    */
  def sameTree(order: String): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(a =>
          λ(b =>
            a(
              λ(leafLabelA =>
                b(λ(leafLabelB => naturalEqual(leafLabelA)(leafLabelB)))(
                  λ(_ => λ(_ => λ(_ => falseValue)))
                )
              )
            )(
              λ(labelA =>
                λ(leftA =>
                  λ(rightA =>
                    b(λ(_ => falseValue))(
                      λ(labelB =>
                        λ(leftB =>
                          λ(rightB =>
                            contest.conjunction(naturalEqual(labelA)(labelB))(
                              clausesFile.template(
                                "same_order",
                                Map(0 -> order),
                                Map(
                                  1 -> contest.conjunction,
                                  2 -> self,
                                  3 -> leftA,
                                  4 -> leftB,
                                  5 -> rightA,
                                  6 -> rightB
                                ),
                                7
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  def leftSpine(rightLeaf: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        treeBranch(numeral(1), self, treeLeafLabelled(numeral(rightLeaf)))
      )
    )

  def treeSameLeftFirstDifferRight: ProblemTerm =
    sameTree("left_first")(leftSpine(5))(leftSpine(6))
  def treeSameRightFirstDifferRight: ProblemTerm =
    sameTree("right_first")(leftSpine(5))(leftSpine(6))
  def treeSameRightFirstEqual: ProblemTerm =
    sameTree("right_first")(leftSpine(5))(leftSpine(5))

  // ==== H16. the JIT framework's own ground ====

  /** `identity_tower(Height, Term)`. */
  def identityTower(height: Int, term: ProblemTerm): ProblemTerm =
    (1 to height).foldLeft(term)((inner, _) => identity(inner))

  def hotCountDown(height: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          natural(trueValue)(
            λ(predecessor => self(identityTower(height, predecessor)))
          )
        )
      )
    )

  def hotBodyCountDown(height: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          identityTower(height, natural)(trueValue)(
            λ(predecessor => self(predecessor))
          )
        )
      )
    )

  def jitHotBodyCountDown: ProblemTerm =
    hotBodyCountDown(40)(numeral(drawnSize("jit_hot_body_count_down", "count")))

  /** `s_k_k_tower(Height, Term)`. */
  def sKKTower(height: Int, term: ProblemTerm): ProblemTerm =
    (1 to height).foldLeft(term)((inner, _) =>
      λ(f => λ(g => λ(x => f(x)(g(x)))))(λ(a => λ(_ => a)))(λ(b => λ(_ => b)))(
        inner
      )
    )

  /** `compose_chain(Height)`. */
  def composeChain(height: Int): ProblemTerm =
    (1 to height).foldLeft(identity)((inner, _) =>
      λ(f => λ(g => λ(x => f(g(x)))))(identity)(inner)
    )

  def hotCombinatorCountDown(height: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          sKKTower(height, natural)(trueValue)(
            λ(predecessor => self(predecessor))
          )
        )
      )
    )

  def hotComposeCountDown(height: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          composeChain(height)(natural)(trueValue)(
            λ(predecessor => self(predecessor))
          )
        )
      )
    )

  def jitHotCombinatorCountDown: ProblemTerm =
    hotCombinatorCountDown(20)(
      numeral(drawnSize("jit_hot_combinator_count_down", "count"))
    )
  def jitHotComposeCountDown: ProblemTerm =
    hotComposeCountDown(30)(
      numeral(drawnSize("jit_hot_compose_count_down", "count"))
    )

  def coarsenedStreamLoop(rounds: Int, index: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          λ(stream =>
            natural(trueValue)(
              λ(predecessor =>
                naturalEqual(contest.streamNth(numeral(index))(stream))(
                  numeral(1)
                )(self(predecessor)(cons(numeral(1))(stream)))(falseValue)
              )
            )
          )
        )
      )
    )(numeral(rounds))(periodic(Vector(1)))

  def coarsenReusedStream: ProblemTerm = coarsenedStreamLoop(600, 400)
  def jitHotCountDown: ProblemTerm = hotCountDown(40)(numeral(800))
  def jitHotCountDownUnrolled: ProblemTerm = hotCountDown(40)(numeral(10))

  /** `tower_closures(Count)`. */
  def towerClosures(count: Int): ProblemTerm =
    (1 to count).foldLeft(nil)((rest, height) =>
      cons(λ(argument => identityTower(height, argument)))(rest)
    )

  val everyTrue: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(list =>
          list(trueValue)(
            λ(function =>
              λ(rest => contest.conjunction(function(trueValue))(self(rest)))
            )
          )
        )
      )
    )

  def jitManyCodes: ProblemTerm = everyTrue(towerClosures(150))

  val buildList: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          λ(accumulated =>
            natural(accumulated)(
              λ(predecessor => self(predecessor)(cons(numeral(1))(accumulated)))
            )
          )
        )
      )
    )

  def jitAccumulatingParameter: ProblemTerm =
    naturalEqual(length(buildList(numeral(400))(nil)))(numeral(400))

  // ==== H17. recomputed accumulators, the growth one level deeper ====

  val naturalPredecessor: ProblemTerm =
    λ(natural => natural(zero)(λ(predecessor => predecessor)))

  val endsWithCount: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(node =>
          λ(count =>
            node(trueValue)(
              λ(_ =>
                λ(tail => self(tail)(successor(naturalPredecessor(count))))
              )
            )
          )
        )
      )
    )

  def lassoEndsWithCount: ProblemTerm =
    endsWithCount(contest.lasso(8, 8))(numeral(3))
  def acyclicEndsWithCount: ProblemTerm =
    endsWithCount(contest.acyclic(60))(numeral(3))

  val endsWithPair: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(node =>
          λ(carried =>
            node(trueValue)(
              λ(_ =>
                λ(tail =>
                  self(tail)(
                    pair(contest.conjunction(first(carried))(trueValue))(nil)
                  )
                )
              )
            )
          )
        )
      )
    )

  def lassoEndsWithPair: ProblemTerm =
    endsWithPair(contest.lasso(8, 8))(pair(trueValue)(nil))
  def acyclicEndsWithPair: ProblemTerm =
    endsWithPair(contest.acyclic(60))(pair(trueValue)(nil))

  // ==== H18. olympiad problems written by their definitions ====

  val booleanNot: ProblemTerm = λ(boolean => boolean(falseValue)(trueValue))

  def subtractionGame(moves: Seq[Int]): ProblemTerm =
    fixpoint(
      λ(win =>
        λ(natural =>
          fixpoint(
            λ(any =>
              λ(remaining =>
                remaining(falseValue)(
                  λ(move =>
                    λ(rest =>
                      or(
                        contest.conjunction(naturalAtLeast(natural)(move))(
                          booleanNot(win(naturalDifference(natural)(move)))
                        )
                      )(any(rest))
                    )
                  )
                )
              )
            )
          )(contest.labelsList(moves, nil))
        )
      )
    )

  def gameSubtractionWin: ProblemTerm =
    subtractionGame(Vector(1, 3, 4))(numeral(24))
  def gameSubtractionLose: ProblemTerm =
    subtractionGame(Vector(1, 3, 4))(numeral(30))
  def gameSubtractionUnrolled: ProblemTerm =
    subtractionGame(Vector(1, 3, 4))(numeral(9))
  def gameSubtractionMedium: ProblemTerm =
    subtractionGame(Vector(1, 3, 4))(numeral(16))

  val coinWays: ProblemTerm =
    fixpoint(
      λ(ways =>
        λ(natural =>
          λ(coins =>
            natural(numeral(1))(
              λ(_ =>
                coins(zero)(
                  λ(coin =>
                    λ(rest =>
                      naturalPlus(
                        naturalAtLeast(natural)(coin)(
                          ways(naturalDifference(natural)(coin))(coins)
                        )(zero)
                      )(ways(natural)(rest))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  def coinChange(amount: Int, coins: Seq[Int], expected: Int): ProblemTerm =
    naturalEqual(coinWays(numeral(amount))(contest.labelsList(coins, nil)))(
      numeral(expected)
    )

  def coinsTwenty: ProblemTerm = coinChange(20, Vector(1, 2, 5), 29)
  def coinsTwentyWrongCount: ProblemTerm = coinChange(20, Vector(1, 2, 5), 30)
  def coinsUnrolled: ProblemTerm = coinChange(12, Vector(1, 2, 5), 13)

  def naturalModulo(modulus: Int): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(natural =>
          naturalAtLeast(natural)(numeral(modulus))(
            self(naturalDifference(natural)(numeral(modulus)))
          )(natural)
        )
      )
    )

  val congruentialMap: ProblemTerm =
    λ(natural =>
      naturalModulo(23)(
        naturalPlus(
          naturalPlus(
            naturalPlus(naturalPlus(naturalPlus(natural)(natural))(natural))(
              natural
            )
          )(natural)
        )(numeral(3))
      )
    )

  def reachTarget(target: Int): ProblemTerm =
    fixpoint(
      λ(reach =>
        λ(natural =>
          or(naturalEqual(natural)(numeral(target)))(
            reach(congruentialMap(natural))
          )
        )
      )
    )

  def congruentialUnreachable: ProblemTerm = reachTarget(5)(numeral(1))
  def congruentialReachable: ProblemTerm = reachTarget(0)(numeral(1))

  val smallCongruentialMap: ProblemTerm =
    λ(natural => naturalModulo(21)(naturalPlus(natural)(numeral(6))))

  def congruentialSmallUnreachable: ProblemTerm =
    fixpoint(
      λ(reach =>
        λ(natural =>
          or(naturalEqual(natural)(numeral(2)))(
            reach(smallCongruentialMap(natural))
          )
        )
      )
    )(numeral(1))

  def congruentialTinyUnreachable: ProblemTerm =
    fixpoint(
      λ(reach =>
        λ(natural =>
          or(naturalEqual(natural)(zero))(
            reach(naturalModulo(6)(naturalPlus(natural)(numeral(2))))
          )
        )
      )
    )(numeral(1))

  // ==== H19. where the baseline does not converge at all ====

  val bitFlip: ProblemTerm = λ(bit => bit(numeral(1))(λ(_ => zero)))

  private def alternating: ProblemTerm = fixpoint(
    λ(self => cons(zero)(map(bitFlip)(self)))
  )

  def theoremAlternation: ProblemTerm =
    streamEqual(alternating)(periodic(Vector(0, 1)))
  def theoremAlternationRefuted: ProblemTerm =
    streamEqual(alternating)(periodic(Vector(0)))

  val bitAnd: ProblemTerm = λ(a => λ(b => a(zero)(λ(_ => b))))

  val seriesAdd: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            left(right)(
              λ(leftHead =>
                λ(leftTail =>
                  right(left)(
                    λ(rightHead =>
                      λ(rightTail =>
                        cons(bitExclusiveOr(leftHead)(rightHead))(
                          self(leftTail)(rightTail)
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  val seriesScale: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(bit =>
          λ(series =>
            series(nil)(
              λ(head => λ(tail => cons(bitAnd(bit)(head))(self(bit)(tail))))
            )
          )
        )
      )
    )

  val seriesMultiply: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            left(nil)(
              λ(head =>
                λ(tail =>
                  seriesAdd(seriesScale(head)(right))(
                    cons(zero)(self(tail)(right))
                  )
                )
              )
            )
          )
        )
      )
    )

  val zeros: ProblemTerm = fixpoint(λ(self => cons(zero)(self)))

  def onePlusX: ProblemTerm = cons(numeral(1))(cons(numeral(1))(zeros))

  def seriesProductIdentity: ProblemTerm =
    streamEqual(seriesMultiply(onePlusX)(periodic(Vector(1))))(
      cons(numeral(1))(zeros)
    )
  def seriesProductRefuted: ProblemTerm =
    streamEqual(seriesMultiply(onePlusX)(periodic(Vector(1))))(
      periodic(Vector(1))
    )

  val indexedRecordOperator: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(index =>
          contest.recordNamed(
            "head" -> contest.typeNatural,
            "tail" -> self(successor(index))
          )
        )
      )
    )

  def streamRecordType: ProblemTerm =
    contest.recursiveType(self =>
      contest.recordNamed("head" -> contest.typeNatural, "tail" -> self)
    )

  def typeDeadIndexSubtype: ProblemTerm =
    contest.subtype(indexedRecordOperator(zero))(streamRecordType)

  def typeDeadIndexNotSubtype: ProblemTerm =
    contest.subtype(streamRecordType)(
      fixpoint(
        λ(self =>
          λ(index =>
            contest.recordNamed(
              "head" -> contest.typeBoolean,
              "tail" -> self(successor(index))
            )
          )
        )
      )(zero)
    )

  def typeRecomputedIndexSubtype: ProblemTerm =
    contest.subtype(
      fixpoint(
        λ(self =>
          λ(index =>
            contest.recordNamed(
              "head" -> contest.typeNatural,
              "tail" -> self(naturalPredecessor(successor(index)))
            )
          )
        )
      )(numeral(3))
    )(streamRecordType)

  // ==== H20. symbolic computation by value ====

  val booleanEqual: ProblemTerm =
    λ(left => λ(right => left(right)(booleanNot(right))))

  val regexEquivalent: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            contest.conjunction(
              booleanEqual(contest.regexNullable(left))(
                contest.regexNullable(right)
              )
            )(
              self(contest.regexDerivative("smart")(contest.letter('a'))(left))(
                contest.regexDerivative("smart")(contest.letter('a'))(right)
              )
            )
          )
        )
      )
    )

  val grammarAStarByTwo: ProblemTerm =
    fixpoint(
      λ(grammar =>
        contest.regexAlternation(contest.regexEpsilon)(
          contest.regexConcatenation(contest.letterExpression('a'))(
            contest.regexAlternation(contest.regexEpsilon)(
              contest.regexConcatenation(contest.letterExpression('a'))(grammar)
            )
          )
        )
      )
    )

  val grammarEvenAs: ProblemTerm =
    fixpoint(
      λ(grammar =>
        contest.regexAlternation(contest.regexEpsilon)(
          contest.regexConcatenation(contest.letterExpression('a'))(
            contest.regexConcatenation(contest.letterExpression('a'))(grammar)
          )
        )
      )
    )

  def regexEquivalentStar: ProblemTerm =
    regexEquivalent(contest.grammarAStar)(grammarAStarByTwo)
  def regexInequivalentEven: ProblemTerm =
    regexEquivalent(contest.grammarAStar)(grammarEvenAs)
  def regexEquivalentEven: ProblemTerm =
    regexEquivalent(grammarEvenAs)(grammarEvenAs)

  val mapTree: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(function =>
          λ(tree =>
            tree(
              λ(leafValue =>
                λ(leafLabel => λ(leaf => λ(_ => leaf(leafLabel))))(
                  function(leafValue)
                )
              )
            )(
              λ(label =>
                λ(left =>
                  λ(right =>
                    λ(branchLabel =>
                      λ(branchLeft =>
                        λ(branchRight =>
                          λ(_ =>
                            λ(branch =>
                              branch(branchLabel)(branchLeft)(branchRight)
                            )
                          )
                        )
                      )
                    )(function(label))(self(function)(left))(
                      self(function)(right)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  val isZero: ProblemTerm = λ(natural => natural(trueValue)(λ(_ => falseValue)))

  val allZeroTree: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(tree =>
          tree(λ(leafLabel => isZero(leafLabel)))(
            λ(label =>
              λ(left =>
                λ(right =>
                  contest.conjunction(isZero(label))(
                    contest.conjunction(self(right))(self(left))
                  )
                )
              )
            )
          )
        )
      )
    )

  private def treeByMaps(leafLabel: ProblemTerm): ProblemTerm =
    fixpoint(
      λ(self =>
        treeBranch(
          zero,
          mapTree(naturalPredecessor)(mapTree(successor)(self)),
          treeLeafLabelled(leafLabel)
        )
      )
    )

  def treeZeroByMaps: ProblemTerm = allZeroTree(treeByMaps(zero))
  def treeZeroByMapsRefuted: ProblemTerm = allZeroTree(treeByMaps(numeral(1)))

  // ==== H21. common material ====

  /** `zeros_list(Count)`. */
  def zerosList(count: Int): ProblemTerm =
    contest.labelsList(Vector.fill(count)(0), nil)

  val listHead: ProblemTerm = λ(list => list(zero)(λ(head => λ(_ => head))))

  def commonLengthOfMap: ProblemTerm =
    naturalEqual(length(map(successor)(zerosList(200))))(numeral(200))
  def commonAppendLength: ProblemTerm =
    naturalEqual(length(append(zerosList(100))(zerosList(50))))(numeral(150))
  def commonReverseTwice: ProblemTerm =
    naturalEqual(
      listHead(listReverse(listReverse(contest.labelsList(1 to 30, nil))))
    )(numeral(1))
  def commonAllZero: ProblemTerm = contest.everyElementIs(zero)(zerosList(200))

  // ==== H22, H24. coinductive typing ====

  def objectTriple: ProblemTerm = clausesFile.program("object_triple")
  def objectTag: ProblemTerm = clausesFile.program("object_tag")
  def objectMethod: ProblemTerm = clausesFile.program("object_method")
  def objectBase: ProblemTerm = clausesFile.program("object_base")
  def naturalCertificate: ProblemTerm =
    clausesFile.program("natural_certificate")
  def identityOf: ProblemTerm = clausesFile.program("identity_of")
  def noHead: ProblemTerm = clausesFile.program("no_head")
  def flip: ProblemTerm = clausesFile.program("flip")

  def badObject: ProblemTerm = objectTriple(falseValue)(identity)(falseValue)

  def symbolGenerator(judgment: ProblemTerm): ProblemTerm =
    λ(self =>
      objectTriple(trueValue)(λ(that => identityOf(judgment(that))(self)))(
        falseValue
      )
    )

  def symbolOf(judgment: ProblemTerm): ProblemTerm =
    λ(left => symbolGenerator(judgment)(left(left)))(
      λ(right => symbolGenerator(judgment)(right(right)))
    )

  def judgmentGenerator(memberOf: String): ProblemTerm =
    λ(judge =>
      λ(subject =>
        objectTag(subject)(
          objectBase(subject)(naturalCertificate)(
            judge(objectMethod(subject)(member(memberOf, judge)))
          )
        )(judge(subject)(λ(_ => λ(secondMember => secondMember))))
      )
    )

  /** `member_of(MemberOf, Judge)`. */
  def member(memberOf: String, judge: ProblemTerm): ProblemTerm = memberOf match
    case "symbol" => symbolOf(judge)
    case "pair"   => pairMemberOf(judge)
    case other    => throw IllegalArgumentException(s"no member kind $other")

  def naturalJudgment(memberOf: String): ProblemTerm =
    λ(left => judgmentGenerator(memberOf)(left(left)))(
      λ(right => judgmentGenerator(memberOf)(right(right)))
    )

  def typingNaturalSymbol: ProblemTerm =
    λ(judge => judge(symbolOf(judge)))(naturalJudgment("symbol"))

  def returnsBadObject: ProblemTerm =
    objectTriple(trueValue)(λ(_ => badObject))(falseValue)

  def typingNaturalReturnsBad: ProblemTerm =
    naturalJudgment("symbol")(returnsBadObject)
  def typingNaturalBadUnrolled: ProblemTerm =
    naturalJudgment("symbol")(badObject)

  def pairMemberGenerator(judgment: ProblemTerm): ProblemTerm =
    λ(self =>
      objectTriple(trueValue)(
        λ(that => identityOf(judgment(that))(otherMember(judgment, self)))
      )(falseValue)
    )

  def otherMember(judgment: ProblemTerm, self: ProblemTerm): ProblemTerm =
    objectTriple(trueValue)(λ(that => identityOf(judgment(that))(self)))(
      falseValue
    )

  def pairMemberOf(judgment: ProblemTerm): ProblemTerm =
    λ(left => pairMemberGenerator(judgment)(left(left)))(
      λ(right => pairMemberGenerator(judgment)(right(right)))
    )

  def typingNaturalPair: ProblemTerm =
    λ(judge => judge(pairMemberOf(judge)))(naturalJudgment("pair"))

  // ==== H23. suites ====

  val everyCase: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(check =>
          λ(cases =>
            cases(trueValue)(
              λ(caseTerm =>
                λ(rest =>
                  contest.conjunction(check(caseTerm))(self(check)(rest))
                )
              )
            )
          )
        )
      )
    )

  def caseList(cases: Seq[(ProblemTerm, ProblemTerm)]): ProblemTerm =
    cases.foldRight(nil)((caseTerm, rest) =>
      cons(pair(caseTerm._1)(caseTerm._2))(rest)
    )

  def expectedBoolean(expected: Boolean): ProblemTerm =
    if expected then trueValue else falseValue

  val regexMatchesSmart: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(expression =>
          λ(word =>
            word(contest.regexNullable(expression))(
              λ(letterVariable =>
                λ(rest =>
                  self(
                    contest.regexDerivative("smart")(letterVariable)(expression)
                  )(rest)
                )
              )
            )
          )
        )
      )
    )

  val regexSuiteCheck: ProblemTerm =
    λ(caseTerm =>
      booleanEqual(regexMatchesSmart(contest.grammarANBN)(first(caseTerm)))(
        second(caseTerm)
      )
    )

  def regexSuiteCases(largest: Int): Vector[(ProblemTerm, ProblemTerm)] =
    (1 to largest).toVector.flatMap(count =>
      Vector(
        contest.aNBNWord(count, Vector.empty) -> expectedBoolean(true),
        contest.aNBNWord(count, Vector('b')) -> expectedBoolean(false),
        contest.word(
          Vector.fill(count + 1)('a') ++ Vector.fill(count)('b')
        ) -> expectedBoolean(false)
      )
    )

  def regexSuite(largest: Int): ProblemTerm =
    everyCase(regexSuiteCheck)(caseList(regexSuiteCases(largest)))

  def suiteRegexANB: ProblemTerm = regexSuite(32)

  val listEqual: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            left(right(trueValue)(λ(_ => λ(_ => falseValue))))(
              λ(leftHead =>
                λ(leftTail =>
                  right(falseValue)(
                    λ(rightHead =>
                      λ(rightTail =>
                        contest.conjunction(naturalEqual(leftHead)(rightHead))(
                          self(leftTail)(rightTail)
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  val palindromeSuiteCheck: ProblemTerm =
    λ(caseTerm =>
      booleanEqual(
        listEqual(reverseOnto(first(caseTerm))(nil))(first(caseTerm))
      )(second(caseTerm))
    )

  def naturalList(naturals: Seq[Int]): ProblemTerm =
    naturals.foldRight(nil)((natural, rest) => cons(numeral(natural))(rest))

  def palindromeSuiteCases(largest: Int): Vector[(ProblemTerm, ProblemTerm)] =
    (1 to largest).toVector.flatMap(count =>
      val up = (0 until count).toVector.map(_ % 5)
      Vector(
        naturalList(up ++ up.reverse) -> expectedBoolean(true),
        naturalList((0 to count).toVector.map(_ % 5)) -> expectedBoolean(false)
      )
    )

  def palindromeSuite(largest: Int): ProblemTerm =
    everyCase(palindromeSuiteCheck)(caseList(palindromeSuiteCases(largest)))

  def suitePalindrome: ProblemTerm = palindromeSuite(45)

  def streamCertificate: ProblemTerm = λ(selector =>
    selector(λ(_ => badObject))(λ(_ => λ(witness => λ(_ => witness))))
  )

  // ==== H29. probe cycles ====

  def probeCycle(kind: String): ProblemTerm = kind match
    case "and_false" => fixpoint(λ(x => x(falseValue)(falseValue)))
    case "if_false"  => fixpoint(λ(x => x(falseValue)(x)))
    case "and_or" => fixpoint(λ(x => x(trueValue)(x)(falseValue)(falseValue)))
    case other    => throw IllegalArgumentException(s"no probe cycle $other")

  def flipCycleHalf: ProblemTerm =
    λ(p => flip(p(p))(λ(z => z))(flip)(λ(x => x(x))))

  def selfApplicationFlipCycle: ProblemTerm = flipCycleHalf(flipCycleHalf)

  // ==== H30. cycles of the value map ====

  def valueMapCycle(length: String): ProblemTerm = length match
    case "two"   => fixpoint(λ(x => x(λ(_ => λ(_ => trueValue)))(falseValue)))
    case "three" =>
      fixpoint(λ(x => x(λ(_ => λ(_ => λ(_ => λ(_ => trueValue)))))(falseValue)))
    case other => throw IllegalArgumentException(s"no value map cycle $other")

  /** The points of `problems/hard_clauses`, by name. */
  def points: Map[String, () => ProblemTerm] = Map(
    "stream_periods_equal_small" -> (() => streamPeriodsEqualSmall),
    "stream_periods_equal_medium" -> (() => streamPeriodsEqualMedium),
    "stream_periods_equal_large" -> (() => streamPeriodsEqualLarge),
    "stream_periods_differ_large" -> (() => streamPeriodsDifferLarge),
    "stream_periods_equal_unrolled" -> (() => streamPeriodsEqualUnrolled),
    "type_periods_subtype_small" -> (() => typePeriodsSubtypeSmall),
    "type_periods_subtype_large" -> (() => typePeriodsSubtypeLarge),
    "type_periods_not_subtype" -> (() => typePeriodsNotSubtype),
    "type_periods_subtype_unrolled" -> (() => typePeriodsSubtypeUnrolled),
    "sharing_conjunction_chain" -> (() => sharingConjunctionChain),
    "sharing_conjunction_chain_unrolled" -> (() =>
      sharingConjunctionChainUnrolled
    ),
    "safety_diamond_trapped" -> (() => safetyDiamondTrapped),
    "safety_diamond_trapped_unrolled" -> (() => safetyDiamondTrappedUnrolled),
    "safety_escape_behind_traps" -> (() => safetyEscapeBehindTraps),
    "safety_escape_behind_traps_unrolled" -> (() =>
      safetyEscapeBehindTrapsUnrolled
    ),
    "path_rebuilt_by_identity" -> (() => pathRebuiltByIdentity),
    "path_rebuilt_by_plus_minus_small" -> (() => pathRebuiltByPlusMinusSmall),
    "path_rebuilt_by_plus_minus_large" -> (() => pathRebuiltByPlusMinusLarge),
    "path_rebuilt_unrolled" -> (() => pathRebuiltUnrolled),
    "lasso_ends_carrying_junk" -> (() => lassoEndsCarryingJunk),
    "acyclic_ends_carrying_junk" -> (() => acyclicEndsCarryingJunk),
    "acyclic_ends_carrying_junk_unrolled" -> (() =>
      acyclicEndsCarryingJunkUnrolled
    ),
    "lasso_long_prefix_ends" -> (() => lassoLongPrefixEnds),
    "acyclic_long_ends" -> (() => acyclicLongEnds),
    "stream_period_against_map" -> (() => streamPeriodAgainstMap),
    "stream_period_against_map_differ" -> (() => streamPeriodAgainstMapDiffer),
    "repmin_sum_small" -> (() => repminSumSmall),
    "repmin_sum_large" -> (() => repminSumLarge),
    "fibonacci_parity_nth" -> (() => fibonacciParityNth),
    "fibonacci_parity_nth_unrolled" -> (() => fibonacciParityNthUnrolled),
    "fibonacci_parity_periodic" -> (() => fibonacciParityPeriodic),
    "fibonacci_parity_not_periodic" -> (() => fibonacciParityNotPeriodic),
    "omega_equal_by_two" -> (() => omegaEqualByTwo),
    "omega_equal_by_copy" -> (() => omegaEqualByCopy),
    "omega_not_forty" -> (() => omegaNotForty),
    "omega_at_least_forty" -> (() => omegaAtLeastForty),
    "stream_unproductive_second" -> (() => streamUnproductiveSecond),
    "stream_unproductive_by_map_second" -> (() =>
      streamUnproductiveByMapSecond
    ),
    "stream_unproductive_by_map_first" -> (() => streamUnproductiveByMapFirst),
    "path_rebuilt_by_plus_minus_tiny" -> (() => pathRebuiltByPlusMinusTiny),
    "lasso_ends_with_flag" -> (() => lassoEndsWithFlag),
    "acyclic_ends_with_flag" -> (() => acyclicEndsWithFlag),
    "lasso_ends_with_reversed_list" -> (() => lassoEndsWithReversedList),
    "acyclic_ends_with_reversed_list" -> (() => acyclicEndsWithReversedList),
    "path_eta_expanded" -> (() => pathEtaExpanded),
    "path_eta_expanded_unrolled" -> (() => pathEtaExpandedUnrolled),
    "tree_same_left_first_differ_right" -> (() => treeSameLeftFirstDifferRight),
    "tree_same_right_first_differ_right" -> (() =>
      treeSameRightFirstDifferRight
    ),
    "tree_same_right_first_equal" -> (() => treeSameRightFirstEqual),
    "jit_hot_count_down" -> (() => jitHotCountDown),
    "jit_hot_body_count_down" -> (() => jitHotBodyCountDown),
    "jit_hot_combinator_count_down" -> (() => jitHotCombinatorCountDown),
    "jit_hot_compose_count_down" -> (() => jitHotComposeCountDown),
    "coarsen_reused_stream" -> (() => coarsenReusedStream),
    "jit_hot_count_down_unrolled" -> (() => jitHotCountDownUnrolled),
    "jit_many_codes" -> (() => jitManyCodes),
    "jit_accumulating_parameter" -> (() => jitAccumulatingParameter),
    "lasso_ends_with_count" -> (() => lassoEndsWithCount),
    "acyclic_ends_with_count" -> (() => acyclicEndsWithCount),
    "lasso_ends_with_pair" -> (() => lassoEndsWithPair),
    "acyclic_ends_with_pair" -> (() => acyclicEndsWithPair),
    "game_subtraction_win" -> (() => gameSubtractionWin),
    "game_subtraction_lose" -> (() => gameSubtractionLose),
    "game_subtraction_unrolled" -> (() => gameSubtractionUnrolled),
    "coins_twenty" -> (() => coinsTwenty),
    "coins_twenty_wrong_count" -> (() => coinsTwentyWrongCount),
    "coins_unrolled" -> (() => coinsUnrolled),
    "congruential_unreachable" -> (() => congruentialUnreachable),
    "congruential_reachable" -> (() => congruentialReachable),
    "game_subtraction_medium" -> (() => gameSubtractionMedium),
    "congruential_small_unreachable" -> (() => congruentialSmallUnreachable),
    "congruential_tiny_unreachable" -> (() => congruentialTinyUnreachable),
    "common_length_of_map" -> (() => commonLengthOfMap),
    "common_append_length" -> (() => commonAppendLength),
    "common_reverse_twice" -> (() => commonReverseTwice),
    "common_all_zero" -> (() => commonAllZero),
    "theorem_alternation" -> (() => theoremAlternation),
    "theorem_alternation_refuted" -> (() => theoremAlternationRefuted),
    "series_product_identity" -> (() => seriesProductIdentity),
    "series_product_refuted" -> (() => seriesProductRefuted),
    "type_dead_index_subtype" -> (() => typeDeadIndexSubtype),
    "type_dead_index_not_subtype" -> (() => typeDeadIndexNotSubtype),
    "type_recomputed_index_subtype" -> (() => typeRecomputedIndexSubtype),
    "regex_equivalent_star" -> (() => regexEquivalentStar),
    "regex_inequivalent_even" -> (() => regexInequivalentEven),
    "regex_equivalent_even" -> (() => regexEquivalentEven),
    "tree_zero_by_maps" -> (() => treeZeroByMaps),
    "tree_zero_by_maps_refuted" -> (() => treeZeroByMapsRefuted),
    "typing_natural_symbol" -> (() => typingNaturalSymbol),
    "typing_natural_returns_bad" -> (() => typingNaturalReturnsBad),
    "typing_natural_bad_unrolled" -> (() => typingNaturalBadUnrolled),
    "typing_natural_pair" -> (() => typingNaturalPair),
    "suite_regex_a_n_b_n" -> (() => suiteRegexANB),
    "suite_palindrome" -> (() => suitePalindrome),
    "probe_cycle_and_false" -> (() => probeCycle("and_false")),
    "probe_cycle_if_false" -> (() => probeCycle("if_false")),
    "probe_cycle_and_or" -> (() => probeCycle("and_or")),
    "self_application_flip_cycle" -> (() => selfApplicationFlipCycle),
    "value_map_two_cycle" -> (() => valueMapCycle("two")),
    "value_map_three_cycle" -> (() => valueMapCycle("three"))
  )

  /** `contest_answers:certificate(Name, Term)`, the two certificates of the
    * hard corpus.
    */
  def certificates: Map[String, () => ProblemTerm] = Map(
    "natural" -> (() => naturalCertificate),
    "stream" -> (() => streamCertificate)
  )
