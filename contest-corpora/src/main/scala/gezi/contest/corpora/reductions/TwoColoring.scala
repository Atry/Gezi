package gezi.contest.corpora.reductions

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** The proper two-colorings of a graph, the port of
  * the deleted Prolog file
  * (`git show 6ab16a338^:lambda_jit/corpora/contest_two_coloring.pl`): each coloring chosen node by node and
  * checked edge by edge, answered as a binary code.
  */
object TwoColoring:

  /** The program under the lets of the nodes: `Color (successor last) nil`
    * (`two_coloring_term/3`).
    */
  def twoColoringTerm(attractors: Attractors, count: Int, edges: Vector[(Int, Int)]): Term =
    Graphs.numeralLets(
      count,
      nodes =>
        val countNumeral = attractors.functionSurface("successor", Spelling.Direct)(nodes(count - 1))
        val nil = attractors.functionSurface("nil", Spelling.Direct)
        colorFunction(attractors, colors => edgeChecks(attractors, edges, nodes, colors))(countNumeral)(nil)
    )

  /** `Y (\self. \r. \colors. r Check (\p. Choice (\c. self p (cons c colors))))`,
    * Choice `[\f. f true, \s. s false]` (`color_function/2`).
    */
  private def colorFunction(attractors: Attractors, check: Term => Term): Term =
    val trueValue = attractors.attractorSurface("true", Spelling.Direct)
    val falseValue = attractors.attractorSurface("false", Spelling.Direct)
    val cons = attractors.functionSurface("cons", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(remaining =>
          λ(colors =>
            remaining(check(colors))(λ(predecessor =>
              members(Vector(λ(first => first(trueValue)), λ(second => second(falseValue))))(λ(chosen =>
                self(predecessor)(cons(chosen)(colors))
              ))
            ))
          )
        )
      )
    )

  /** For each edge, `equal (at colors from) (at colors to) [] Rest`, the
    * last Rest the code of the colors (`edge_checks/5`).
    */
  private def edgeChecks(attractors: Attractors, edges: Vector[(Int, Int)], nodes: Vector[Term], colors: Term): Term =
    edges.foldRight(codeFunction(attractors)(colors))((edge, rest) =>
      val equal = attractors.functionSurface("merge_symbols_equal", Spelling.Direct)
      equal(atFunction(attractors)(colors)(nodes(edge._1)))(atFunction(attractors)(colors)(nodes(edge._2)))(top)(rest)
    )

  /** The element of a list at a unary index (`at_function/1`). */
  private def atFunction(attractors: Attractors): Term =
    attractors.fixpoint(
      λ(self =>
        λ(list =>
          λ(index => list(top)(λ(head => λ(tail => index(head)(λ(predecessor => self(tail)(predecessor)))))))
        )
      )
    )

  /** The binary code of a list of Booleans, a leading one above them
    * (`code_function/1`).
    */
  private def codeFunction(attractors: Attractors): Term =
    val oddOne = attractors.functionSurface("binary_odd", Spelling.Direct)
    val oddTwo = attractors.functionSurface("binary_odd", Spelling.Direct)
    val even = attractors.functionSurface("binary_even", Spelling.Direct)
    val zero = attractors.attractorSurface("binary_zero", Spelling.Direct)
    attractors.fixpoint(
      λ(self => λ(list => list(oddOne(zero))(λ(bit => λ(rest => bit(oddTwo(self(rest)))(even(self(rest))))))))
    )

  /** `2^count` plus the colors as bits, node 0 the least significant
    * (`coloring_code/2`).
    */
  def coloringCode(colors: Vector[Int]): BigInt =
    (BigInt(1) << colors.size) + colors.zipWithIndex.map((color, position) => BigInt(color) << position).sum

  /** The sorted codes of the proper colorings: a base coloring by
    * breadth-first search of each component, then every component kept or
    * exchanged; none when the graph is not bipartite (`proper_colorings/3`).
    */
  def properColorings(count: Int, edges: Vector[(Int, Int)]): Vector[BigInt] =
    baseColoring(count, edges) match
      case None => Vector.empty
      case Some((base, components)) =>
        flipped(components, base)
          .map(colored => coloringCode((0 until count).toVector.map(node => colored.find(_._1 == node).get._2)))
          .distinct
          .sorted

  /** The base coloring, node and color pairs newest first, and the
    * components, newest first (`base_coloring/4`).
    */
  private def baseColoring(count: Int, edges: Vector[(Int, Int)]): Option[(List[(Int, Int)], List[List[Int]])] =
    (0 until count).foldLeft(Option((List.empty[(Int, Int)], List.empty[List[Int]]))) { (state, node) =>
      state.flatMap((colored, components) =>
        if colored.exists(_._1 == node) then Some((colored, components))
        else
          breadthFirstColored(Vector((node, 0)), edges, colored, List.empty).map((result, component) =>
            (result, component :: components)
          )
      )
    }

  @tailrec
  private def breadthFirstColored(
      queue: Vector[(Int, Int)],
      edges: Vector[(Int, Int)],
      colored: List[(Int, Int)],
      component: List[Int]
  ): Option[(List[(Int, Int)], List[Int])] =
    queue.headOption match
      case None => Some((colored, component))
      case Some((node, color)) =>
        colored.find(_._1 == node) match
          case Some((_, existing)) =>
            if existing != color then None else breadthFirstColored(queue.tail, edges, colored, component)
          case None =>
            val other = 1 - color
            val neighbours =
              edges.collect { case (`node`, neighbour) => (neighbour, other) } ++
                edges.collect { case (neighbour, `node`) => (neighbour, other) }
            breadthFirstColored(queue.tail ++ neighbours, edges, (node, color) :: colored, node :: component)

  /** Every combination of keeping or exchanging each component
    * (`flipped/3`).
    */
  private def flipped(components: List[List[Int]], base: List[(Int, Int)]): Vector[List[(Int, Int)]] =
    components match
      case Nil => Vector(base)
      case component :: rest =>
        Vector(false, true).flatMap(exchange =>
          val after =
            if exchange then base.map((node, color) => if component.contains(node) then (node, 1 - color) else (node, color))
            else base
          flipped(rest, after)
        )

  /** The ring of `count` nodes, `i -> i + 1 mod count` (`ring/3`). */
  def ring(count: Int): Vector[(Int, Int)] = (0 until count).toVector.map(node => (node, (node + 1) % count))

  /** The points and their graphs (`two_coloring_point/3`, clauses whose
    * graphs are computed).
    */
  val points: Vector[(String, Int, Vector[(Int, Int)])] = Vector(
    ("reduction_two_coloring_ring_small", 8, ring(8)),
    ("reduction_two_coloring_ring_large", 24, ring(24)),
    ("reduction_two_coloring_odd_ring_near_miss", 9, ring(9)),
    ("reduction_two_coloring_chord_near_miss", 8, (0, 2) +: ring(8))
  )

  /** The problems: the codes of the proper colorings. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points.map((point, count, edges) =>
      ReductionProblem(
        point,
        twoColoringTerm(group.attractors, count, edges),
        "binary",
        Expected.Trees(properColorings(count, edges).map(Scott.binaryTree)),
        Reduction.defaultLimits
      )
    )
