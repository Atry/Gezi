package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemField

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The set of the lengths of the walks from a start to a target, the port of
  * `problems/path_lengths`.
  */
object PathLengths:

  private val family = "path_lengths"

  /** The bound of a point relative to the least length of a walk, the
    * constructors of problems/path_lengths/bound in order: the factor times the
    * least length, and one less than the least length.
    */
  enum Bound:
    case Times(factor: Int)
    case OneShort

  /** The bound a field writes, a constructor of problems/path_lengths/bound
    * read by its position (`ProblemData.alternative`), times's field its
    * factor.
    */
  def bound(field: ProblemField): Bound =
    ProblemData.alternative(field, ProblemData.caseCount[Bound]) match
      case (0, Vector(factor)) => Bound.Times(ProblemData.small(factor))
      case (1, Vector())       => Bound.OneShort
      case (position, fields)  =>
        throw IllegalArgumentException(
          s"the bound of $family at position $position has ${fields.size} fields"
        )

  /** The program: under the lets of the nodes, `Y Lengths Bound Start`, Lengths
    * answering zero at the target and the successor of each successor's lengths
    * (`path_lengths_term/6`).
    */
  def pathLengthsTerm(
      attractors: Attractors,
      count: Int,
      edges: Vector[(Int, Int)],
      start: Int,
      target: Int,
      bound: Int
  ): ProblemTerm =
    Graphs.numeralLets(
      count,
      nodes =>
        val zero = attractors.attractorSurface("zero", Spelling.Direct)
        val lengths = λ(self =>
          λ(remaining =>
            λ(vertex =>
              members(
                Vector(
                  Graphs.numeralCase(
                    (0 until count).toVector.map(index =>
                      if index == target then zero else top
                    ),
                    vertex
                  ),
                  remaining(top)(
                    λ(predecessor =>
                      Graphs.numeralCase(
                        (0 until count).toVector.map(index =>
                          members(edges.collect {
                            case (from, to) if from == index =>
                              attractors.functionSurface(
                                "successor",
                                Spelling.Direct
                              )(self(predecessor)(nodes(to)))
                          })
                        ),
                        vertex
                      )
                    )
                  )
                )
              )
            )
          )
        )
        attractors.fixpoint(lengths)(unary(bound))(nodes(start))
    )

  /** The sorted lengths of at most `bound` of the walks from the start to the
    * target, by layers (`walk_lengths/6`).
    */
  def walkLengths(
      edges: Vector[(Int, Int)],
      start: Int,
      target: Int,
      bound: Int
  ): Vector[Int] =
    (0 to bound)
      .foldLeft((Vector(start), Vector.empty[Int])) {
        case ((layer, found), step) =>
          val next = layer
            .flatMap(from => edges.collect { case (`from`, to) => to })
            .distinct
            .sorted
          (next, if layer.contains(target) then found :+ step else found)
      }
      ._2

  /** The least length of a walk (`distance/5`). */
  def distance(
      count: Int,
      edges: Vector[(Int, Int)],
      start: Int,
      target: Int
  ): Int =
    walkLengths(edges, start, target, count * count).headOption
      .getOrElse(
        throw IllegalArgumentException(s"no walk from $start to $target")
      )

  /** The problems (`path_lengths_point/4`), the bound twice the distance or one
    * short of it.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("path_lengths_point").map {
      case Vector(point, shape, size, boundRule) =>
        val graph = Graphs.graph(Graphs.shape(shape), ProblemData.small(size))
        val least =
          distance(graph.count, graph.edges, graph.start, graph.target)
        val bound = this.bound(boundRule) match
          case Bound.Times(factor) => factor * least
          case Bound.OneShort      => least - 1
        ReductionProblem(
          ProblemData.text(point),
          pathLengthsTerm(
            group.attractors,
            graph.count,
            graph.edges,
            graph.start,
            graph.target,
            bound
          ),
          "unary",
          Reduction.expectedOf(
            walkLengths(graph.edges, graph.start, graph.target, bound)
              .map(Scott.unaryTree)
          ),
          Reduction.defaultLimits
        )
      case other =>
        throw IllegalArgumentException(s"not a path lengths point: $other")
    }
