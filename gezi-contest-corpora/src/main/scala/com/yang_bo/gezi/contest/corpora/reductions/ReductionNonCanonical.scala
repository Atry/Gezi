package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemData

import com.yang_bo.gezi.frontend.Term

/** Non-canonical binary naturals, the port of
  * `problems/reduction_non_canonical`: sums whose operands carry leading zero
  * digits, so that the definitional plus answers a tree that is not the
  * canonical one of its value.
  */
object ReductionNonCanonical:

  private val family = "reduction_non_canonical"

  private val zero = Scott.leaf("zero")

  /** The tree the definitional plus of `problems/merge_dynamic` gives on the
    * trees, case by case (`plus_tree/3`).
    */
  def plusTree(left: ScottTree, right: ScottTree): ScottTree =
    (left, right) match
      case (ScottTree("zero", _), _) => right
      case (_, ScottTree("zero", _)) => left
      case (
            ScottTree("even", Vector(half)),
            ScottTree("even", Vector(other))
          ) =>
        ScottTree("even", Vector(plusTree(half, other)))
      case (ScottTree("even", Vector(half)), ScottTree("odd", Vector(other))) =>
        ScottTree("odd", Vector(plusTree(half, other)))
      case (ScottTree("odd", Vector(half)), ScottTree("even", Vector(other))) =>
        ScottTree("odd", Vector(plusTree(half, other)))
      case (ScottTree("odd", Vector(half)), ScottTree("odd", Vector(other))) =>
        ScottTree("even", Vector(incrementTree(plusTree(half, other))))
      case _ =>
        throw IllegalArgumentException(s"not binary trees: $left, $right")

  /** The definitional increment (`increment_tree/2`). */
  def incrementTree(tree: ScottTree): ScottTree = tree match
    case ScottTree("zero", _)            => ScottTree("odd", Vector(zero))
    case ScottTree("even", Vector(half)) => ScottTree("odd", Vector(half))
    case ScottTree("odd", Vector(half))  =>
      ScottTree("even", Vector(incrementTree(half)))
    case _ => throw IllegalArgumentException(s"not a binary tree: $tree")

  /** The canonical tree of the natural with its zero replaced by `padding`
    * evens over zero (`padded_tree/3`).
    */
  def paddedTree(number: BigInt, padding: Int): ScottTree =
    zeroReplaced(
      Scott.binaryTree(number),
      (1 to padding).foldLeft(zero)((inner, _) =>
        ScottTree("even", Vector(inner))
      )
    )

  private def zeroReplaced(tree: ScottTree, replacement: ScottTree): ScottTree =
    tree match
      case ScottTree("zero", _)          => replacement
      case ScottTree(name, Vector(half)) =>
        ScottTree(name, Vector(zeroReplaced(half, replacement)))
      case _ => throw IllegalArgumentException(s"not a binary tree: $tree")

  /** `plus Left Right` under the lets of the arithmetic, the operands the
    * canonical terms of the trees (`sum_surface/3`).
    */
  def sumSurface(
      group: ReductionGroup,
      left: ScottTree,
      right: ScottTree
  ): ProblemTerm =
    group.arithmetic.withArithmetic(names =>
      names.plus(group.scott.canonical("binary", left))(
        group.scott.canonical("binary", right)
      )
    )

  /** The operands of each point (`operands/3`): the facts read, then the sums
    * of the products of `problems/merge_binary` padded by 8 and 4.
    */
  def operands(group: ReductionGroup): Vector[(String, ScottTree, ScottTree)] =
    val stated = group.problems(family).rows("operands").map {
      case Vector(point, left, right) =>
        (
          ProblemData.text(point),
          ScottTrees.treeOf(left),
          ScottTrees.treeOf(right)
        )
      case other => throw IllegalArgumentException(s"not operands: $other")
    }
    val sums = group.problems(family).rows("sum_problem").map {
      case Vector(point, original) =>
        val (left, right, _) =
          group.products.claimed(ProblemData.text(original))
        (ProblemData.text(point), paddedTree(left, 8), paddedTree(right, 4))
      case other => throw IllegalArgumentException(s"not a sum problem: $other")
    }
    stated ++ sums

  /** The problems: each sum expects the definitional plus's tree. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    operands(group).map((point, left, right) =>
      ReductionProblem(
        point,
        sumSurface(group, left, right),
        "binary",
        Expected.One(plusTree(left, right)),
        Reduction.defaultLimits
      )
    )
