package gezi.ematching

import gezi.ir.NativeSpecializer

/** Where a seed's steps end in a tree: the seed's number among the seeds
  * filed under its kind and key, and what its match is made of.
  */
final case class SeedEnd(
    seed: Int,
    orientation: Int,
    root: Register,
    bindings: Vector[Option[Register]]
)

/** The seeds filed under one kind and key, their equal leading steps
  * shared: a trie of their steps, each path compressed into one node. A run
  * of a tree runs its steps once for every way they succeed, as a seed's are
  * run; after each success it makes the match of every seed that ends there,
  * then runs each branch. A step two seeds share is equal in both, its
  * registers included, so that it reads the same entries in both; the tree
  * reads them once where the seeds run one by one would read them once per
  * seed.
  *
  * The matches of one seed come out of the tree in the order its own run
  * finds them, since the tree runs that seed's steps depth first in the same
  * order; a backend hands the matches of a key over grouped by seed number,
  * each group in the order found, which is the sequence the seeds run one by
  * one in their order would give.
  */
final case class SeedTree[C <: NativeSpecializer & Singleton](
    steps: Vector[Step[C]],
    ends: Vector[SeedEnd],
    branches: Vector[SeedTree[C]]
)

object SeedTree:

  /** The tree of the seeds, numbered by their position; the tree of no seed
    * runs no step and makes no match.
    */
  def of[C <: NativeSpecializer & Singleton](seeds: Vector[Seed[C]]): SeedTree[C] =
    if seeds.isEmpty then SeedTree[C](Vector.empty, Vector.empty, Vector.empty)
    else grown(seeds.zipWithIndex, 0)

  /** The tree of the numbered seeds, all of which begin with the same
    * `depth` steps: their longest common prefix after those steps, the seeds
    * that end there, and one branch for each next step, in the order the
    * seeds first take it.
    */
  private def grown[C <: NativeSpecializer & Singleton](seeds: Vector[(Seed[C], Int)], depth: Int): SeedTree[C] =
    val prefix = commonLength(seeds.map(_._1.steps), depth)
    val end = depth + prefix
    val (ending, going) = seeds.partition(_._1.steps.size == end)
    val nextSteps = going.map(_._1.steps(end)).distinct
    SeedTree(
      steps = seeds.head._1.steps.slice(depth, end),
      ends = ending.map((seed, number) =>
        SeedEnd(number, seed.orientation, seed.root, seed.bindings)
      ),
      branches = nextSteps.map(next =>
        grown(going.filter(_._1.steps(end) == next), end)
      )
    )

  /** The number of steps after `depth` that every sequence has, equal in
    * all.
    */
  private def commonLength[C <: NativeSpecializer & Singleton](sequences: Vector[Vector[Step[C]]], depth: Int): Int =
    val shortest = sequences.map(_.size).min - depth
    (0 until shortest)
      .find(offset =>
        sequences.exists(_(depth + offset) != sequences.head(depth + offset))
      )
      .getOrElse(shortest)

  /** The registers a run of the tree uses: one more than the largest a step
    * of it writes or a match of it reads, register 0 included.
    */
  def registerCount[C <: NativeSpecializer & Singleton](tree: SeedTree[C]): Int =
    1 + (0 +: (tree.steps.flatMap(writtenRegisters) ++
      tree.ends.flatMap(end => end.root +: end.bindings.flatten) ++
      tree.branches.map(registerCount(_) - 1))).max

  /** The registers the step writes, those of a witness's steps included. */
  private def writtenRegisters[C <: NativeSpecializer & Singleton](step: Step[C]): Vector[Register] = step match
    case Step.Layer(_, _, children)             => children
    case Step.Root(_, target)                   => Vector(target)
    case Step.EachHeadMember(_, _, target)      => Vector(target)
    case Step.EachMember(_, _, target)          => Vector(target)
    case Step.EachUser(_, _, target)            => Vector(target)
    case Step.EachPositionUser(_, _, _, target) => Vector(target)
    case Step.InstructionNode(_, target)             => Vector(target)
    case Step.Lookup(_, _, target)              => Vector(target)
    case Step.Once(steps)                       => steps.flatMap(writtenRegisters)
    case Step.Same(_, _) | Step.InstructionIn(_, _) | Step.HasClosure(_) =>
      Vector.empty
