package com.yang_bo.gezi.ematching

import com.yang_bo.gezi.egraph.Head
import com.yang_bo.gezi.egraph.MemberShape
import com.yang_bo.gezi.egraph.PositionRole
import com.yang_bo.gezi.egraph.UserRole
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The two kinds of orientation: those whose added side is a metavariable or a
  * subpattern of the matched side, which only unite, and the others, which add
  * nodes. A delta is matched by the first kind before the second.
  */
enum SeedKind:
  case Merge
  case Add

/** The key a delta node is matched under: an application under `Apply` and
  * under each of its heads, a node of another shape under its shape, a node of
  * a class holding a closure state under `Closure`, and the node of an
  * instruction under that instruction.
  */
enum SeedKey[C <: NativeSpecializer & Singleton]:
  case Apply[C <: NativeSpecializer & Singleton]() extends SeedKey[C]
  case Headed(head: Head[C])
  case Parallel[C <: NativeSpecializer & Singleton]() extends SeedKey[C]
  case Choice[C <: NativeSpecializer & Singleton]() extends SeedKey[C]
  case Thunk[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole]
  ) extends SeedKey[C]
  case Closure[C <: NativeSpecializer & Singleton]() extends SeedKey[C]
  case InstructionNode(instruction: Configured[C])

/** The layer a node must have: its shape (the choice binary), and a thunk's
  * code and holes.
  */
enum LayerTemplate:
  case Apply
  case Parallel
  case Choice
  case Thunk(code: Code, holes: Vector[Hole])

/** A register: a place a step writes once and later steps read, holding a node;
  * register 0 holds the delta node a seed starts from.
  */
type Register = Int

/** One step of a seed. A step that writes a register writes one no step before
  * it wrote. The steps after an `Each` step run once for every entry it reads,
  * in the entries' order, skipping duplicates; a step whose check fails ends
  * the run it is in.
  */
enum Step[C <: NativeSpecializer & Singleton]:
  /** The node has the template's layer; its children, as the layer was made, go
    * to `children` in child order.
    */
  case Layer[C <: NativeSpecializer & Singleton](
      node: Register,
      template: LayerTemplate,
      children: Vector[Register]
  ) extends Step[C]

  /** The root of the node's class goes to `target`. */
  case Root[C <: NativeSpecializer & Singleton](
      node: Register,
      target: Register
  ) extends Step[C]

  /** The two registers hold the same node: a metavariable met again. */
  case Same[C <: NativeSpecializer & Singleton](
      first: Register,
      second: Register
  ) extends Step[C]

  /** The instruction's node is in the class whose root the register holds. */
  case InstructionIn(instruction: Configured[C], root: Register)

  /** The class whose root the register holds has a closure state. */
  case HasClosure[C <: NativeSpecializer & Singleton](root: Register)
      extends Step[C]

  /** The instruction's node, when the graph has added it, goes to `target`. */
  case InstructionNode(instruction: Configured[C], target: Register)

  /** The node whose layer has the template over the classes of the nodes at
    * `children`, in child order, when the graph has one, goes to `target`
    * (`GraphView.layerNode`). It reads no entry: congruence leaves one live
    * node of a signature, the one the signature table holds.
    */
  case Lookup[C <: NativeSpecializer & Singleton](
      template: LayerTemplate,
      children: Vector[Register],
      target: Register
  ) extends Step[C]

  case EachHeadMember(root: Register, head: Head[C], target: Register)

  case EachMember[C <: NativeSpecializer & Singleton](
      root: Register,
      shape: MemberShape,
      target: Register
  ) extends Step[C]

  case EachUser[C <: NativeSpecializer & Singleton](
      root: Register,
      role: UserRole,
      target: Register
  ) extends Step[C]

  /** Each user of the class at the position of its members or fillings. */
  case EachPositionUser[C <: NativeSpecializer & Singleton](
      root: Register,
      role: PositionRole,
      position: Int,
      target: Register
  ) extends Step[C]

  /** The first run of the inner steps that succeeds, its registers kept: a
    * witness, whose every match stands for all.
    */
  case Once(steps: Vector[Step[C]])

/** The steps that complete a match of an orientation's matched side from a
  * delta node at one of its positions, and where the match's root and the
  * metavariables' nodes are when they succeed; a metavariable no side mentions
  * has no register.
  */
final case class Seed[C <: NativeSpecializer & Singleton](
    orientation: Int,
    steps: Vector[Step[C]],
    root: Register,
    bindings: Vector[Option[Register]]
)

/** A building: the nodes to add for a side or a code body, a tree whose leaves
  * are values the caller gives (an instance's bindings, a β step's slot values)
  * and instructions, and whose layers are added children first.
  */
enum Building[C <: NativeSpecializer & Singleton]:
  /** The value the caller gives at the index. */
  case Value[C <: NativeSpecializer & Singleton](index: Int) extends Building[C]

  /** The node of the instruction, added when the graph lacks it. */
  case InstructionNode(instruction: Configured[C])

  /** The building of the code, with the same values: a body's subcode. */
  case CodeBody[C <: NativeSpecializer & Singleton](code: Code)
      extends Building[C]

  /** An application; `read` when the β rule reads it. */
  case Apply(function: Building[C], argument: Building[C], read: Boolean)

  case Parallel(left: Building[C], right: Building[C])

  case Choice(left: Building[C], right: Building[C])

  case Thunk(code: Code, holes: Vector[Hole], fillings: Vector[Building[C]])

/** What saturation needs of an orientation to apply an instance: the lemma that
  * justifies its union, which side goes first in the union, its added side, and
  * what tells two of its instances apart.
  */
final case class OrientationPlan[C <: NativeSpecializer & Singleton](
    lemma: LemmaIdentifier,
    direction: Direction,
    added: Building[C],
    essential: Vector[Int],
    shared: Vector[Building[C]]
)

/** A whole program: the seeds filed under each kind and key, each list in the
  * order its seeds' matches are handed over; the plan of every orientation, by
  * number; and the building of every code's body. It is first-order data: no
  * field holds a function.
  */
final case class Program[C <: NativeSpecializer & Singleton](
    seeds: Map[(SeedKind, SeedKey[C]), Vector[Seed[C]]],
    orientations: Vector[OrientationPlan[C]],
    codes: Map[Code, Building[C]]
):
  /** The seeds under each kind and key as the tree every backend runs, so that
    * the steps the seeds begin with in common are run once.
    */
  lazy val trees: Map[(SeedKind, SeedKey[C]), SeedTree[C]] =
    seeds.map((kindAndKey, filed) => kindAndKey -> SeedTree.of(filed))
