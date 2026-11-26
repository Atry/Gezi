package gezi.ematching

import gezi.egraph.Head
import gezi.egraph.MemberShape
import gezi.egraph.PositionRole
import gezi.egraph.UserRole
import gezi.ir.Code
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.LemmaIdentifier

/** The two kinds of orientation: those whose added side is a metavariable
  * or a subpattern of the matched side, which only unite, and the others,
  * which add nodes. A delta is matched by the first kind before the second.
  */
enum SeedKind:
  case Merge
  case Add

/** The key a delta node is matched under: an application under `Apply` and
  * under each of its heads, a node of another shape under its shape, a node
  * of a class holding a closure state under `Closure`, and the node of an
  * instruction under that instruction.
  */
enum SeedKey:
  case Apply
  case Headed(head: Head)
  case Parallel
  case Choice
  case Thunk(code: Code, holes: Vector[Hole])
  case Closure
  case InstructionNode(instruction: Instruction)

/** The layer a node must have: its shape (the choice binary), and a thunk's
  * code and holes.
  */
enum LayerTemplate:
  case Apply
  case Parallel
  case Choice
  case Thunk(code: Code, holes: Vector[Hole])

/** A register: a place a step writes once and later steps read, holding a
  * node; register 0 holds the delta node a seed starts from.
  */
type Register = Int

/** One step of a seed. A step that writes a register writes one no step
  * before it wrote. The steps after an `Each` step run once for every entry
  * it reads, in the entries' order, skipping duplicates; a step whose check
  * fails ends the run it is in.
  */
enum Step:
  /** The node has the template's layer; its children, as the layer was
    * made, go to `children` in child order.
    */
  case Layer(node: Register, template: LayerTemplate, children: Vector[Register])

  /** The root of the node's class goes to `target`. */
  case Root(node: Register, target: Register)

  /** The two registers hold the same node: a metavariable met again. */
  case Same(first: Register, second: Register)

  /** The instruction's node is in the class whose root the register holds. */
  case InstructionIn(instruction: Instruction, root: Register)

  /** The class whose root the register holds has a closure state. */
  case HasClosure(root: Register)

  /** The instruction's node, when the graph has added it, goes to `target`. */
  case InstructionNode(instruction: Instruction, target: Register)

  /** The node whose layer has the template over the classes of the nodes at
    * `children`, in child order, when the graph has one, goes to `target`
    * (`GraphView.layerNode`). It reads no entry: congruence leaves one live
    * node of a signature, the one the signature table holds.
    */
  case Lookup(template: LayerTemplate, children: Vector[Register], target: Register)

  case EachHeadMember(root: Register, head: Head, target: Register)

  case EachMember(root: Register, shape: MemberShape, target: Register)

  case EachUser(root: Register, role: UserRole, target: Register)

  /** Each user of the class at the position of its members or fillings. */
  case EachPositionUser(
      root: Register,
      role: PositionRole,
      position: Int,
      target: Register
  )

  /** The first run of the inner steps that succeeds, its registers kept: a
    * witness, whose every match stands for all.
    */
  case Once(steps: Vector[Step])

/** The steps that complete a match of an orientation's matched side from a
  * delta node at one of its positions, and where the match's root and the
  * metavariables' nodes are when they succeed; a metavariable no side
  * mentions has no register.
  */
final case class Seed(
    orientation: Int,
    steps: Vector[Step],
    root: Register,
    bindings: Vector[Option[Register]]
)

/** A building: the nodes to add for a side or a code body, a tree whose
  * leaves are values the caller gives (an instance's bindings, a β step's
  * slot values) and instructions, and whose layers are added children first.
  */
enum Building:
  /** The value the caller gives at the index. */
  case Value(index: Int)

  /** The node of the instruction, added when the graph lacks it. */
  case InstructionNode(instruction: Instruction)

  /** The building of the code, with the same values: a body's subcode. */
  case CodeBody(code: Code)

  /** An application; `read` when the β rule reads it. */
  case Apply(function: Building, argument: Building, read: Boolean)

  case Parallel(left: Building, right: Building)

  case Choice(left: Building, right: Building)

  case Thunk(code: Code, holes: Vector[Hole], fillings: Vector[Building])

/** What saturation needs of an orientation to apply an instance: the lemma
  * that justifies its union, which side goes first in the union, its added
  * side, and what tells two of its instances apart.
  */
final case class OrientationPlan(
    lemma: LemmaIdentifier,
    direction: Direction,
    added: Building,
    essential: Vector[Int],
    shared: Vector[Building]
)

/** A whole program: the seeds filed under each kind and key, each list in
  * the order its seeds' matches are handed over; the plan of every
  * orientation, by number; and the building of every code's body. It is
  * first-order data: no field holds a function.
  */
final case class Program(
    seeds: Map[(SeedKind, SeedKey), Vector[Seed]],
    orientations: Vector[OrientationPlan],
    codes: Map[Code, Building]
):
  /** The seeds under each kind and key as the tree every backend runs, so
    * that the steps the seeds begin with in common are run once.
    */
  lazy val trees: Map[(SeedKind, SeedKey), SeedTree] =
    seeds.map((kindAndKey, filed) => kindAndKey -> SeedTree.of(filed))
