package gezi.standardlibrary

/** A slot of a knowledge term, the mixin of the fixed-width encoding a
  * knowledge file writes, keyed by no string, so that several files contribute
  * to one knowledge term. The term is a mixin of three groups, each a mixin of
  * its own slots, a group holding about seven slots, a design guideline and not
  * a hard limit:
  *
  * {{{
  * rewriting   lemmas, leaves
  * properties  associative, first_order_constructor, typed_branch,
  *             name_marker, closure_marker, tag_origin, tag_next, repeller
  * backend     natives, representations, families, fields, jvm_types
  * }}}
  *
  * A contribution to the slot of position p in the group of position g is
  * `λself. λg0 g1 g2. gg λself. λc0 … cW. cp body`, W the group's width; a file
  * that reads no self writes `_` for it, and one wrapper may give several
  * slots, the λ distributing over the choice (`λ_ lemmas leaves. lemmas L +
  * leaves V`).
  *
  * @param group
  *   the position of the slot's group among the three
  * @param position
  *   the slot's position in its group
  */
enum KnowledgeSlot(val group: Int, val position: Int):
  case Lemmas extends KnowledgeSlot(0, 0)
  case Leaves extends KnowledgeSlot(0, 1)
  case Associative extends KnowledgeSlot(1, 0)
  case FirstOrderConstructor extends KnowledgeSlot(1, 1)
  case TypedBranch extends KnowledgeSlot(1, 2)
  case NameMarker extends KnowledgeSlot(1, 3)
  case ClosureMarker extends KnowledgeSlot(1, 4)
  case TagOrigin extends KnowledgeSlot(1, 5)
  case TagNext extends KnowledgeSlot(1, 6)
  case Repeller extends KnowledgeSlot(1, 7)
  case Natives extends KnowledgeSlot(2, 0)
  case Representations extends KnowledgeSlot(2, 1)
  case Families extends KnowledgeSlot(2, 2)
  case Fields extends KnowledgeSlot(2, 3)
  case JvmTypes extends KnowledgeSlot(2, 4)

object KnowledgeSlot:

  /** The width of the knowledge term's top level, its number of groups. */
  val width: Int = 3

  /** The width of each group, in the groups' order. */
  val groupWidths: Vector[Int] = Vector.tabulate(width)(group =>
    KnowledgeSlot.values.count(_.group == group)
  )

  require(
    KnowledgeSlot.values.forall(slot =>
      slot.position < groupWidths(slot.group)
    ) &&
      KnowledgeSlot.values
        .groupBy(slot => (slot.group, slot.position))
        .forall(_._2.size == 1),
    "the knowledge slots' positions are not each group's 0 to its width"
  )
