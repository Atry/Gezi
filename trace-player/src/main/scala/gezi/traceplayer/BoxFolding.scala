package gezi.traceplayer

import gezi.frontend.ReadableText
import gezi.locations.SourceMap
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** The configuration of the terms here: no facts. */
private given boxFoldingNoFacts: NoFacts.type = NoFacts

/** How the boxes view draws a step's term folded as the printer shares it: each
  * shared instruction the printed text binds
  * (`ReadableText.Printed[NoFacts.type].sharedValues`) drawn once, under its
  * name, and referred to by its name where it occurs, a library term the trace
  * names (`Played.names`) among them, bound under that name as the text binds
  * it; and every other instruction drawn as the box of its layer, an inlined
  * shared one with the key it is inlined by (`SharedKey`), whose box offers to
  * bind it again.
  *
  * A box stands at a place (`ReadableText.Place`): in the binding of a shared
  * instruction, its name and the path from that instruction, else in the body,
  * the path from the root. The view keys its boxes by their places, finds the
  * box of a path by `place`, and asks `body`, `binding` and `under` what to
  * draw, so that what it draws is the tree of `drawn`, whose laws
  * `BoxFoldingLawTest` checks.
  */
final case class BoxFolding(
    root: Configured[NoFacts.type],
    map: SourceMap,
    bindings: Vector[ReadableText.SharedValue[NoFacts.type]],
    inlined: Map[Configured[NoFacts.type], String]
):

  private val referenced: Map[Configured[NoFacts.type], String] =
    bindings.map(value => value.instruction -> value.name).toMap

  private val bound: Map[String, ReadableText.SharedValue[NoFacts.type]] =
    bindings.map(value => value.name -> value).toMap

  /** What is drawn where the instruction occurs, with the map of that
    * occurrence: a reference to its binding, or its layer's box.
    */
  private def occurrence(
      instruction: Configured[NoFacts.type],
      occurrenceMap: SourceMap
  ): BoxFolding.Shown =
    referenced.get(instruction) match
      case Some(name) => BoxFolding.Shown.Reference(name, SharedKey.of(name))
      case None       =>
        BoxFolding.Shown.Layer(
          instruction,
          occurrenceMap,
          inlined.get(instruction)
        )

  /** What the body draws at its root. */
  def body: BoxFolding.Shown = occurrence(root, map)

  /** What the binding of the name draws at its root: the shared instruction's
    * layer, with the map of its occurrences merged. Throws
    * `IllegalArgumentException` for a name the printed text does not bind.
    */
  def binding(name: String): BoxFolding.Shown =
    val value = bound.getOrElse(
      name,
      throw IllegalArgumentException(
        s"the printed text binds no shared instruction named $name"
      )
    )
    BoxFolding.Shown.Layer(value.instruction, value.map, None)

  /** What is drawn at the index of `Layer.children` under a layer's box. Throws
    * `IllegalArgumentException` for anything else, which has no box under it,
    * and for an index the layer has no term at.
    */
  def under(shown: BoxFolding.Shown, index: Int): BoxFolding.Shown = shown match
    case BoxFolding.Shown.Layer(instruction, layerMap, _) =>
      occurrence(
        NodeShape.under(instruction, index),
        layerMap.children.lift(index).getOrElse(SourceMap.unlocated)
      )
    case other => throw IllegalArgumentException(s"$other has no box under it")

  /** The place of the box that draws the subterm of the root at the path, by
    * the indices of `Layer.children`: in the binding of the last shared
    * instruction on the way down, else in the body. Throws
    * `IllegalArgumentException` for a path that leads below an opaque
    * instruction or past a layer's terms.
    */
  def place(path: Vector[Int]): ReadableText.Place =
    path
      .foldLeft((root, ReadableText.Place(None, Vector.empty))) {
        case ((current, found), index) =>
          val child = NodeShape.under(current, index)
          referenced.get(child) match
            case Some(name) =>
              (child, ReadableText.Place(Some(name), Vector.empty))
            case None => (child, found.copy(path = found.path :+ index))
      }
      ._2

  /** The boxes the view draws, as a tree: each binding's, in the order the text
    * binds them, with its name, and the body's.
    */
  def drawn: (Vector[(String, BoxFolding.Box)], BoxFolding.Box) =
    def tree(
        place: ReadableText.Place,
        shown: BoxFolding.Shown
    ): BoxFolding.Box = shown match
      case BoxFolding.Shown.Layer(instruction, _, _) =>
        val count =
          if instruction.opaque then 0 else instruction.layer.children.size
        BoxFolding.Box(
          place,
          shown,
          Vector.tabulate(count)(index =>
            tree(place.copy(path = place.path :+ index), under(shown, index))
          )
        )
      case _ => BoxFolding.Box(place, shown, Vector.empty)
    (
      bindings.map(value =>
        value.name -> tree(
          ReadableText.Place(Some(value.name), Vector.empty),
          binding(value.name)
        )
      ),
      tree(ReadableText.Place(None, Vector.empty), body)
    )

  /** The key of the inlined shared instruction at each place the tree draws
    * one, for the text view's buttons that bind it again; empty when nothing is
    * inlined.
    */
  def extractions: Map[String, String] =
    if inlined.isEmpty then Map.empty
    else
      def found(box: BoxFolding.Box): Vector[(String, String)] =
        val here = box.shown match
          case BoxFolding.Shown.Layer(_, _, Some(key)) =>
            Vector(box.place.key -> key)
          case _ => Vector.empty
        here ++ box.under.flatMap(found)
      val (boundBoxes, bodyBox) = drawn
      (boundBoxes.map(_._2) :+ bodyBox).flatMap(found).toMap

object BoxFolding:

  /** What a box draws of its own place. */
  enum Shown:

    /** The box of the instruction's layer, with the map of its occurrence, and
      * the key of the shared instruction it is when that is inlined.
      */
    case Layer(
        instruction: Configured[NoFacts.type],
        map: SourceMap,
        extracted: Option[String]
    )

    /** A reference to the binding of the name, with the key that inlines it,
      * none for a name the printer did not synthesize.
      */
    case Reference(name: String, key: Option[String])

  /** A box at its place, what it draws, and the boxes under it. */
  final case class Box(
      place: ReadableText.Place,
      shown: Shown,
      under: Vector[Box]
  )

  /** The printed text of the step's term and its boxes' folding, the shared
    * instructions whose keys `keys` holds inlined: the term printed once with
    * none inlined, the keys looked up among the names of its shared
    * instructions (a key no step's term shares does nothing), and printed again
    * with those inlined. The library terms `known` names are bound at the
    * text's start under their names in both views
    * (`ReadableText.KnownNames.Bound`), so that the text is a closed term that
    * reads back as the step's term, and no inlining unbinds them: a step that
    * wrote them by name and bound them nowhere is no term.
    */
  def step(
      term: Configured[NoFacts.type],
      map: SourceMap,
      known: Map[Configured[NoFacts.type], String],
      keys: Set[String]
  ): (ReadableText.Printed[NoFacts.type], BoxFolding) =
    val names = ReadableText.KnownNames.Bound(known)
    val plain = ReadableText.printed(term, map, names)
    val inlined = plain.sharedValues
      .flatMap(value =>
        SharedKey
          .of(value.name)
          .filter(keys.contains)
          .map(key => value.instruction -> key)
      )
      .toMap
    val printed = if inlined.isEmpty then plain
    else ReadableText.printed(term, map, names, inlined.keySet)
    (printed, BoxFolding(term, map, printed.sharedValues, inlined))
