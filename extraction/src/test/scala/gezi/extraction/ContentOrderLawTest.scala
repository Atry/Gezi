package gezi.extraction

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}

/** The laws of `ContentOrder.compare` on generated entries: it is a total
  * order on spelled terms, antisymmetric, transitive and total, and it is
  * zero exactly when the two entries spell one term, whatever node numbers
  * and child classes their shapes carry. The entries are drawn from small
  * pools of instructions, codes and holes, so that equal and nearly equal
  * spellings are common. Its purpose is to catch a comparison that is not
  * an order (a pending pair compared in the wrong order, a fallback on equal
  * hash codes that disagrees with structure), which would make the class an
  * extraction keeps among equal costs depend on the order it met them in.
  */
class ContentOrderLawTest extends GeneratedProperties:

  private val leaves = Vector(Instruction.opaque("first"), Instruction.opaque("second"))

  private val instructions: Vector[Instruction] =
    leaves ++ Vector(Instruction(Apply(leaves(0), leaves(1))), Instruction(Parallel(leaves(1), leaves(0))))

  private val codes: Vector[Code] =
    Vector(Code(Slot(0)), Code(Slot(1)),
      Code(Apply(Code(Slot(0)), Code(Slot(1)))))

  private val holeLists: Vector[Vector[Hole]] =
    Vector(Vector(Hole.Bound(0)), Vector(Hole.Ignored), Vector(Hole.Bound(0), Hole.Bound(1)))

  private val nodeNumber: Gen[Int] = Gen.int(Range.linear(0, 5))

  private def entry(depth: Int): Gen[Entry[Unit]] =
    val leaf: Gen[Entry[Unit]] = Gen.choice1(
      Gen.element1(instructions.head, instructions.tail*).map(instruction => Entry((), Shape.Name(instruction), Vector.empty)),
      for number <- nodeNumber; instruction <- Gen.element1(instructions.head, instructions.tail*)
      yield Entry((), Shape.Node(number, NoinlineLeaf(instruction)), Vector.empty)
    )
    if depth == 0 then leaf
    else
      def node(layer: Int => Layer[Int], children: Int): Gen[Entry[Unit]] =
        for
          number <- nodeNumber
          childEntries <- entry(depth - 1).list(Range.singleton(children))
        yield Entry((), Shape.Node(number, layer(number)), childEntries.toVector)
      Gen.choice1(
        leaf,
        node(root => Apply(root, root + 1), 2),
        node(root => Parallel(root, root), 2),
        node(root => Choice(root, root), 2),
        for
          code <- Gen.element1(codes.head, codes.tail*)
          holes <- Gen.element1(holeLists.head, holeLists.tail*)
          width <- Gen.int(Range.linear(0, 2))
          thunk <- node(root => Thunk(code, holes, Vector.fill(width)(root)), width)
        yield thunk
      )

  /** The term an entry spells: its shapes without node numbers and child
    * classes, over its child entries' terms.
    */
  private def spelling(entry: Entry[Unit]): Any =
    val shape = entry.shape match
      case Shape.Name(instruction)    => ("name", instruction)
      case Shape.Node(_, layer)  => ("node", layer.map(_ => 0))
      case pattern               => throw IllegalStateException(s"the generator makes names and nodes only, not $pattern")
    (shape, entry.childEntries.map(spelling))

  private val entries: Gen[Entry[Unit]] = Gen.int(Range.linear(0, 3)).flatMap(entry)

  property("the order of content is a total order that is zero exactly on one spelled term") {
    for
      first <- entries.forAll
      second <- entries.forAll
      third <- entries.forAll
    yield
      val firstSecond = ContentOrder.compare(first, second)
      val secondThird = ContentOrder.compare(second, third)
      val firstThird = ContentOrder.compare(first, third)
      Result.all(List(
        Result.diff(firstSecond == 0, spelling(first) == spelling(second))(_ == _).log("zero exactly on one term"),
        Result.diff(firstSecond.sign, -ContentOrder.compare(second, first).sign)(_ == _).log("antisymmetric"),
        Result.assert(!(firstSecond <= 0 && secondThird <= 0) || firstThird <= 0).log("transitive"),
        Result.assert(ContentOrder.compare(first, first) == 0).log("reflexive")
      ))
  }
