package gezi.jit

import gezi.ir.ConstructorIdentity
import gezi.ir.Instruction
import gezi.weakhead.ListCase
import gezi.weakhead.ListRepresentation
import gezi.weakhead.ListTail
import gezi.weakhead.Value
import gezi.weakhead.Values
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A node of a value as a key: equal to itself only and hashed by its
  * identity, so that a subvalue the heap shares is one key, found in time
  * independent of its size.
  */
final class Identity(val node: AnyRef):

  override def equals(other: Any): Boolean = other match
    case that: Identity => that.node eq node
    case _              => false

  override def hashCode: Int = System.identityHashCode(node)

/** The values a walk found to hold no case of a decoding
  * (`JitValues.caseWalk`), by identity: the memo of a pure function of the
  * value, whose emptying changes only how many nodes a later walk visits
  * (`CONTRIBUTING.md`, "Tables"). It is kept in two generations, as the
  * instance table is (`InstanceRetention`), so that a long run holds a
  * bounded number of values. A value found in the older generation is
  * brought into the young one with nothing under it visited, so that the
  * root of a structure met in every generation stands for the whole of it.
  */
final case class CaseFreeValues(young: Set[Identity], older: Set[Identity])

object CaseFreeValues:

  /** No value known. */
  val empty: CaseFreeValues = CaseFreeValues(Set.empty, Set.empty)

/** What a walk for a case of a decoding found: the values known afterwards
  * when the walked value holds no case, none when it holds one; and the nodes
  * the walk visited, a cost.
  */
final case class CaseWalk(caseFree: Option[CaseFreeValues], visits: Long)

/** The conversions between the reference's values and the JIT's, each
  * trampolined, so that a deep value costs heap and not JVM stack.
  *
  * SHARING. Each conversion that rebuilds a value threads an immutable map
  * from the nodes already converted, keyed by identity (`Identity`), to
  * their images, so that a subvalue met along several paths is converted
  * once and its image is shared by the paths as the subvalue was: the result
  * has as many distinct nodes as the input, not as many as the input
  * written out as a tree. A value that is a small graph of a large tree
  * (the program of `ReductionMeaningsRepeated` at seed 568201625 and two
  * repetitions: 156 distinct nodes, 1.93e10 as a tree) is then converted in
  * time and space linear in its distinct nodes.
  */
object JitValues:

  /** The images of the nodes converted so far, by identity. */
  private type Images[Image] = Map[Identity, Image]

  /** The step's image of the node, read from the images when the node was
    * met before, and otherwise made by the step and recorded.
    */
  private def shared[Node <: AnyRef, Image](node: Node, images: Images[Image])(
      step: (Node, Images[Image]) => TailRec[(Image, Images[Image])]
  ): TailRec[(Image, Images[Image])] =
    images.get(Identity(node)) match
      case Some(found) => done((found, images))
      case None =>
        tailcall(step(node, images)).map((image, after) => (image, after.updated(Identity(node), image)))

  /** The step's images of the nodes in order, the images threaded from one
    * node to the next.
    */
  private def allImages[Node, Image](nodes: Vector[Node], images: Images[Image])(
      step: (Node, Images[Image]) => TailRec[(Image, Images[Image])]
  ): TailRec[(Vector[Image], Images[Image])] =
    def from(index: Int, found: Vector[Image], current: Images[Image]): TailRec[(Vector[Image], Images[Image])] =
      if index >= nodes.size then done((found, current))
      else tailcall(step(nodes(index), current)).flatMap((image, next) => from(index + 1, found :+ image, next))
    from(0, Vector.empty, images)

  /** The step's images of two nodes, the images threaded from the first to
    * the second.
    */
  private def bothImages[Node, Image](first: Node, second: Node, images: Images[Image])(
      step: (Node, Images[Image]) => TailRec[(Image, Images[Image])]
  ): TailRec[((Image, Image), Images[Image])] =
    tailcall(step(first, images)).flatMap((firstImage, afterFirst) =>
      tailcall(step(second, afterFirst)).map((secondImage, afterSecond) => ((firstImage, secondImage), afterSecond))
    )

  /** The run-time value of a field of the representation: the term itself
    * for a field of the family `unread`, the value of the representation
    * otherwise.
    */
  def fieldTerm(representation: Representation, value: NativeValue): JitValue = value match
    case NativeValue.Unread(term) => term
    case other                    => JitValue.Represented(representation, other)

  /** Whether the value holds a case of a decoding (`DataCase`, `ListCase`):
    * a field kept unread that holds one refers to the binder the decoding
    * opened, so that the case would leave the decoding. The walk visits each
    * shared part once and stops at a value `known` holds, so that a run whose
    * state grows by a part at each step visits that part and not the whole
    * state. The values it visited become known only when it found no case.
    */
  def caseWalk(value: JitValue, known: CaseFreeValues, retention: InstanceRetention): CaseWalk =
    val (seen, visits) = walkedForCase(List(value), known.young, known.older, 0L)
    CaseWalk(
      seen.map(young =>
        retention match
          case InstanceRetention.Generations(size) if young.size >= size => CaseFreeValues(Set.empty, young)
          case InstanceRetention.Generations(_) | InstanceRetention.NeverDropped => CaseFreeValues(young, known.older)
      ),
      visits
    )

  @tailrec
  private def walkedForCase(
      pending: List[JitValue],
      seen: Set[Identity],
      older: Set[Identity],
      visits: Long
  ): (Option[Set[Identity]], Long) = pending match
    case Nil => (Some(seen), visits)
    case value :: rest =>
      val key = Identity(value)
      if seen.contains(key) then walkedForCase(rest, seen, older, visits)
      else if older.contains(key) then walkedForCase(rest, seen + key, older, visits)
      else
        val visited = seen + key
        val counted = visits + 1
        value match
          case JitValue.Neutral(_: DataCase | _: ListCase, _) => (None, counted)
          case JitValue.Neutral(JitCarried(carried), arguments) =>
            walkedForCase(carried :: arguments.toList ++ rest, visited, older, counted)
          case JitValue.Neutral(_, arguments)     => walkedForCase(arguments.toList ++ rest, visited, older, counted)
          case JitValue.Apply(function, argument) => walkedForCase(function :: argument :: rest, visited, older, counted)
          case JitValue.Parallel(left, right)     => walkedForCase(left :: right :: rest, visited, older, counted)
          case JitValue.Choice(members)           => walkedForCase(members.toList ++ rest, visited, older, counted)
          case JitValue.Thunk(_, _, fillings)     => walkedForCase(fillings.toList ++ rest, visited, older, counted)
          case JitValue.Cell(inner)               => walkedForCase(inner :: rest, visited, older, counted)
          case JitValue.Evaluated(written, _, _)  => walkedForCase(written :: rest, visited, older, counted)
          case JitValue.Represented(_, native)    => walkedForCase(nativeParts(native) ++ rest, visited, older, counted)
          case _                                  => walkedForCase(rest, visited, older, counted)

  /** The run-time values a native value holds. */
  private def nativeParts(value: NativeValue): List[JitValue] = value match
    case NativeValue.Unread(term)             => List(term)
    case NativeValue.Constructed(_, _, fields) => fields.toList.flatMap(nativeParts)
    case NativeValue.Listed(list)             => listParts(list)
    case _                                    => Nil

  private def listParts(list: ListRepresentation[JitValue]): List[JitValue] = list match
    case ListRepresentation.Items(_, items)                 => items.toList
    case ListRepresentation.Cell(item, ListTail.Unread(term)) => List(item, term)
    case ListRepresentation.Cell(item, ListTail.Listed(rest)) => item :: listParts(rest)

  /** The JIT's value of a value a reader gives: a carried leaf is the value
    * it carries; an instruction (`ConstructorIdentity.isInstruction`, one
    * field read: no neutral value under it) is a reference to itself, as an
    * instruction was; every other value is taken over part by part, each shared
    * part once.
    */
  def fromValue(value: Value): JitValue = converted(value, Map.empty).result._1

  private def converted(value: Value, images: Images[JitValue]): TailRec[(JitValue, Images[JitValue])] = value match
    case Value.Neutral(JitCarried(carried), arguments) if arguments.isEmpty => done((carried, images))
    case instruction if ConstructorIdentity.isInstruction(instruction) =>
      // Sound: one pool interns both, and a value made of the IR's
      // constructors only is an instruction, which is a value of the JIT as it is.
      done((instruction.asInstanceOf[Instruction], images))
    case _ => shared(value, images)(convertedNode)

  private def convertedNode(value: Value, images: Images[JitValue]): TailRec[(JitValue, Images[JitValue])] = value match
    case Value.Apply(function, argument) =>
      bothImages(function, argument, images)(converted).map { case ((jitFunction, jitArgument), after) =>
        (JitValue.Apply(jitFunction, jitArgument), after)
      }
    case Value.Parallel(left, right) =>
      bothImages(left, right, images)(converted).map { case ((jitLeft, jitRight), after) =>
        (JitValue.Parallel(jitLeft, jitRight), after)
      }
    case Value.Choice(left, right) =>
      bothImages(left, right, images)(converted).map { case ((jitLeft, jitRight), after) =>
        (JitValue.Choice(Vector(jitLeft, jitRight)), after)
      }
    case Value.Thunk(code, holes, fillings) =>
      allImages(fillings, images)(converted).map((found, after) => (JitValue.Thunk(code, holes, found), after))
    case Value.Neutral(variable, arguments) =>
      allImages(arguments, images)(converted).map((found, after) => (JitValue.Neutral(variable, found), after))
    case other => throw IllegalStateException(s"a ${other.layer.productPrefix} value is no layer of a value")

  /** The value as a reader holds it, in one step whatever its size: an
    * instruction is a value as it is, any other value is carried
    * (`JitCarried`).
    */
  def carried(value: JitValue): Value = value match
    case JitValue.Instruction(instruction) => instruction
    case other                        => Value.Neutral(JitCarried(other), Vector.empty)

  /** The plain value of a JIT value that holds no value of the JIT's own,
    * each shared part converted once. Throws `IllegalArgumentException` on a
    * represented or `Evaluated` value.
    */
  def plain(value: JitValue): Value = plainOf(value, Map.empty).result._1

  private def plainOf(value: JitValue, images: Images[Value]): TailRec[(Value, Images[Value])] = value match
    case JitValue.Instruction(instruction) => done((instruction, images))
    case JitValue.Cell(inner)         => tailcall(plainOf(inner, images))
    case _                            => shared(value, images)(plainNode)

  /** The plain value of the choice of no member ([[EmptyChoice]]): top
    * (`gezi.frontend.Literals.top`), the term of no answer.
    */
  private lazy val noAnswer: Value =
    gezi.frontend.Defunctionalization.thunkInstruction(gezi.frontend.Literals.top)

  private def plainNode(value: JitValue, images: Images[Value]): TailRec[(Value, Images[Value])] = value match
    case JitValue.Apply(function, argument) =>
      bothImages(function, argument, images)(plainOf).map { case ((plainFunction, plainArgument), after) =>
        (Value.Apply(plainFunction, plainArgument), after)
      }
    case JitValue.Parallel(left, right) =>
      bothImages(left, right, images)(plainOf).map { case ((plainLeft, plainRight), after) =>
        (Value.Parallel(plainLeft, plainRight), after)
      }
    case JitValue.Choice(members) =>
      allImages(members, images)(plainOf).map((found, after) =>
        (if found.isEmpty then noAnswer else gezi.ir.ChoiceSpine.nested[Value](found, Value.Choice(_, _)), after)
      )
    case JitValue.Thunk(code, holes, fillings) =>
      allImages(fillings, images)(plainOf).map((found, after) => (Value.Thunk(code, holes, found), after))
    case JitValue.Neutral(variable, arguments) =>
      allImages(arguments, images)(plainOf).map((found, after) => (Value.Neutral(variable, found), after))
    case other => throw IllegalArgumentException(s"a ${other.layer.productPrefix} value is no plain value")

  /** The value with every represented value replaced by the term it stands
    * for, whole (represented_term/3: successor^n zero over the codec's
    * instructions, a boolean's define, a list's cells), and every `Evaluated`
    * value by its written operand, encoded likewise (value_encoded/2); each
    * shared subvalue encoded once, so that the result shares as the value
    * does (SHARING).
    */
  def encoded(value: JitValue, facts: BackendFacts): JitValue = encodedOf(value, facts, Map.empty).result._1

  private def encodedOf(value: JitValue, facts: BackendFacts, images: Images[JitValue]): TailRec[(JitValue, Images[JitValue])] =
    value match
      case JitValue.Instruction(_) => done((value, images))
      case _                       => shared(value, images)(encodedNode(_, facts, _))

  private def encodedNode(value: JitValue, facts: BackendFacts, images: Images[JitValue]): TailRec[(JitValue, Images[JitValue])] =
    def encodedPart(part: JitValue, current: Images[JitValue]) = encodedOf(part, facts, current)
    value match
      case JitValue.Represented(representation, native) => representedTerm(representation, native, facts, images)
      case JitValue.Evaluated(written, _, _) => tailcall(encodedOf(written, facts, images))
      case JitValue.Cell(inner) =>
        tailcall(encodedOf(inner, facts, images)).map((found, after) => (JitValue.Cell(found), after))
      case JitValue.Apply(function, argument) =>
        bothImages(function, argument, images)(encodedPart).map { case ((encodedFunction, encodedArgument), after) =>
          (JitValue.Apply(encodedFunction, encodedArgument), after)
        }
      case JitValue.Parallel(left, right) =>
        bothImages(left, right, images)(encodedPart).map { case ((encodedLeft, encodedRight), after) =>
          (JitValue.Parallel(encodedLeft, encodedRight), after)
        }
      case JitValue.Choice(members) =>
        allImages(members, images)(encodedPart).map((found, after) => (JitValue.Choice(found), after))
      case JitValue.Thunk(code, holes, fillings) =>
        allImages(fillings, images)(encodedPart).map((found, after) => (JitValue.Thunk(code, holes, found), after))
      case JitValue.Neutral(variable, arguments) =>
        allImages(arguments, images)(encodedPart).map((found, after) => (JitValue.Neutral(variable, found), after))
      case JitValue.Instruction(_) => done((value, images))

  private def representedTerm(
      representation: Representation,
      value: NativeValue,
      facts: BackendFacts,
      images: Images[JitValue]
  ): TailRec[(JitValue, Images[JitValue])] =
    def encodedPart(part: JitValue, current: Images[JitValue]) = encodedOf(part, facts, current)
    (representation, value) match
      case (Representation.Data(familyIdentity, parameter), _) =>
        val family = facts.nativeBackend.family(familyIdentity).getOrElse(
          throw IllegalStateException(s"no data family ${familyIdentity.shown} in the backend")
        )
        val DataLayer(constructor, fields) = family.layer(parameter, value)
        val atParameter = family.constructors(parameter)(constructor)
        val represented = atParameter.fields.zip(fields).map((field, fieldValue) =>
          fieldTerm(field.representation(parameter), fieldValue)
        )
        allImages(represented, images)(encodedPart).map((encodedFields, after) =>
          (
            encodedFields.foldLeft(facts.constructorDefine(atParameter.native): JitValue)(
              JitValue.Apply(_, _)
            ),
            after
          )
        )
      case (Representation.ListOf(element), NativeValue.Listed(ListRepresentation.Items(_, items))) =>
        allImages(items, images)(encodedPart).map((encodedItems, after) =>
          (
            encodedItems.foldRight(facts.nil: JitValue)((item, rest) =>
              JitValue.Apply(JitValue.Apply(facts.cons, JitValue.Parallel(item, element)), rest)
            ),
            after
          )
        )
      case (Representation.ListOf(element), NativeValue.Listed(ListRepresentation.Cell(item, tail))) =>
        val tailTerm = tail match
          case ListTail.Unread(term) => term
          case ListTail.Listed(list) => JitValue.Represented(representation, NativeValue.Listed(list))
        bothImages(item, tailTerm, images)(encodedPart).map { case ((encodedItem, encodedTail), after) =>
          (JitValue.Apply(JitValue.Apply(facts.cons, JitValue.Parallel(encodedItem, element)), encodedTail), after)
        }
      case _ => throw IllegalStateException(s"a value of another representation than ${representation.familyIdentity.shown}")

  /** The value with every `Evaluated` value in it replaced by its written
    * operand (written_throughout/2), each shared subvalue rebuilt once
    * (SHARING); represented values stay.
    */
  def writtenThroughout(value: JitValue): JitValue = writtenOf(value, Map.empty).result._1

  private def writtenOf(value: JitValue, images: Images[JitValue]): TailRec[(JitValue, Images[JitValue])] = value match
    case JitValue.Evaluated(written, _, _) => done((written, images))
    case JitValue.Instruction(_)           => done((value, images))
    case JitValue.Apply(_, _) | JitValue.Parallel(_, _) | JitValue.Choice(_) | JitValue.Thunk(_, _, _) | JitValue.Neutral(_, _) |
        JitValue.Cell(_) =>
      shared(value, images)(writtenNode)
    case other => done((other, images))

  private def writtenNode(value: JitValue, images: Images[JitValue]): TailRec[(JitValue, Images[JitValue])] = value match
    case JitValue.Apply(function, argument) =>
      bothImages(function, argument, images)(writtenOf).map { case ((writtenFunction, writtenArgument), after) =>
        (JitValue.Apply(writtenFunction, writtenArgument), after)
      }
    case JitValue.Parallel(left, right) =>
      bothImages(left, right, images)(writtenOf).map { case ((writtenLeft, writtenRight), after) =>
        (JitValue.Parallel(writtenLeft, writtenRight), after)
      }
    case JitValue.Choice(members) =>
      allImages(members, images)(writtenOf).map((found, after) => (JitValue.Choice(found), after))
    case JitValue.Thunk(code, holes, fillings) =>
      allImages(fillings, images)(writtenOf).map((found, after) => (JitValue.Thunk(code, holes, found), after))
    case JitValue.Neutral(variable, arguments) =>
      allImages(arguments, images)(writtenOf).map((found, after) => (JitValue.Neutral(variable, found), after))
    case JitValue.Cell(inner) => tailcall(writtenOf(inner, images)).map((found, after) => (JitValue.Cell(found), after))
    case other => done((other, images))
