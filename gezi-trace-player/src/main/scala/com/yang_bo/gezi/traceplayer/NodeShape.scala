package com.yang_bo.gezi.traceplayer

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.ir
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** One node of an IR term as the player draws it: the layer's constructor and
  * its atoms (a thunk's code and holes), without the terms under it, which are
  * drawn as nodes of their own at the positions `roles` names. Two terms with
  * equal shapes are drawn by one element whose nodes under it are updated in
  * place (`TermView`).
  */
enum NodeShape:
  case Apply
  case Parallel
  case Choice

  /** A thunk: its code, the hole of each binder in lambda order, and the number
    * of its fillings, the values of the code's other slots in slot order.
    */
  case Thunk(code: Code, holes: Vector[Hole], fillings: Int)

  /** An opaque instruction, drawn by what it says of itself: a trace's terms
    * are closed and hold none, but the eigenvariable of an opened body is one
    * (`com.yang_bo.gezi.rewritetrace.Conversions.eigenvariables`).
    */
  case Opaque(description: String)

  /** The role of each term under the node, in the order of `Layer.children`:
    * the names that the trace format's positions use.
    */
  def roles: Vector[String] = this match
    case Apply              => Vector("function", "argument")
    case Parallel | Choice  => Vector("left", "right")
    case Thunk(_, _, count) =>
      Vector.tabulate(count)(index => s"filling $index")
    case Opaque(_) => Vector.empty

object NodeShape:

  /** The shape of the term's root: `Opaque` for an opaque instruction (a URI
    * node or an opaque term), the layer's shape for any other.
    */
  def of[C <: NativeSpecializer & Singleton](instruction: Configured[C])(using
      C
  ): NodeShape =
    // A storage is shown as the leaf it is in its term's layer, its view not read.
    if instruction.opaque || ir.NativeStorage.stored(instruction.representation)
    then Opaque(instruction.toString)
    else
      val shape = instruction.layer match
        case ir.Apply(_, _)                  => Apply
        case ir.Parallel(_, _)               => Parallel
        case ir.Choice(_, _)                 => Choice
        case ir.Thunk(code, holes, fillings) =>
          Thunk(code, holes, fillings.size)
        case leaf @ (ir.UriNode(_) | ir.Opaque(_) | _: ir.NativeStorage) =>
          throw IllegalStateException(
            s"an opaque instruction is answered before its layer is read: $leaf"
          )
      assert(
        shape.roles.size == instruction.layer.children.size,
        s"the shape $shape names ${shape.roles.size} roles for ${instruction.layer.children.size} terms under it"
      )
      shape

  /** The term at the index of `Layer.children` under the term's root. Throws
    * `IllegalArgumentException` when the root has no term there: the caller
    * asks only for the positions of the root's shape.
    */
  def under[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      index: Int
  )(using C): Configured[C] =
    val children =
      if instruction.opaque then Vector.empty else instruction.layer.children
    require(
      children.indices.contains(index),
      s"the $instruction has ${children.size} terms under it, none at $index"
    )
    children(index)
