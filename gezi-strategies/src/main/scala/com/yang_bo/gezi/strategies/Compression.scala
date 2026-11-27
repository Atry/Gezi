package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.ir.NativeSpecializer

/** The fold state of `compression`: the size, which is the value and the rank.
  */
final case class CompressionState(size: BigInt) extends FoldState

/** Row 6 of the HM baseline, the module `compression`, the port of
  * `gezi/prolog/gezi/baseline/compression.pl`: the number of nodes of the IR
  * instruction tree, an instruction one node, a metavariable one node, a thunk
  * one node more than its resolved body. So a name beats the shape it stands
  * for.
  */
object Compression extends ConfigurationFreeModule:

  val name: String = "compression"

  val meetsExtractionContract: Boolean = true

  def folded[C <: NativeSpecializer & Singleton](
      layer: OrderTerm[C],
      reading: TermReading[C]
  ): FoldState = CompressionState(size(layer))

  private def size[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C]
  ): BigInt = term match
    case OrderTerm.Folded(state, _) =>
      TermOrder.ownState[CompressionState](state).size
    case OrderTerm.Name(_)                   => 1
    case leaf if TermReading.leafTerm(leaf)  => 1
    case OrderTerm.Apply(function, argument) =>
      1 + size(function) + size(argument)
    case OrderTerm.Choice(members)              => 1 + members.map(size).sum
    case OrderTerm.Parallel(left, right, _)     => 1 + size(left) + size(right)
    case OrderTerm.Thunk(code, holes, fillings) =>
      1 + size(TermReading.resolved(code, holes, fillings))
    case other => TermOrder.refused(other)

  def rank(state: FoldState): OrderValue = OrderValue.Number(sizeOf(state))

  def value(state: FoldState): OrderValue = rank(state)

  /** The size of a code, part by part: a slot the size of what it holds, a hole
    * one node, an application or a parallel one node more than its parts, a
    * thunk one node more than its code, as `size` reads a thunk's body with its
    * fillings in their slots (`TermReading.resolved`); a filling the code does
    * not read counts nothing.
    */
  override def codeFolding[C <: NativeSpecializer & Singleton]
      : Option[CodeFolding[C]] = Some(
    new CodeFolding[C]:
      def folded(layer: CodeFold[C], reading: TermReading[C]): FoldState =
        layer match
          case CodeFold.Filling(term, _)   => CompressionState(size(term))
          case CodeFold.InnerFilling(part) => part
          case CodeFold.HoleSlot(_, _, _)  => CompressionState(1)
          case CodeFold.Apply(function, argument) =>
            CompressionState(1 + sizeOf(function) + sizeOf(argument))
          case CodeFold.Parallel(left, criterion) =>
            CompressionState(1 + sizeOf(left) + sizeOf(criterion))
          case CodeFold.RangeParallel(left, range) =>
            CompressionState(1 + sizeOf(left) + sizeOf(range))
          case CodeFold.Choice(_, Some(dispatched)) => dispatched
          case CodeFold.Choice(members, None)       =>
            CompressionState(1 + members.map(sizeOf).sum)
          case CodeFold.InnerThunk(_, _, _, _, body, _) =>
            CompressionState(1 + sizeOf(body))
          case CodeFold.Closing(_, _, body, _, _) =>
            CompressionState(1 + sizeOf(body))
      def rank(state: FoldState): OrderValue = Compression.rank(state)
      def reading(state: FoldState): ModuleReading = ModuleReading.One
  )

  /** The size a code state holds, read by its class without summoning a
    * `ClassTag` at each part (`TermOrder.ownState`), which the code fold reads
    * at every node.
    */
  private def sizeOf(state: FoldState): BigInt = state match
    case CompressionState(size) => size
    case other                  =>
      throw TermOrderError(
        TermOrderErrorReason.NotATerm(OrderTerm.Folded[Nothing](other, false))
      )
