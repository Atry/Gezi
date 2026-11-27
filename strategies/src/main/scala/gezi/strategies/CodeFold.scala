package gezi.strategies

import gezi.ir.NativeSpecializer

import gezi.ir.Code
import gezi.ir.Hole

/** One layer of a thunk's code, folded part by part by a module that folds
  * codes (`NormalityModule.codeFolding`), each part read through its code
  * state, so that the extraction finds a thunk's least candidates of each
  * reading by a dynamic program over its code, an inner thunk's code included
  * (`ThunkCandidates`), instead of listing every combination of the readings of
  * the fillings under an inner thunk, which a module that folds a thunk whole
  * reads jointly.
  *
  * A code is folded with `depth` counting the thunks around a part from the
  * thunk whose candidates are found (0) inward, so that a module tells a hole
  * of the thunk from a hole of an inner one. A filling of the thunk that the
  * code reads more than once, counted through inner thunks, is marked
  * `repeated` where the code reads it and given again, once, when the thunk is
  * closed (`Closing`), so that a module that counts a thunk's fillings once
  * each, not once per occurrence, counts a repeated filling there. The
  * extraction lists the repeated fillings jointly, one entry each at a time, so
  * the parts it compares read the same entries of them.
  */
enum CodeFold[C <: NativeSpecializer & Singleton]:

  /** A slot that holds a filling of the thunk whose candidates are found, read
    * as the term given: `OrderTerm.Folded` by its state, or
    * `OrderTerm.Unpriced` by its reading where the code reads it only as a
    * criterion; `repeated` where the code reads that filling more than once,
    * counted through inner thunks.
    */
  case Filling(term: OrderTerm[C], repeated: Boolean)

  /** A slot that holds a filling of an inner thunk: the filling's code folded
    * (`part`).
    */
  case InnerFilling[C <: NativeSpecializer & Singleton](part: FoldState)
      extends CodeFold[C]

  /** A slot that holds a hole: of the thunk `depth` thunks in, at `position`
    * among its `count` holes in lambda order.
    */
  case HoleSlot[C <: NativeSpecializer & Singleton](
      depth: Int,
      position: Int,
      count: Int
  ) extends CodeFold[C]

  /** An application of two parts. */
  case Apply[C <: NativeSpecializer & Singleton](
      function: FoldState,
      argument: FoldState
  ) extends CodeFold[C]

  /** A parallel of a part and its criterion, a slot that holds a filling of the
    * thunk whose candidates are found.
    */
  case Parallel[C <: NativeSpecializer & Singleton](
      left: FoldState,
      criterion: FoldState
  ) extends CodeFold[C]

  /** The range of a specialization's typed member, `F (A ∥ D) ∥ R`: a parallel
    * of the typed application and the range, a slot that holds a filling of the
    * thunk whose candidates are found, read as `TermReading.typedMember` reads
    * it (`OrderTerm.Parallel`'s `specializationRange`).
    */
  case RangeParallel[C <: NativeSpecializer & Singleton](
      left: FoldState,
      range: FoldState
  ) extends CodeFold[C]

  /** A choice of the code, at depth 0: its members as written, the right spine
    * of the choice listed (`Code.ChoiceMembers`), each folded; and, where the
    * dispatch patterns read it as a specialization or a judgment
    * (`TermReading.resolved`), the term they read it as, folded: the typed
    * member, or the judgment's value. A module whose fold of a whole thunk
    * reads the code as written (`narrow_blocks`, compression) reads the
    * members; one whose fold resolves the dispatch (specialization attraction)
    * reads `dispatched`, or the members where it is none.
    */
  case Choice[C <: NativeSpecializer & Singleton](
      members: Vector[FoldState],
      dispatched: Option[FoldState]
  ) extends CodeFold[C]

  /** An inner thunk of the code, `depth` thunks in: its own code, holes and
    * fillings' codes, its code folded with its fillings in their slots (`body`,
    * at `depth + 1`), and the parts of the fillings its code does not read, in
    * filling order.
    */
  case InnerThunk[C <: NativeSpecializer & Singleton](
      depth: Int,
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Code],
      body: FoldState,
      unread: Vector[FoldState]
  ) extends CodeFold[C]

  /** The thunk whose candidates are found, closed: its code, its holes, its
    * code folded (`body`, at depth 0), the fillings its code does not read and
    * those it reads more than once (`Filling`'s `repeated`), each as `Filling`
    * reads it, in filling order. The state a module gives it is the state
    * `NormalityModule.folded` gives the layer
    * `OrderTerm.Thunk(code, holes, fillings)` over the same fillings
    * (`CostMonotonicityLaws.foldedByParts`). A repeated filling is counted here
    * rather than where the code reads it because the extraction lists the
    * repeated fillings jointly (`CodeCandidates`): within one combination every
    * part it compares at a node reads the same entry of each of them, so what
    * they add to a part's rank is the same for every part compared, and leaving
    * it out of the parts changes no comparison.
    */
  case Closing(
      code: Code,
      holes: Vector[Hole],
      body: FoldState,
      unread: Vector[OrderTerm[C]],
      repeated: Vector[OrderTerm[C]]
  )

/** A module's fold of codes (`CodeFold`), layer by layer. Its contract, which
  * `CostMonotonicityLaws.foldedByParts` checks of each module that has one:
  *   - closing a code folded layer by layer gives the state the module's
  *     `folded` gives the whole thunk over the same fillings;
  *   - a code part's state is a function of its parts' states, and its
  *     `reading` decides everything a part around it reads of it beyond its
  *     `rank`, within which the rank is monotone in each part's, so that the
  *     extraction keeps one least part of each reading
  *     (`gezi.extraction.CostModel`, THE CONTRACT, here over the parts of a
  *     code).
  * A code state holds what the module's own `folded` derives from the code's
  * syntax and the fillings' states (kinds, counts, sizes): no fact about a
  * node's type and no record kept beside the term, a memo of a function of the
  * syntax (`CONTRIBUTING.md`, "Tables").
  */
trait CodeFolding[C <: NativeSpecializer & Singleton]:

  /** The state of the code layer. */
  def folded(layer: CodeFold[C], reading: TermReading[C]): FoldState

  /** The rank of a code part's state, smaller better, as the module's `rank` of
    * a term's.
    */
  def rank(state: FoldState): OrderValue

  /** The reading of a code part's state: everything a part around it reads of
    * it beyond its rank.
    */
  def reading(state: FoldState): ModuleReading
