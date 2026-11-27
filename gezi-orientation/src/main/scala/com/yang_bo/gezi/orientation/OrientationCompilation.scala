package com.yang_bo.gezi.orientation

import com.yang_bo.gezi.ir.BindingNormalForm
import com.yang_bo.gezi.ir.ChoiceSpine
import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Spine
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.ir.{
  Apply,
  Choice,
  NoinlineLeaf,
  Opaque,
  Parallel,
  Slot,
  Thunk,
  UriNode
}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** An enabled lemma as the orientation compiler takes it: its identifier, the
  * number of its metavariables, numbered from 0, and the patterns of its two
  * sides. A side's eta-shaped lambda `\x. M x` is the thunk pattern it is
  * written as; the compiler reads it as a closure. No side holds
  * `Pattern.Closure`.
  */
final case class LemmaSides[C <: NativeSpecializer & Singleton](
    lemma: LemmaIdentifier,
    arity: Int,
    left: Pattern[C],
    right: Pattern[C]
)

/** The orientations of a set of lemmas and the instructions their matched sides
  * mention, which are added to every graph before its inputs.
  */
final case class CompiledOrientations[C <: NativeSpecializer & Singleton](
    orientations: Vector[Orientation[C]],
    patternInstructions: Vector[Configured[C]]
)

/** How a round's enabled lemmas and the store become the orientations its
  * saturation matches and the instructions those mention, numbered from 0: the
  * number of an orientation is the order the indexer files its seeds in, so it
  * decides which matches a saturation a budget cuts has made. A round's choice,
  * as the indexer, the lemma encoding and the e-matching backend are; the
  * framework's default is chosen in `com.yang_bo.gezi.contest.entry.Defaults`. An
  * orientation unites or adds only what its lemma states, whichever are
  * compiled, so the choice changes which instances a cut saturation has made,
  * never their soundness.
  */
trait OrientationCompiler:
  def compiled[C <: NativeSpecializer & Singleton](
      lemmas: Vector[LemmaSides[C]],
      store: Store[C]
  ): CompiledOrientations[C]

/** The framework's orientation compiler, `OrientationCompilation.compiled`. */
object StandardOrientationCompiler extends OrientationCompiler:
  def compiled[C <: NativeSpecializer & Singleton](
      lemmas: Vector[LemmaSides[C]],
      store: Store[C]
  ): CompiledOrientations[C] =
    OrientationCompilation.compiled(lemmas, store)

/** The compiler of lemma orientations, the port of the Prolog baseline's
  * `orientations_compiled/2` and the predicates it calls
  * (`lemma_orientation/5`, `pattern_normalized/2`, `orientation_content/3`,
  * `orientation_filed/4` without its seed clauses, which the index module
  * writes as seeds, `essential/4` and `pattern_handle/2`). It reads the
  * patterns and the store and nothing else: it names no lemma.
  *
  * A USABLE ORIENTATION of a lemma matches one side, rigid, and adds the other,
  * which mentions no metavariable the matched side lacks (the baseline makes no
  * schematic variable). A lemma whose sides are one pattern has its forward
  * orientation only; an orientation whose matched side is a choice of which the
  * added side, rigid, is a member mentioning every metavariable of the choice,
  * is not compiled.
  *
  * THE ORDER. The orientations are numbered in the standard order of Prolog
  * terms on their contents (`StandardOrder`): `content(Matched, Added)`, each
  * pattern with every instruction written out as the term it stands for and
  * every code as its tree, the same in every process. Where two orientations
  * have one content, the baseline ordered them by the address of the lemma's
  * instruction, which differs between processes; here they keep the order of
  * the lemmas given, then the backward orientation before the forward one, as
  * the standard order puts `backward` before `forward`.
  *
  * THE SHARED SUBTERMS of an orientation are listed in the standard order of
  * their contents, duplicates once. The baseline sorted them with `sort/2` on
  * the patterns, whose instructions Prolog compares by address, an order that
  * differs between processes; the order by content is the same in every
  * process.
  *
  * THE PATTERN INSTRUCTIONS are the instructions the baseline's seed clauses
  * mention, in the order they first mention them: the clauses of the
  * orientations that add (whose added side is no metavariable and no subpattern
  * of the matched side), in their order, then those of the orientations that
  * only unite. The first clause of an orientation stands at the root of its
  * matched side and mentions every instruction of the side below the root, left
  * to right; a matched side that is an instruction mentions none.
  */
object OrientationCompilation:

  /** The orientations of the lemmas, numbered, and their pattern instructions.
    * The lemmas are distinct; no instruction of their patterns is opaque.
    *
    * Each usable orientation matches its side as stated (`closuresRead`), and
    * where that side holds a thunk the front end spells otherwise
    * (`normalized`), a second orientation of the same lemma and direction
    * matches the respelled side: a program, which is in the front end's
    * spelling, holds the respelled thunk, and a node another lemma added in the
    * stated spelling holds the stated one. Both add the side as stated, so the
    * second orientation only adds matches, never changes what a lemma adds.
    *
    * FIXME: the choices of this compiler are fixed in it,
    * https://github.com/Atry/private-overlay/issues/2032 each with one way
    * implemented: every usable direction, a second orientation per respelled
    * side, and the numbering in the standard order, which orders the matches.
    * Another compiler replaces them whole (`OrientationCompiler`, a round's
    * `orientation_compiler`).
    */
  def compiled[C <: NativeSpecializer & Singleton](
      lemmas: Vector[LemmaSides[C]],
      store: Store[C]
  ): CompiledOrientations[C] =
    require(
      lemmas.map(_.lemma).distinct.size == lemmas.size,
      "the lemmas given are distinct"
    )
    val contents = Contents[C](store)
    val oriented = for
      (sides, lemmaPosition) <- lemmas.zipWithIndex
      left = closuresRead(sides.left, store)
      right = closuresRead(sides.right, store)
      (direction, matched, added) <- usable(left, right)
      respelledMatched = normalized(
        direction match
          case Direction.Forward  => sides.left
          case Direction.Backward => sides.right,
        store
      )
      spelling <- matched +: Vector(respelledMatched).filter(respelling =>
        respelling != matched && orientationUsable(direction, respelling, added)
      )
    yield (
      contents.orientationContent(spelling, added),
      lemmaPosition,
      directionName(direction),
      Oriented(sides.lemma, direction, sides.arity, spelling, added)
    )
    val sorted = oriented.sortWith((first, second) =>
      val byContent = StandardOrder.ordering.compare(first._1, second._1)
      if byContent != 0 then byContent < 0
      else if first._2 != second._2 then first._2 < second._2
      else first._3 < second._3
    )
    val orientations = sorted.zipWithIndex.map {
      case ((_, _, _, found), index) =>
        filed(found, index, contents)
    }
    CompiledOrientations(orientations, patternInstructions(orientations))

  /** An orientation before it is numbered. */
  private final case class Oriented[C <: NativeSpecializer & Singleton](
      lemma: LemmaIdentifier,
      direction: Direction,
      arity: Int,
      matched: Pattern[C],
      added: Pattern[C]
  )

  private def directionName(direction: Direction): String = direction match
    case Direction.Forward  => "forward"
    case Direction.Backward => "backward"

  /** The usable orientations of a lemma whose normalized sides are given, the
    * forward one first.
    */
  private def usable[C <: NativeSpecializer & Singleton](
      left: Pattern[C],
      right: Pattern[C]
  ): Vector[(Direction, Pattern[C], Pattern[C])] =
    Vector((Direction.Forward, left, right), (Direction.Backward, right, left))
      .filter(orientationUsable)

  /** Whether the orientation that matches `matched` and adds `added` is usable.
    */
  private def orientationUsable[C <: NativeSpecializer & Singleton](
      direction: Direction,
      matched: Pattern[C],
      added: Pattern[C]
  ): Boolean =
    rigid(matched) &&
      mentions(added).forall(mentions(matched).contains) &&
      (if matched == added then direction == Direction.Forward
       else
         matched match
           case Pattern.Choice(_, _) =>
             !(rigid(added) && Pattern.choiceMembers(matched).contains(added) &&
               mentions(matched).forall(mentions(added).contains))
           case _ => true)

  /** The pattern with every eta-shaped lambda `\x. M x` read as the closure of
    * M's metavariable, and every other thunk with holes in the front end's
    * spelling (`respelled`). Throws `IllegalArgumentException` for a record
    * pattern of more than one entry: a record pattern is a definition or `{}`,
    * the record of no entries.
    *
    * FIXME (2026-11-08): reading `\x. M x` as M's closure is the η rule, which
    * https://github.com/Atry/private-overlay/issues/1970 is not sound on terms
    * with records once the records' axioms, the missing field's among them,
    * hold. The matcher binds M to a class, not a term, so whether M holds a
    * record is no local check here: a class holding a closure state may also
    * hold a record after a union. Candidate: a class analysis of whether a
    * class holds a record or a field selection, read by the closure seed's
    * `HasClosure` step.
    */
  def normalized[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      store: Store[C]
  ): Pattern[C] =
    read(pattern, store, respelling = true)

  /** The pattern with every eta-shaped lambda `\x. M x` read as the closure of
    * M's metavariable, every other thunk as stated: `normalized` without the
    * respelling, the side as the encoding states it.
    */
  def closuresRead[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      store: Store[C]
  ): Pattern[C] =
    read(pattern, store, respelling = false)

  private def read[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      store: Store[C],
      respelling: Boolean
  ): Pattern[C] = pattern match
    case thunk @ Pattern.Thunk(code, holes, fillings) =>
      lambdaMetavariable(thunk, store) match
        case Some(index) => Pattern.Closure(index)
        case None        =>
          (if respelling then respelled(thunk) else None) match
            case Some(spelling) => read(spelling, store, respelling)
            case None           =>
              Pattern.Thunk(
                code,
                holes,
                fillings.map(read(_, store, respelling))
              )
    case Pattern.Metavariable(_) | Pattern.InstructionReference(_) => pattern
    case Pattern.Apply(function, argument)                         =>
      Pattern.Apply(
        read(function, store, respelling),
        read(argument, store, respelling)
      )
    case Pattern.Parallel(left, right) =>
      Pattern.Parallel(
        read(left, store, respelling),
        read(right, store, respelling)
      )
    case Pattern.Choice(left, right) =>
      Pattern.Choice(
        read(left, store, respelling),
        read(right, store, respelling)
      )
    case Pattern.Closure(_) =>
      throw IllegalArgumentException(
        "a lemma side holds no closure before it is normalized"
      )

  /** The pattern of the front end's spelling of a thunk pattern with holes that
    * is not its own spelling (`BindingNormalForm.respelled`), its fillings
    * patterns over the thunk's fillings by position; none for a thunk that is.
    * The front end spells a program's closed subterms into fillings, the
    * e-graph makes every thunk node with holes in that spelling
    * (`com.yang_bo.gezi.egraph.EGraph.layerMade`, `com.yang_bo.gezi.egraph.Respelling`), and a lemma's
    * side split by an encoding into its metavariables' fillings and the holes
    * left need not be so spelled: `λk. λa. λz. k a` has the thunk
    * `thunk(apply(slot 0, slot 1), [ignored], [k, a])`, whose instances a
    * program holds as `thunk(slot 0, [ignored], [apply(k, a)])`. A pattern
    * holding the first looks for a code no program holds, and its lemma never
    * fires.
    *
    * FIXME (2026-11-17): the fillings are kept by position, never merged by
    * https://github.com/Atry/private-overlay/issues/1971 metavariable: when the
    * front end spells an instance whose two fillings are equal terms (two
    * metavariables bound to one term, or one metavariable in two fillings) it
    * makes them one slot, and this pattern, which keeps two, does not match
    * that instance: an instance lost, never an unsound one. Which fillings are
    * equal is known only when the metavariables are bound, so no spelling of
    * the pattern alone matches every instance. Candidate: a matching step that
    * respells a thunk node's code under the bindings (`BindingNormalForm.of`),
    * as the higher-order matching does; not designed.
    */
  private def respelled[C <: NativeSpecializer & Singleton](
      thunk: Pattern.Thunk[C]
  ): Option[Pattern[C]] = thunk match
    case Pattern.Thunk(code, holes, fillings) if holes.nonEmpty =>
      BindingNormalForm
        .respelled(code, holes, fillings.size)
        .map((spelledCode, spelledHoles, spelledFillings) =>
          Pattern.Thunk(
            spelledCode,
            spelledHoles,
            spelledFillings
              .map(BindingNormalForm.fillingMapped(_, fillings)(layerPattern))
          )
        )
    case _ => None

  /** A layer of a respelled filling over its children's patterns as a pattern.
    * A filling is a code over the fillings' slots, so its layer is never a
    * noinline leaf, which its leaf type `Nothing` says.
    */
  private def layerPattern[C <: NativeSpecializer & Singleton](
      layer: LayerWith[Pattern[C], Nothing]
  ): Pattern[C] = layer match
    case Apply(function, argument)    => Pattern.Apply(function, argument)
    case Parallel(left, right)        => Pattern.Parallel(left, right)
    case Choice(left, right)          => Pattern.Choice(left, right)
    case Thunk(code, holes, fillings) => Pattern.Thunk(code, holes, fillings)
    case view: com.yang_bo.gezi.ir.StorageView[?] =>
      throw IllegalStateException(
        s"a respelled filling's layer is the storage view $view"
      )
    case com.yang_bo.gezi.ir.NoinlineLeaf(leaf) => leaf

  /** The metavariable of a thunk pattern that is a lambda pattern
    * `thunk(apply(slot(F), slot(H)), [H], [metavariable(Index)])`, F not H.
    */
  private def lambdaMetavariable[C <: NativeSpecializer & Singleton](
      thunk: Pattern.Thunk[C],
      store: Store[C]
  ): Option[Int] =
    thunk match
      case Pattern.Thunk(
            code,
            Vector(Hole.Bound(hole)),
            Vector(Pattern.Metavariable(index))
          ) =>
        store.code(code) match
          case Apply(function, argument) =>
            (store.code(function), store.code(argument)) match
              case (Slot(functionSlot), Slot(argumentSlot))
                  if argumentSlot == hole && functionSlot != hole =>
                Some(index)
              case _ => None
          case _ => None
      case _ => None

  /** The pattern has a rigid symbol: an instruction, a closure, a thunk, a
    * choice, a parallel, a record, a field selection, or an application with a
    * rigid side.
    */
  def rigid[C <: NativeSpecializer & Singleton](pattern: Pattern[C]): Boolean =
    pattern match
      case Pattern.Metavariable(_)           => false
      case Pattern.Apply(function, argument) =>
        rigid(function) || rigid(argument)
      case _ => true

  /** The metavariables the pattern mentions, a closure's included, each once.
    */
  def mentions[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Int] = (pattern match
    case Pattern.Metavariable(index) => Vector(index)
    case Pattern.Closure(index)      => Vector(index)
    case other                       => other.children.flatMap(mentions)
  ).distinct

  /** The metavariables of the closures the pattern mentions, the function
    * metavariables, each once.
    */
  private def closureMentions[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Int] = (pattern match
    case Pattern.Closure(index) => Vector(index)
    case other                  => other.children.flatMap(closureMentions)
  ).distinct

  /** The metavariables at the head of an application's spine in the pattern: an
    * added side's applications of them are read by β. Without them, an instance
    * such as `C @ names = … C @ typed names …`, C matched by the reverse beta
    * to an abstraction, built `C @ typed names` unread and never reduced it
    * (measured 2026-11-07 on the inlined hot site: 16 β steps against 32 for
    * the same term given as an input).
    *
    * FIXME (2026-11-07): matching does not check
    * https://github.com/Atry/private-overlay/issues/1972 how the application it
    * binds was built, so the matched application may be one a code body built
    * unread, a slot-headed one such as a self-application inside a fixed
    * point's body; the added side's application of the same metavariable is
    * then read, and may unfold what `Indexing.codeBuilding` leaves unread.
    * Sound, β being an equation; its termination rests on the round's cap.
    * Candidate fix: read the added application only when the matched one is
    * readable.
    */
  private def appliedMetavariables[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Int] = (pattern match
    case Pattern.Apply(function, argument) =>
      spineHead(function).toVector ++ appliedMetavariables(
        function
      ) ++ appliedMetavariables(argument)
    case other => other.children.flatMap(appliedMetavariables)
  ).distinct

  private def spineHead[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Option[Int] = Spine.of(pattern)._1 match
    case Pattern.Metavariable(index) => Some(index)
    case Pattern.Closure(index)      => Some(index)
    case _                           => None

  private def compound[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Boolean = pattern match
    case Pattern.Apply(_, _) | Pattern.Parallel(_, _) | Pattern.Choice(_, _) |
        Pattern.Thunk(_, _, _) =>
      true
    case _ => false

  /** The orientation numbered `index`, with its functions, its essential
    * metavariables and its shared subterms.
    */
  private def filed[C <: NativeSpecializer & Singleton](
      oriented: Oriented[C],
      index: Int,
      contents: Contents[C]
  ): Orientation[C] =
    val (essential, shared) =
      essentialAndShared(oriented.added, oriented.matched, contents)
    Orientation(
      index = index,
      lemma = oriented.lemma,
      direction = oriented.direction,
      arity = oriented.arity,
      matched = oriented.matched,
      added = oriented.added,
      functions = (closureMentions(oriented.matched) ++ closureMentions(
        oriented.added
      ) ++ appliedMetavariables(oriented.matched)).distinct.sorted,
      essential = essential,
      shared = shared
    )

  /** What decides what an instance adds: the metavariables the added side
    * mentions outside the shared subterms, ascending, and the shared subterms,
    * the largest compound subterms of the added side that are subpatterns of
    * the matched side as well; an added metavariable or closure is essential
    * and shares nothing.
    */
  private def essentialAndShared[C <: NativeSpecializer & Singleton](
      added: Pattern[C],
      matched: Pattern[C],
      contents: Contents[C]
  ): (Vector[Int], Vector[Pattern[C]]) = added match
    case Pattern.Metavariable(index) => (Vector(index), Vector.empty)
    case Pattern.Closure(index)      => (Vector(index), Vector.empty)
    case _                           =>
      val shared = sharedSubterms(added, matched).distinct
        .sortWith((first, second) =>
          StandardOrder.ordering
            .compare(contents.pattern(first), contents.pattern(second)) < 0
        )
      (mentionedOutside(added, shared).distinct.sorted, shared)

  private def sharedSubterms[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      matched: Pattern[C]
  ): Vector[Pattern[C]] =
    if compound(pattern) && (pattern == matched || Orientations.contains(
        matched,
        pattern
      ))
    then Vector(pattern)
    else pattern.children.flatMap(sharedSubterms(_, matched))

  private def mentionedOutside[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      shared: Vector[Pattern[C]]
  ): Vector[Int] =
    if shared.contains(pattern) then Vector.empty
    else
      pattern match
        case Pattern.Metavariable(index) => Vector(index)
        case Pattern.Closure(index)      => Vector(index)
        case other => other.children.flatMap(mentionedOutside(_, shared))

  /** The instructions of the matched sides, those of the orientations that add
    * first, each once in the order first met. A matched side that is a
    * reference is filed too: its orientation is seeded under the node filed
    * under the instruction (`Seeding`), and a node a lemma writes with the
    * instruction's layer is that filed node only when the graph holds it.
    * Filing the roots here, rather than seeding a reference under every class
    * its layer's structural pattern matches, is chosen by measurement
    * (2026-11-02, strategies' FixedWidthTypingLawTest, int16_add on two 17-bit
    * words): with the roots left out, the node a lemma writes for a reference
    * side of no metavariable (`word_structure_above zero`) is filed under no
    * instruction, the lemma that matches it never fires, and the run reaches
    * its fixed point at 3,045 instances with no clash; with the roots filed it
    * clashes, at 3,003 instances. The second candidate would make every
    * reference a structural match, the encoding that filing the references
    * replaced.
    */
  private def patternInstructions[C <: NativeSpecializer & Singleton](
      orientations: Vector[Orientation[C]]
  ): Vector[Configured[C]] =
    val (onlyUniting, adding) = orientations.partition(onlyUnitesAsFiled)
    (adding ++ onlyUniting)
      .flatMap(orientation => instructions(orientation.matched))
      .distinct

  /** The baseline's kind `merge`: the added side is a metavariable, or a
    * subpattern of the matched side below its root; an added closure counts
    * only in the second way.
    */
  private def onlyUnitesAsFiled[C <: NativeSpecializer & Singleton](
      orientation: Orientation[C]
  ): Boolean = orientation.added match
    case Pattern.Metavariable(_) => true
    case added => Orientations.contains(orientation.matched, added)

  private def instructions[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[Configured[C]] = pattern match
    case Pattern.InstructionReference(instruction) => Vector(instruction)
    case other => other.children.flatMap(instructions)

  /** The contents of patterns over the store: every instruction written out as
    * the term it stands for, every code as its tree.
    */
  private final case class Contents[C <: NativeSpecializer & Singleton](
      store: Store[C]
  ):
    // A choice is written as the list of the members of its right `+` spine
    // (`ChoiceSpine.members`), so that a chain reads as the member list it
    // was before the choice became binary.

    def orientationContent(matched: Pattern[C], added: Pattern[C]): PrologTerm =
      PrologTerm.Compound("content", Vector(pattern(matched), pattern(added)))

    def pattern(pattern: Pattern[C]): PrologTerm = pattern match
      case Pattern.Metavariable(index) =>
        compound("metavariable", PrologTerm.Integer(index))
      case Pattern.Closure(index) =>
        compound("closure", PrologTerm.Integer(index))
      case Pattern.InstructionReference(referenced) =>
        compound("handle", instruction(referenced))
      case Pattern.Apply(function, argument) =>
        compound("apply", this.pattern(function), this.pattern(argument))
      case Pattern.Parallel(left, right) =>
        compound("parallel", this.pattern(left), this.pattern(right))
      case Pattern.Choice(_, _) =>
        compound(
          "choice",
          StandardOrder.list(Pattern.choiceMembers(pattern).map(this.pattern))
        )
      case Pattern.Thunk(code, holes, fillings) =>
        compound(
          "thunk",
          codeTree(code),
          holeList(holes),
          StandardOrder.list(fillings.map(this.pattern))
        )

    /** The instruction, as the Prolog front end's `instruction_stored/2` writes
      * it; an opaque instruction, whose layer is not known, as `opaque(Name)`.
      */
    def instruction(written: Configured[C]): PrologTerm =
      if written.representation.heldAsLeaf then
        compound("opaque", PrologTerm.Atom(written.toString))
      else
        written.layer match
          case Apply(function, argument) =>
            compound("apply", instruction(function), instruction(argument))
          case Parallel(left, right) =>
            compound("parallel", instruction(left), instruction(right))
          case Choice(_, _) =>
            val members = ChoiceSpine.members(
              written,
              (term: Configured[C]) =>
                term.layer match
                  case Choice(left, right) => Some((left, right))
                  case _                   => None
            )
            compound("choice", StandardOrder.list(members.map(instruction)))
          case Thunk(code, holes, fillings) =>
            compound(
              "thunk",
              codeTree(code),
              holeList(holes),
              StandardOrder.list(fillings.map(instruction))
            )
          case UriNode(_) | Opaque(_) =>
            throw IllegalStateException(s"the opaque $written has no layer")
          case storage: com.yang_bo.gezi.ir.NativeStorage =>
            throw IllegalStateException(
              s"the storage $storage is no leaf of the store, and has no layer of the IR"
            )

    private def codeTree(identifier: Code): PrologTerm =
      store.code(identifier) match
        case Slot(index) => compound("slot", PrologTerm.Integer(index))
        case Apply(function, argument) =>
          compound("apply", codeTree(function), codeTree(argument))
        case Parallel(left, right) =>
          compound("parallel", codeTree(left), codeTree(right))
        case Choice(_, _) =>
          val Code.ChoiceMembers(members) = identifier
          compound("choice", StandardOrder.list(members.map(codeTree)))
        case Thunk(inner, holes, fillings) =>
          compound(
            "thunk",
            codeTree(inner),
            holeList(holes),
            StandardOrder.list(fillings.map(codeTree))
          )

    private def holeList(holes: Vector[Hole]): PrologTerm =
      StandardOrder.list(holes.map {
        case Hole.Bound(slot) => PrologTerm.Integer(slot)
        case Hole.Ignored     => PrologTerm.Atom("ignored")
      })

    private def compound(name: String, arguments: PrologTerm*): PrologTerm =
      PrologTerm.Compound(name, arguments.toVector)
