package gezi.ematching.indexing

import gezi.egraph.Head
import gezi.egraph.MemberShape
import gezi.egraph.PositionRole
import gezi.egraph.UserRole
import gezi.orientation.Orientation
import gezi.orientation.Orientations
import gezi.ematching.LayerTemplate
import gezi.ematching.Register
import gezi.ematching.Seed
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ematching.Step
import gezi.ir.Pattern
import gezi.ir.Spine

/** The seeds of an orientation, as the Prolog baseline's `seed_clause/7`
  * writes its seed clauses: one for every compound position and every
  * lambda position of the matched side, in pre-order, except the positions
  * inside a shallow witness; or, when the matched side is an instruction, one
  * filed under the instruction. A seed's steps are the clause's goals in their
  * order, its registers the clause's variables.
  */
private[indexing] object Seeding:

  /** The seeds of the orientation with the kind and the key each is filed
    * under, in the order of their positions.
    */
  def seeds(orientation: Orientation): Vector[((SeedKind, SeedKey), Seed)] =
    val kind =
      if Orientations.onlyUnites(orientation) then SeedKind.Merge
      else SeedKind.Add
    orientation.matched match
      case Pattern.InstructionReference(instruction) =>
        if kind == SeedKind.Add then
          Vector(
            (SeedKind.Add, SeedKey.InstructionNode(instruction)) -> Seed(
              orientation = orientation.index,
              steps = Vector(Step.Root(0, 1)),
              root = 1,
              bindings = Vector.fill(orientation.arity)(None)
            )
          )
        else Vector.empty
      case matched =>
        val context = Context(matched, orientation.essential)
        Orientations.positions(matched).collect {
          case (path, position)
              if seedable(position) && !insideShallowWitness(path, context) =>
            seedAt(orientation, kind, context, path, position)
        }

  /** The matched side and the essential metavariables, what decides which
    * subpatterns are witnesses.
    */
  private final case class Context(matched: Pattern, essential: Vector[Int])

  /** A seed being written: the next register free, the steps so far, and the
    * register each metavariable was bound to.
    */
  private final case class Writing(
      nextRegister: Register,
      steps: Vector[Step],
      bindings: Vector[Option[Register]]
  ):
    def fresh: (Writing, Register) =
      (copy(nextRegister = nextRegister + 1), nextRegister)

    def freshRegisters(count: Int): (Writing, Vector[Register]) =
      (
        copy(nextRegister = nextRegister + count),
        Vector.range(nextRegister, nextRegister + count)
      )

    def step(added: Step): Writing = copy(steps = steps :+ added)

    /** The metavariable bound to the class at the register. */
    def bound(index: Int, register: Register): Writing =
      copy(bindings = bindings.updated(index, Some(register)))

    /** The class at the register is the metavariable's: bound to it at the
      * metavariable's first occurrence, checked against it at the others.
      */
    def metavariable(index: Int, register: Register): Writing =
      bindings(index) match
        case Some(earlier) => step(Step.Same(register, earlier))
        case None          => bound(index, register)

  private def seedable(pattern: Pattern): Boolean = pattern match
    case Pattern.InstructionReference(_) | Pattern.Metavariable(_) => false
    case _                                                    => true

  private def seedAt(
      orientation: Orientation,
      kind: SeedKind,
      context: Context,
      path: Vector[Int],
      position: Pattern
  ): ((SeedKind, SeedKey), Seed) =
    val initial =
      Writing(1, Vector.empty, Vector.fill(orientation.arity)(None))
    val (key, started, classRegister) = position match
      case Pattern.Closure(index) =>
        val (writing, classRegister) = initial.fresh
        (
          SeedKey.Closure,
          writing
            .step(Step.Root(0, classRegister))
            .step(Step.HasClosure(classRegister))
            .bound(index, classRegister),
          classRegister
        )
      case _ =>
        val (withChildren, childRegisters) =
          initial.freshRegisters(position.children.size)
        val descended = position.children
          .zip(childRegisters)
          .foldLeft(
            withChildren.step(Step.Layer(0, template(position), childRegisters))
          ) { case (writing, (child, register)) =>
            downward(child, register, context, writing)
          }
        val (rooted, classRegister) = descended.fresh
        (seedKey(position), rooted.step(Step.Root(0, classRegister)), classRegister)
    val (finished, rootRegister) =
      upward(path, classRegister, context, started)
    (kind, key) -> Seed(
      orientation = orientation.index,
      steps = finished.steps,
      root = rootRegister,
      bindings = finished.bindings
    )

  /** The key a seed at the position is filed under (the baseline's
    * `seed_key/2`).
    */
  private def seedKey(pattern: Pattern): SeedKey = pattern match
    case Pattern.Apply(_, _) =>
      Orientations.spineHead(pattern) match
        case Some((instruction, arity)) => SeedKey.Headed(Head(instruction, arity))
        case None                  => SeedKey.Apply
    case Pattern.Parallel(_, _)        => SeedKey.Parallel
    case Pattern.Choice(_, _)          => SeedKey.Choice
    case Pattern.Thunk(code, holes, _) => SeedKey.Thunk(code, holes)
    case other =>
      throw IllegalArgumentException(s"no seed key for the pattern $other")

  /** The layer a node at the pattern has (the baseline's `layer_template/3`).
    */
  private def template(pattern: Pattern): LayerTemplate = pattern match
    case Pattern.Apply(_, _)           => LayerTemplate.Apply
    case Pattern.Parallel(_, _)        => LayerTemplate.Parallel
    case Pattern.Choice(_, _)          => LayerTemplate.Choice
    case Pattern.Thunk(code, holes, _) => LayerTemplate.Thunk(code, holes)
    case other =>
      throw IllegalArgumentException(s"no layer template for the pattern $other")

  /** The steps matching the pattern in the class of the node at the
    * register: a check of the class when the pattern is compound and
    * determined; otherwise its matching, once when the pattern is a witness
    * only (the baseline's `down_goals/5`).
    */
  private def downward(
      pattern: Pattern,
      node: Register,
      context: Context,
      writing: Writing
  ): Writing =
    if compound(pattern) && determined(pattern, writing) then
      val (resolvedWriting, found) = resolved(pattern, writing)
      val (withClass, classRegister) = resolvedWriting.fresh
      val (withFound, foundClass) = withClass.fresh
      withFound
        .step(Step.Root(node, classRegister))
        .step(Step.Root(found, foundClass))
        .step(Step.Same(foundClass, classRegister))
    else if witnessOnly(pattern, context) then
      val inner =
        matching(pattern, node, context, writing.copy(steps = Vector.empty))
      inner.copy(steps = writing.steps :+ Step.Once(inner.steps))
    else matching(pattern, node, context, writing)

  /** The steps matching the pattern in the class of the node at the
    * register (the baseline's `match_goals/5`).
    */
  private def matching(
      pattern: Pattern,
      node: Register,
      context: Context,
      writing: Writing
  ): Writing = pattern match
    case Pattern.Metavariable(index) =>
      val (fresh, classRegister) = writing.fresh
      fresh
        .step(Step.Root(node, classRegister))
        .metavariable(index, classRegister)
    case Pattern.Closure(index) =>
      val (fresh, classRegister) = writing.fresh
      fresh
        .step(Step.Root(node, classRegister))
        .step(Step.HasClosure(classRegister))
        .metavariable(index, classRegister)
    case Pattern.InstructionReference(instruction) =>
      val (fresh, classRegister) = writing.fresh
      fresh
        .step(Step.Root(node, classRegister))
        .step(Step.InstructionIn(instruction, classRegister))
    case _ =>
      val (withRoot, classRegister) = writing.fresh
      val (withMember, member) = withRoot.fresh
      val each = pattern match
        case Pattern.Apply(_, _) =>
          Orientations.spineHead(pattern) match
            case Some((instruction, arity)) =>
              Step.EachHeadMember(classRegister, Head(instruction, arity), member)
            case None => Step.EachMember(classRegister, MemberShape.Apply, member)
        case Pattern.Parallel(_, _) =>
          Step.EachMember(classRegister, MemberShape.Parallel, member)
        case Pattern.Choice(_, _) =>
          Step.EachMember(classRegister, MemberShape.Choice, member)
        case _ => Step.EachMember(classRegister, MemberShape.Thunk, member)
      val (withChildren, childRegisters) =
        withMember.freshRegisters(pattern.children.size)
      pattern.children
        .zip(childRegisters)
        .foldLeft(
          withChildren
            .step(Step.Root(node, classRegister))
            .step(each)
            .step(Step.Layer(member, template(pattern), childRegisters))
        ) { case (current, (child, register)) =>
          downward(child, register, context, current)
        }

  /** The steps climbing from the class at the register, at the path, to the
    * matched side's root, matching the other children of every node on the
    * way; the register of the root's class (the baseline's
    * `upward_goals/7`). Where the other children of a node are all
    * determined, the node is looked up by signature instead of read from the
    * class's users.
    */
  private def upward(
      path: Vector[Int],
      classRegister: Register,
      context: Context,
      writing: Writing
  ): (Writing, Register) =
    if path.isEmpty then (writing, classRegister)
    else
      val parentPath = path.init
      val position = path.last
      val parent = patternAt(context.matched, parentPath)
      if parent.children.indices.forall(index =>
          index == position || determined(parent.children(index), writing)
        )
      then
        val (withSiblings, childRegisters) =
          parent.children.zipWithIndex.foldLeft((writing, Vector.empty[Register])) {
            case ((current, registers), (child, index)) =>
              if index == position then (current, registers :+ classRegister)
              else
                val (next, register) = resolved(child, current)
                (next, registers :+ register)
          }
        val (withUser, user) = withSiblings.fresh
        val (rooted, parentClass) = withUser
          .step(Step.Lookup(template(parent), childRegisters, user))
          .fresh
        upward(
          parentPath,
          parentClass,
          context,
          rooted.step(Step.Root(user, parentClass))
        )
      else climbed(parent, parentPath, position, classRegister, context, writing)

  /** The climb to the parent through the users of the class at the register
    * (the baseline's `upward_goals/7` for one level), when a sibling is not
    * determined.
    */
  private def climbed(
      parent: Pattern,
      parentPath: Vector[Int],
      position: Int,
      classRegister: Register,
      context: Context,
      writing: Writing
  ): (Writing, Register) =
    val (withUser, user) = writing.fresh
    val (withChildren, childRegisters) =
      withUser.freshRegisters(parent.children.size)
    val siblingsMatched = parent.children.zipWithIndex.foldLeft(
      withChildren
        .step(userStep(parent, position, classRegister, user))
        .step(Step.Layer(user, template(parent), childRegisters))
    ) { case (current, (child, index)) =>
      if index == position then current
      else downward(child, childRegisters(index), context, current)
    }
    val (rooted, parentClass) = siblingsMatched.fresh
    upward(
      parentPath,
      parentClass,
      context,
      rooted.step(Step.Root(user, parentClass))
    )

  /** The pattern's class is fixed by the metavariables bound so far: each
    * of its leaves is an instruction or a bound metavariable. A lambda pattern is
    * not, since its class must hold a closure state as well.
    */
  private def determined(pattern: Pattern, writing: Writing): Boolean =
    pattern match
      case Pattern.InstructionReference(_)  => true
      case Pattern.Metavariable(index) => writing.bindings(index).isDefined
      case Pattern.Closure(_)          => false
      case other                       => other.children.forall(determined(_, writing))

  /** The steps writing a register with a node of the class of the
    * determined pattern, and that register: an instruction's node, a bound
    * metavariable's register, or the node a compound pattern's layer has over
    * its children's, looked up by signature. Congruence leaves one live node
    * of a signature, so that the lookup finds the one node the matching of
    * the pattern through members or users would find, reading no entry.
    */
  private def resolved(pattern: Pattern, writing: Writing): (Writing, Register) =
    pattern match
      case Pattern.InstructionReference(instruction) =>
        val (fresh, register) = writing.fresh
        (fresh.step(Step.InstructionNode(instruction, register)), register)
      case Pattern.Metavariable(index) =>
        writing.bindings(index) match
          case Some(register) => (writing, register)
          case None =>
            throw IllegalArgumentException(s"the metavariable $index is not bound")
      case Pattern.Closure(index) =>
        throw IllegalArgumentException(s"the lambda pattern of $index is not determined")
      case other =>
        val (withChildren, childRegisters) =
          other.children.foldLeft((writing, Vector.empty[Register])) {
            case ((current, registers), child) =>
              val (next, register) = resolved(child, current)
              (next, registers :+ register)
          }
        val (fresh, register) = withChildren.fresh
        (fresh.step(Step.Lookup(template(other), childRegisters, register)), register)

  /** The step finding a user of the class at the position of a node at the
    * parent pattern (the baseline's `user_goal/5`).
    */
  private def userStep(
      parent: Pattern,
      position: Int,
      classRegister: Register,
      user: Register
  ): Step = (parent, position) match
    case (Pattern.Apply(_, _), 0) =>
      Step.EachUser(classRegister, UserRole.Function, user)
    case (Pattern.Apply(_, _), 1) =>
      Step.EachUser(classRegister, UserRole.Argument, user)
    case (Pattern.Parallel(_, _), 0) =>
      Step.EachUser(classRegister, UserRole.Left, user)
    case (Pattern.Parallel(_, _), 1) =>
      Step.EachUser(classRegister, UserRole.Right, user)
    case (Pattern.Choice(_, _), _) =>
      Step.EachPositionUser(classRegister, PositionRole.Member, position, user)
    case (Pattern.Thunk(_, _, _), _) =>
      Step.EachPositionUser(classRegister, PositionRole.Filling, position, user)
    case other =>
      throw IllegalArgumentException(s"no user step for the position $other")

  private def patternAt(pattern: Pattern, path: Vector[Int]): Pattern =
    path.foldLeft(pattern)((current, position) => current.children(position))

  private def compound(pattern: Pattern): Boolean = pattern match
    case Pattern.Apply(_, _) | Pattern.Parallel(_, _) | Pattern.Choice(_, _) | Pattern.Thunk(_, _, _) =>
      true
    case _ => false

  /** Every occurrence of a metavariable in the pattern, a lambda pattern's
    * included (the baseline's `mentions/2`).
    */
  private def occurrences(pattern: Pattern): Vector[Int] = pattern match
    case Pattern.Metavariable(index) => Vector(index)
    case Pattern.Closure(index)      => Vector(index)
    case _                           => pattern.children.flatMap(occurrences)

  /** The pattern is compound, and each of its metavariables is inessential
    * and occurs in the matched side only inside copies of the pattern, so
    * that one match of it stands for all. The baseline's `witness_only/2`
    * admits one copy; more copies are admitted for this reason: copies
    * matched with the same metavariables match nodes congruent to one
    * another, which lie in one class, so that the first copy, checked once,
    * binds the metavariables, and every other copy, matched with them bound,
    * succeeds exactly when it lies in the first copy's class. An inessential
    * metavariable changes neither an instance's key nor what it adds (the
    * added side mentions it only inside shared subterms, whose classes are
    * the match's), so which match of the first copy stands for all changes no
    * instance.
    */
  private def witnessOnly(pattern: Pattern, context: Context): Boolean =
    compound(pattern) && {
      val inside = occurrences(pattern)
      val everywhere = occurrences(context.matched)
      val copies = copiesIn(context.matched, pattern)
      inside.forall(index =>
        !context.essential.contains(index) &&
          everywhere.count(_ == index) == copies * inside.count(_ == index)
      )
    }

  /** The number of the subpatterns of the matched side equal to the pattern,
    * the matched side itself included.
    */
  private def copiesIn(matched: Pattern, pattern: Pattern): Int =
    (if matched == pattern then 1 else 0) + matched.children.map(copiesIn(_, pattern)).sum

  /** The pattern is a witness only and an instruction applied to distinct
    * metavariables (the baseline's `shallow_witness/2`).
    */
  private def shallowWitness(pattern: Pattern, context: Context): Boolean =
    pattern match
      case Pattern.Apply(_, _) if witnessOnly(pattern, context) =>
        val (head, arguments) = Spine.of(pattern)
        val indices = arguments.collect { case Pattern.Metavariable(index) =>
          index
        }
        head match
          case Pattern.InstructionReference(_) =>
            indices.size == arguments.size &&
            indices.distinct.size == indices.size
          case _ => false
      case _ => false

  /** The position at the path lies in a subpattern that is a shallow
    * witness, the matched side's root excepted, the position itself included
    * (the baseline's `inside_shallow_witness/3`).
    */
  private def insideShallowWitness(
      path: Vector[Int],
      context: Context
  ): Boolean =
    (1 to path.size).exists(length =>
      shallowWitness(patternAt(context.matched, path.take(length)), context)
    )
