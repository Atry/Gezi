package gezi.contest.corpora.reductions

import java.nio.file.Files
import java.nio.file.Path
import gezi.contest.corpora.reductions.Encodings.*
import gezi.directorysugar.DirectoryTree
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Lexeme
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.frontend.TokenKind
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The data of `problems/mixin_builtin` that the mixin_builtin families
  * (`MixinBuiltinFamilies`) build their
  * programs from: MIXINv2's Builtin library desugared file by file into the
  * directory `Builtin`, and the observer `BooleanChurch` beside it.
  *
  * A point is a closed term that carries the bodies, never the names
  * ([[gezi.contest.corpora.reductions]]), so the library
  * it holds is the term the directory tree gives the directory
  * `mixin_builtin` (`DirectoryTree`'s Scaladoc), written out with no URI
  * node: each file read by the front end in the scope the tree reads it in
  * (`DirectoryTree.scope`), and each directory the tree's own
  * `λe. (λ"c1". U_c1 … e) + … + (λ"ck". U_ck … e)`. Two parts of the tree's
  * term are left out, and the point's answer does not depend on either:
  *
  *   - the levels above `mixin_builtin`: the scope a file is read in here
  *     starts at `mixin_builtin`, so a file that named a level above it
  *     would be rejected as a free name by the reader (`FreeNames.Rejected`),
  *     and none does; a level a file does not name is an abstraction its
  *     unit drops by the β rule, and keeping it would write the checkout's
  *     absolute path into every point;
  *   - the entries of `mixin_builtin` other than `Builtin` and
  *     `BooleanChurch`, the point tables and the sample `ThreePlusFour`,
  *     which no program reads: the projection of a key the mixin lacks is
  *     top, and the programs project only those two.
  *
  * A file is read once, when first used; a respelled point renames the
  * labels of the term read (`MixinBuiltinSpelling.relabelled`).
  */
final case class MixinBuiltinLibrary(root: Path):

  /** The directory `problems/mixin_builtin`. */
  private lazy val directory: Path = root.resolve("problems").resolve(MixinBuiltinLibrary.family)

  /** The directory of MIXINv2's Builtin library. */
  private lazy val builtinDirectory: Path = directory.resolve(MixinBuiltinLibrary.builtinKey)

  /** The keys of the files of `Builtin`, ordered as the tree orders them. */
  lazy val builtinKeys: Vector[String] = DirectoryTree.fileKeys(builtinDirectory)

  private def filePath(parent: Path, key: String): Path = parent.resolve(key + DirectoryTree.fileExtension)

  /** The text of each file of `Builtin`, by key. */
  private lazy val builtinTexts: Map[String, String] =
    builtinKeys.map(key => key -> Files.readString(filePath(builtinDirectory, key))).toMap

  /** The text of `BooleanChurch`. */
  private lazy val booleanChurchText: String = Files.readString(filePath(directory, MixinBuiltinLibrary.booleanChurchKey))

  /** Every label the library's files write, the keys of the entries the
    * programs read included: what a respelling renames.
    */
  lazy val labels: Set[String] =
    (booleanChurchText +: builtinKeys.map(builtinTexts)).flatMap(MixinBuiltinLibrary.literals).toSet ++
      builtinKeys ++ Vector(MixinBuiltinLibrary.builtinKey, MixinBuiltinLibrary.booleanChurchKey)

  /** The unit of a file under its scope from `mixin_builtin` down, the
    * enclosing names of the tree's scope of the file (`DirectoryTree.scope`)
    * from that level on: `λmixin_builtin. … λe. M`, a closed term.
    */
  private def fileUnit(path: Path, text: String, levels: Int): DeBruijnTerm =
    Lambdalattice.termInScope(DirectoryTree.scope(path).takeRight(levels), text)

  /** The mixin of the directory `mixin_builtin`, its entries `Builtin` and
    * `BooleanChurch`, a closed term written directly as the reader writes
    * one: `λmixin_builtin. (λ"BooleanChurch". U_BooleanChurch mixin_builtin)
    * + (λ"Builtin". λBuiltin. (λ"c1". U_c1 mixin_builtin Builtin) + …)`.
    * Read once, when first used.
    */
  lazy val directMixinTerm: DeBruijnTerm =
    def member(key: String, body: DeBruijnTerm): DeBruijnTerm = Literals.partialFunction(Literal.text(key), body)
    val units = builtinKeys.map(key => key -> fileUnit(filePath(builtinDirectory, key), builtinTexts(key), 3))
    val booleanChurch = fileUnit(filePath(directory, MixinBuiltinLibrary.booleanChurchKey), booleanChurchText, 2)
    val builtin = DeBruijnTerm.Lambda(
      DeBruijnTerm.nestedChoice(units.map((key, unit) =>
        member(key, DeBruijnTerm.Apply(DeBruijnTerm.Apply(unit, DeBruijnTerm.Variable(1)), DeBruijnTerm.Variable(0)))
      ))
    )
    DeBruijnTerm.Lambda(
      DeBruijnTerm.nestedChoice(
        Vector(
          member(MixinBuiltinLibrary.booleanChurchKey, DeBruijnTerm.Apply(booleanChurch, DeBruijnTerm.Variable(0))),
          member(MixinBuiltinLibrary.builtinKey, builtin)
        )
      )
    )

  /** The mixin with its labels renamed (`MixinBuiltinSpelling.relabelled`),
    * each to a name of as many bytes.
    */
  def mixinTerm(renamed: String => String): DeBruijnTerm = MixinBuiltinSpelling.relabelled(directMixinTerm, labels, renamed)

  /** The direct spelling's mixin, converted once. */
  lazy val directMixin: Term = Term.closed(Defunctionalization.thunkInstruction(directMixinTerm))

/** The names of the data the families read. */
object MixinBuiltinLibrary:

  /** The directory of the data under `problems`, and the family whose point
    * tables it holds.
    */
  val family: String = "mixin_builtin"

  /** The key of the Builtin directory. */
  val builtinKey: String = "Builtin"

  /** The key of the observer file. */
  val booleanChurchKey: String = "BooleanChurch"

  /** The labels a lambdalattice text writes, each a text string token. */
  def literals(text: String): Vector[String] =
    Lambdalattice.lexemes(text).collect { case Lexeme.Token(TokenKind.StringLiteral(label), _) => label }

/** The pieces of the programs of the mixin_builtin families, their labels
  * renamed by `renamed` (the identity for the direct spelling): the
  * encoding of MIXINv2's YAML as partial functions of literals, as the files
  * of `Builtin` write it, a
  * definition `L : V` written `λ"L" L. V`, a projection `X X "L"` and, of a
  * term that is no variable, `(λo. o o "L") X`, as
  * `problems/mixin_builtin/ThreePlusFour.lambdalattice` writes them.
  */
final case class MixinBuiltinWriting(renamed: String => String):

  /** The variable arguments of the label renamed: each bit of its CBOR
    * text string, high bit first, the Scott Boolean of the bit
    * (`Literals.arguments`).
    */
  private def bits(label: String): Vector[Boolean] =
    Literal.text(renamed(label)).bytes.toVector.flatMap(byte => (7 to 0 by -1).map(position => ((byte >> position) & 1) == 1))

  /** `λ"L". body`, the label renamed: the variable arguments partial
    * function of the literal (`Literals.partialFunction`), which takes the
    * bits one by one and is top at the first that differs.
    */
  def member(label: String, body: Term): Term =
    bits(label).foldRight(body)((bit, rest) =>
      λ(argument => if bit then argument(rest)(MixinBuiltinWriting.top) else argument(MixinBuiltinWriting.top)(rest))
    )

  /** `λ"L" L. body L`: a definition, a class whose self is named by the
    * label.
    */
  def definition(label: String)(body: Term => Term): Term = member(label, λ(body))

  /** The function applied to the label renamed, as variable arguments. */
  def keyed(function: Term, label: String): Term =
    applied(function, bits(label).map(bit => if bit then MixinBuiltinWriting.one else MixinBuiltinWriting.zero))

  /** The member L of the mixin X: `X X "L"` for a variable,
    * `(λo. o o "L") X` for any other term.
    */
  def projected(mixin: Term, label: String): Term =
    if isVariable(mixin) then keyed(mixin(mixin), label)
    else λ(self => keyed(self(self), label))(mixin)

  /** The instance of the mixin, `(λo. o o) X`, `new`. */
  def instantiated(mixin: Term): Term = λ(self => self(self))(mixin)

  /** The entry of `Builtin` the class inherits, applied to its self:
    * `(λo. o o "E") (mixin_builtin mixin_builtin "Builtin") self`.
    */
  def inherited(mixinBuiltin: Term, entry: String, self: Term): Term =
    projected(projected(mixinBuiltin, MixinBuiltinLibrary.builtinKey), entry)(self)

  /** `mixin_builtin mixin_builtin "BooleanChurch" self`. */
  def observed(mixinBuiltin: Term, self: Term): Term = projected(mixinBuiltin, MixinBuiltinLibrary.booleanChurchKey)(self)

/** The closed terms every literal of the writing holds, each converted
  * once (`Term.closed`), so that a key's bits cost a node each in a
  * program's conversion and not the nodes of top or of a Boolean: a point of
  * the natural family at n = 64 and R = 10 took 17.8 s to convert with top
  * and the Booleans written as HOAS at each bit (2026-11-21, a scratch
  * probe, the machine's load about 20 to 36). The term is the same once
  * each closed term is written out as its de Bruijn term, as the
  * snapshots write it.
  */
object MixinBuiltinWriting:

  /** top (`Term.top`), the miss of a literal's partial function. */
  val top: Term = Term.closed(Defunctionalization.thunkInstruction(Literals.top))

  /** The bit 1, `λt f. t`. */
  val one: Term = Term.closed(Defunctionalization.thunkInstruction(deBruijn(trueTerm)))

  /** The bit 0, `λt f. f`. */
  val zero: Term = Term.closed(Defunctionalization.thunkInstruction(deBruijn(falseTerm)))

/** How a point of the mixin_builtin families is written: directly, or
  * respelled, so that a compiler cannot recognise the library by its
  * spelling ([[gezi.contest.corpora.reductions]]). A respelling renames every label literal
  * of the program, the library's and the class's, by one bijection drawn
  * from the draws it is given, each label to a name of as many bytes so that
  * a key's bits are as many, and shuffles the members of every choice.
  * The variables are not renamed: the program a point carries is the IR,
  * whose terms are nameless, so an α-renaming would leave it as it is.
  */
object MixinBuiltinSpelling:

  /** The renaming of the labels drawn from the draws: each label, in
    * sorted order, to a name of lowercase letters as long as it, distinct
    * from the names drawn before; and the draws after it.
    */
  def renaming(labels: Set[String], draws: Draws): (Map[String, String], Draws) =
    labels.toVector.sorted.foldLeft((Map.empty[String, String], draws)) { case ((found, current), label) =>
      val (drawn, after) = name(label.length, current)
      val (renamed, afterName) = distinctName(label.length, drawn, found.values.toSet, after)
      (found.updated(label, renamed), afterName)
    }

  @scala.annotation.tailrec
  private def distinctName(length: Int, drawn: String, taken: Set[String], draws: Draws): (String, Draws) =
    if !taken.contains(drawn) then (drawn, draws)
    else
      val (next, after) = name(length, draws)
      distinctName(length, next, taken, after)

  /** A name of lowercase letters of the length. */
  private def name(length: Int, draws: Draws): (String, Draws) =
    (1 to length).foldLeft(("", draws)) { case ((written, current), _) =>
      val (letter, after) = current.number(0 to 25)
      (written + ('a' + letter).toChar, after)
    }

  /** The renaming as a function: each label of the map to its name; throws
    * for a label the map lacks, which the respelling would leave as written.
    */
  def renamed(renaming: Map[String, String]): String => String =
    label => renaming.getOrElse(label, throw IllegalArgumentException(s"the respelling renames no label $label"))

  /** The term with each label literal renamed to a name of as many bytes:
    * each variable arguments partial function of a label
    * (`Literals.partialFunction`) and each run of a label's variable
    * arguments in an application (`Literals.arguments`) written again with
    * the name's bits, whatever stands inside it kept, which a name of as
    * many bits leaves at its depth. A literal is told by its bits: a chain
    * of abstractions `λx. x R top` (a 1) and `λx. x top R` (a 0), and a run of
    * the Scott Booleans `λt f. t` and `λt f. f`, whose bits spell one of the
    * labels (a CBOR text string's head holds its length, so no label's bits
    * begin another's). Throws for a run of Booleans that spells no label,
    * which the library and the classes never write, and for a name of
    * another length.
    */
  def relabelled(term: DeBruijnTerm, labels: Set[String], renamed: String => String): DeBruijnTerm =
    val byBits = labels.toVector.map(label => bitsOf(label) -> label).toMap
    val lengths = byBits.keys.map(_.size).toVector.distinct.sorted
    def renamedBits(bits: Vector[Boolean]): Vector[Boolean] =
      val label = byBits.getOrElse(bits, throw IllegalArgumentException(s"the bits $bits spell no label"))
      val respelled = bitsOf(renamed(label))
      if respelled.size != bits.size then throw IllegalArgumentException(s"$label is renamed to ${renamed(label)}, of another length")
      respelled
    def chain(current: DeBruijnTerm, found: Vector[Boolean]): (Vector[Boolean], DeBruijnTerm) = current match
      case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), whenOne), whenZero))
          if (whenZero eq Literals.top) != (whenOne eq Literals.top) =>
        if whenZero eq Literals.top then chain(whenOne, found :+ true) else chain(whenZero, found :+ false)
      case other => (found, other)
    /** The bits of the chain's literal, the longest prefix that spells a label, and what stands under them. */
    def partialFunction(current: DeBruijnTerm): Option[(Vector[Boolean], DeBruijnTerm)] =
      val (bits, _) = chain(current, Vector.empty)
      lengths.reverse.find(length => length <= bits.size && byBits.contains(bits.take(length))).map(length =>
        (bits.take(length), (1 to length).foldLeft(current)((level, _) => level match
          case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(_, whenOne), whenZero)) =>
            if whenZero eq Literals.top then whenOne else whenZero
          case other => throw IllegalStateException(s"no level of a literal: $other")
        ))
      )
    def rebuilt(bits: Vector[Boolean], inner: DeBruijnTerm): DeBruijnTerm =
      bits.foldRight(inner)((bit, rest) =>
        DeBruijnTerm.Lambda(
          DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), if bit then rest else Literals.top), if bit then Literals.top else rest)
        )
      )
    def bit(argument: DeBruijnTerm): Option[Boolean] =
      if argument eq one then Some(true) else if argument eq zero then Some(false) else None
    def spine(current: DeBruijnTerm, arguments: List[DeBruijnTerm]): (DeBruijnTerm, Vector[DeBruijnTerm]) = current match
      case DeBruijnTerm.Apply(function, argument) => spine(function, argument :: arguments)
      case head                                   => (head, arguments.toVector)
    /** The arguments with each run of Booleans respelled. */
    def respelledArguments(arguments: Vector[DeBruijnTerm]): Vector[DeBruijnTerm] =
      arguments.foldLeft((Vector.empty[DeBruijnTerm], Vector.empty[Boolean])) { case ((done, run), argument) =>
        bit(argument) match
          case Some(value) => (done, run :+ value)
          case None        => (done ++ runArguments(run) :+ argument, Vector.empty)
      } match
        case (done, run) => done ++ runArguments(run)
    def runArguments(run: Vector[Boolean]): Vector[DeBruijnTerm] =
      if run.isEmpty then Vector.empty else renamedBits(run).map(value => if value then one else zero)
    /** The term walked, each distinct subterm once: the terms are interned,
      * so a subterm met again is the one walked before (`memo`).
      */
    def walked(current: DeBruijnTerm, memo: Map[DeBruijnTerm, DeBruijnTerm]): TailRec[(DeBruijnTerm, Map[DeBruijnTerm, DeBruijnTerm])] =
      memo.get(current) match
        case Some(found) => done((found, memo))
        case None        => tailcall(walkedAnew(current, memo)).map((result, after) => (result, after.updated(current, result)))
    def pair(
        left: DeBruijnTerm,
        right: DeBruijnTerm,
        memo: Map[DeBruijnTerm, DeBruijnTerm],
        make: (DeBruijnTerm, DeBruijnTerm) => DeBruijnTerm
    ): TailRec[(DeBruijnTerm, Map[DeBruijnTerm, DeBruijnTerm])] =
      for
        (walkedLeft, afterLeft) <- tailcall(walked(left, memo))
        (walkedRight, afterRight) <- tailcall(walked(right, afterLeft))
      yield (make(walkedLeft, walkedRight), afterRight)
    def walkedAnew(current: DeBruijnTerm, memo: Map[DeBruijnTerm, DeBruijnTerm]): TailRec[(DeBruijnTerm, Map[DeBruijnTerm, DeBruijnTerm])] =
      if current eq Literals.top then done((current, memo))
      else
        partialFunction(current) match
          case Some((bits, inner)) => tailcall(walked(inner, memo)).map((walkedInner, after) => (rebuilt(renamedBits(bits), walkedInner), after))
          case None =>
            current match
              case DeBruijnTerm.Lambda(body) => tailcall(walked(body, memo)).map((walkedBody, after) => (DeBruijnTerm.Lambda(walkedBody), after))
              case DeBruijnTerm.Apply(_, _) =>
                val (head, arguments) = spine(current, Nil)
                for
                  (walkedHead, afterHead) <- tailcall(walked(head, memo))
                  (walkedArguments, afterArguments) <- respelledArguments(arguments).foldLeft(
                    done((Vector.empty[DeBruijnTerm], afterHead)): TailRec[(Vector[DeBruijnTerm], Map[DeBruijnTerm, DeBruijnTerm])]
                  )((before, argument) =>
                    before.flatMap((found, beforeMemo) =>
                      (if bit(argument).nonEmpty then done((argument, beforeMemo)) else tailcall(walked(argument, beforeMemo)))
                        .map((walkedArgument, after) => (found :+ walkedArgument, after))
                    )
                  )
                yield (walkedArguments.foldLeft(walkedHead)(DeBruijnTerm.Apply(_, _)), afterArguments)
              case DeBruijnTerm.Choice(left, right)   => pair(left, right, memo, DeBruijnTerm.Choice(_, _))
              case DeBruijnTerm.Parallel(left, right) => pair(left, right, memo, DeBruijnTerm.Parallel(_, _))
              case other                              => done((other, memo))
    walked(term, Map.empty).result._1

  /** The bits of the label's CBOR text string, high bit first. */
  private def bitsOf(label: String): Vector[Boolean] =
    Literal.text(label).bytes.toVector.flatMap(byte => (7 to 0 by -1).map(position => ((byte >> position) & 1) == 1))

  /** The Scott Booleans a literal's arguments are (`Literals.arguments`). */
  private val one: DeBruijnTerm = deBruijn(trueTerm)
  private val zero: DeBruijnTerm = deBruijn(falseTerm)

  /** The closed term with the members of every choice of it shuffled by
    * the draws, and the draws after it. The members of a choice are those
    * of its right spine (`DeBruijnTerm.choiceMembers`); the term is equal
    * to the one given up to ≃_O, the choice being associative and
    * commutative (the λ-lattice laws). A constant is kept as it is. Each
    * distinct subterm is shuffled once: the terms are interned, so a
    * subterm met again takes the order drawn where it was first met.
    */
  def shuffled(term: Term, draws: Draws): (Term, Draws) = shuffled(deBruijn(term), draws)

  /** `shuffled` of a de Bruijn term. */
  def shuffled(term: DeBruijnTerm, draws: Draws): (Term, Draws) =
    val (shuffledDeBruijn, after, _) = shuffledTerm(term, draws, Map.empty).result
    (Term.closed(Defunctionalization.thunkInstruction(shuffledDeBruijn)), after)

  private type Shuffled = TailRec[(DeBruijnTerm, Draws, Map[DeBruijnTerm, DeBruijnTerm])]

  private def shuffledTerm(term: DeBruijnTerm, draws: Draws, memo: Map[DeBruijnTerm, DeBruijnTerm]): Shuffled =
    memo.get(term) match
      case Some(found) => done((found, draws, memo))
      case None =>
        tailcall(shuffledAnew(term, draws, memo)).map((result, after, afterMemo) => (result, after, afterMemo.updated(term, result)))

  private def shuffledPair(
      left: DeBruijnTerm,
      right: DeBruijnTerm,
      draws: Draws,
      memo: Map[DeBruijnTerm, DeBruijnTerm],
      make: (DeBruijnTerm, DeBruijnTerm) => DeBruijnTerm
  ): Shuffled =
    for
      (shuffledLeft, afterLeft, leftMemo) <- tailcall(shuffledTerm(left, draws, memo))
      (shuffledRight, afterRight, rightMemo) <- tailcall(shuffledTerm(right, afterLeft, leftMemo))
    yield (make(shuffledLeft, shuffledRight), afterRight, rightMemo)

  private def shuffledAnew(term: DeBruijnTerm, draws: Draws, memo: Map[DeBruijnTerm, DeBruijnTerm]): Shuffled = term match
    case literalPart if (literalPart eq Literals.top) || (literalPart eq one) || (literalPart eq zero) => done((literalPart, draws, memo))
    case DeBruijnTerm.Lambda(body) =>
      tailcall(shuffledTerm(body, draws, memo)).map((shuffledBody, after, afterMemo) => (DeBruijnTerm.Lambda(shuffledBody), after, afterMemo))
    case DeBruijnTerm.Apply(function, argument) => shuffledPair(function, argument, draws, memo, DeBruijnTerm.Apply(_, _))
    case DeBruijnTerm.Parallel(left, right)     => shuffledPair(left, right, draws, memo, DeBruijnTerm.Parallel(_, _))
    case DeBruijnTerm.Choice(_, _) =>
      TailRecFolds.folded(DeBruijnTerm.choiceMembers(term), (Vector.empty[DeBruijnTerm], draws, memo)) {
        case ((found, current, currentMemo), member) =>
          shuffledTerm(member, current, currentMemo).map((shuffledMember, after, afterMemo) => (found :+ shuffledMember, after, afterMemo))
      }
        .map((shuffledMembers, afterMembers, membersMemo) =>
          val (permuted, afterPermutation) = permutation(shuffledMembers, afterMembers)
          (DeBruijnTerm.nestedChoice(permuted), afterPermutation, membersMemo)
        )
    case other => done((other, draws, memo))

  /** The members in an order drawn uniformly (Fisher and Yates). */
  private def permutation[Member](members: Vector[Member], draws: Draws): (Vector[Member], Draws) =
    (members.size - 1 to 1 by -1).foldLeft((members, draws)) { case ((current, before), last) =>
      val (chosen, after) = before.number(0 to last)
      (current.updated(last, current(chosen)).updated(chosen, current(last)), after)
    }
