package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** A Datalog rule of the mixin family, in the labeled family's forms. */
enum DatalogRule:

  /** head(X, Z) from relations(1)(X, Y1), ..., relations(n)(Yn-1, Z). */
  case Join(head: String, relations: Vector[String])

  /** head(X, Y) from left(X, Y) and right(X, Y). */
  case Intersection(head: String, left: String, right: String)

  /** head(X, W) from relation(X, Y), relation(Y, constant) and
    * relation(constant, W).
    */
  case ConstantJoin(head: String, relation: String, constant: String)

  /** head(X, Y) from body(Y, X). */
  case Swap(head: String, body: String)

  /** The head relation. */
  def head: String

  /** The relations the rule names, head first (`rule_relation/2`). */
  def named: Vector[String] = this match
    case Join(head, relations)                 => head +: relations
    case Intersection(head, left, right)       => Vector(head, left, right)
    case ConstantJoin(head, relation, _)       => Vector(head, relation)
    case Swap(head, body)                      => Vector(head, body)

/** A Datalog program: its constants, its facts `relation(first, second)` and
  * its rules (`program(Constants, Facts, Rules)`).
  */
final case class DatalogProgram(
    constants: Vector[String],
    facts: Vector[(String, (String, String))],
    rules: Vector[DatalogRule]
):

  /** The relations of the facts, then of the rules, in the order they first
    * appear (`program_relations/2`).
    */
  def relations: Vector[String] = (facts.map(_._1) ++ rules.flatMap(_.named)).distinct

/** The port of the deleted Prolog file
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_mixin_datalog.pl`; its data are
  * `problems/mixin_datalog`): Datalog in the
  * mixin encoding of `MixinLibrary`. A module has a class per constant (its
  * marker and accept) and per relation (a mixin per fact and per rule whose
  * head it is); a relation's slot of a constant is the row of that constant,
  * a choice of constant classes, so a tuple holds when the second constant's
  * marker is read from the first constant's row. The table of points is
  * read from the file; the programs, a predicate with rules there, are
  * ported here.
  */
final class MixinDatalog(problems: ProblemFamilies, library: MixinLibrary):

  private val file = problems("mixin_datalog")

  private def marker(constant: String): String = s"is_$constant"

  private def datalogModule(constants: Vector[String], relations: Vector[String]): Hierarchy =
    Hierarchy("datalog_module", constants ++ relations)

  private def datalogConstant(constants: Vector[String]): Hierarchy =
    Hierarchy("datalog_constant", constants.map(marker) :+ "accept")

  private def datalogRelation(constants: Vector[String]): Hierarchy = Hierarchy("datalog_relation", constants)

  /** The program a field writes (`program/2`), a constructor of
    * problems/mixin_datalog/program (`MixinDatalog.programKind`).
    */
  def program(name: ProblemField): DatalogProgram = program(MixinDatalog.programKind(name))

  /** The program of the kind: composition, three_way, intersection,
    * constant_join, closure(Shape) and symmetric(Shape).
    */
  def program(kind: MixinDatalog.ProgramKind): DatalogProgram = kind match
    case MixinDatalog.ProgramKind.Composition =>
      DatalogProgram(
        Vector("a", "b", "c"),
        Vector("alpha" -> ("a", "b"), "alpha" -> ("c", "b"), "beta" -> ("b", "a"), "beta" -> ("b", "c")),
        Vector(DatalogRule.Join("composed", Vector("alpha", "beta")))
      )
    case MixinDatalog.ProgramKind.ThreeWay =>
      DatalogProgram(
        Vector("a", "b", "c"),
        Vector(
          "alpha" -> ("a", "b"),
          "alpha" -> ("c", "b"),
          "beta" -> ("b", "a"),
          "beta" -> ("b", "c"),
          "gamma" -> ("a", "b"),
          "gamma" -> ("c", "a")
        ),
        Vector(DatalogRule.Join("chain", Vector("alpha", "beta", "gamma")))
      )
    case MixinDatalog.ProgramKind.Intersection =>
      DatalogProgram(
        Vector("a", "b", "c"),
        Vector("r" -> ("a", "b"), "r" -> ("b", "c"), "s" -> ("a", "b"), "s" -> ("b", "a")),
        Vector(DatalogRule.Intersection("multi", "r", "s"))
      )
    case MixinDatalog.ProgramKind.ConstantJoin =>
      DatalogProgram(
        Vector("a", "b", "c"),
        Vector("edge" -> ("a", "b"), "edge" -> ("b", "c"), "edge" -> ("c", "a")),
        Vector(DatalogRule.ConstantJoin("constant_join", "edge", "b"))
      )
    case MixinDatalog.ProgramKind.Closure(shape) =>
      val (constants, edges) = this.edges(shape)
      DatalogProgram(
        constants,
        edges.map("edge" -> _),
        Vector(DatalogRule.Join("path", Vector("edge")), DatalogRule.Join("path", Vector("edge", "path")))
      )
    case MixinDatalog.ProgramKind.Symmetric(shape) =>
      val (constants, edges) = this.edges(shape)
      DatalogProgram(
        constants,
        edges.map("edge" -> _),
        Vector(
          DatalogRule.Join("sym", Vector("edge")),
          DatalogRule.Swap("sym", "edge"),
          DatalogRule.Join("reach", Vector("sym")),
          DatalogRule.Join("reach", Vector("sym", "reach"))
        )
      )

  /** The constants and edges of a shape (`edges/3`): the cycle and the chain
    * over {a, b, c}, the ring n0 -> ... -> n(size - 1) -> n0 and the same
    * without its closing edge.
    */
  def edges(shape: MixinDatalog.ProgramShape): (Vector[String], Vector[(String, String)]) = shape match
    case MixinDatalog.ProgramShape.AbcCycle => (Vector("a", "b", "c"), Vector("a" -> "b", "b" -> "c", "c" -> "a"))
    case MixinDatalog.ProgramShape.AbcChain => (Vector("a", "b", "c"), Vector("a" -> "b", "b" -> "c"))
    case MixinDatalog.ProgramShape.Ring(count) =>
      (numbered(count), (0 until count).toVector.map(index => s"n$index" -> s"n${(index + 1) % count}"))
    case MixinDatalog.ProgramShape.Line(count) =>
      (numbered(count), (0 to count - 2).toVector.map(index => s"n$index" -> s"n${index + 1}"))

  private def numbered(count: Int): Vector[String] = (0 until count).toVector.map(index => s"n$index")

  /** `Relation.First.is_Second` of the program's module
    * (`datalog_surface/5`).
    */
  def datalogSurface(program: DatalogProgram, relation: String, first: String, second: String): Term =
    val constants = program.constants
    val relations = program.relations
    library.withMixinLibrary(
      Vector.empty,
      _ =>
        val module = choice(
          (constants.map(constantModuleMixin(constants, relations, _)) ++
            relations.map(relationModuleMixin(program, relations, _)))*
        )
        val relationClass = library.readSlot(datalogModule(constants, relations), relation, module)
        val row = library.readSlot(datalogRelation(constants), first, relationClass)
        library.readSlot(datalogConstant(constants), marker(second), row)
    )

  /** The module's mixin of the constant's class: its marker and accept
    * (`constant_module_mixin/4`).
    */
  private def constantModuleMixin(constants: Vector[String], relations: Vector[String], constant: String): Term =
    library.selfMixin(datalogModule(constants, relations), constant, _ =>
      choice(
        library.valueMixin(datalogConstant(constants), marker(constant) -> library.trueTerm),
        library.valueMixin(
          datalogConstant(constants),
          "accept" -> λ(relationClass => library.readSlot(datalogRelation(constants), constant, relationClass))
        )
      )
    )

  /** The constants, the relations and the module's self that the mixins of
    * a relation's class read through.
    */
  private final case class Context(constants: Vector[String], relations: Vector[String], module: Term):

    /** The module's slot of the name, a constant's or a relation's class
      * (`module_class/3`).
      */
    def moduleClass(name: String): Term = library.readSlot(datalogModule(constants, relations), name, module)

    /** relation.constant (`row/4`). */
    def row(relation: String, constant: String): Term =
      library.readSlot(datalogRelation(constants), constant, moduleClass(relation))

    /** `set.is_constant then []`, then once for each occurrence of the
      * constant in the set (`guard/5`). The failure is top (`Term.top`), as the
      * unhandled slots of `MixinLibrary.readHandled` are (its FIXME). https://github.com/Atry/private-overlay/issues/1990
      */
    def guard(constant: String, set: Term, guarded: Term): Term =
      library.slotApplied(datalogConstant(constants), marker(constant), set, guarded, Term.top)

    /** `set.accept relation`, the choice of the rows of the set's constants
      * (`accepted/4`).
      */
    def accepted(set: Term, relation: String): Term =
      library.slotApplied(datalogConstant(constants), "accept", set, moduleClass(relation))

  /** The module's mixin of the relation's class: the mixins of its facts,
    * then of the rules whose head it is (`relation_module_mixin/4`).
    */
  private def relationModuleMixin(program: DatalogProgram, relations: Vector[String], relation: String): Term =
    val constants = program.constants
    library.selfMixin(datalogModule(constants, relations), relation, module =>
      val context = Context(constants, relations, module)
      val factMixins = program.facts.collect { case (`relation`, (first, second)) =>
        library.valueMixin(datalogRelation(constants), first -> context.moduleClass(second))
      }
      val ruleMixins = program.rules.filter(_.head == relation).map(rule =>
        library.valueMixin(datalogRelation(constants), constants.map(constant => constant -> ruleRow(context, rule, constant))*)
      )
      choice((factMixins ++ ruleMixins)*)
    )

  /** The rule's row of the constant (`rule_row/4`). */
  private def ruleRow(context: Context, rule: DatalogRule, constant: String): Term = rule match
    case DatalogRule.Join(_, relations) =>
      relations.tail.foldLeft(context.row(relations.head, constant))((set, relation) => context.accepted(set, relation))
    case DatalogRule.Intersection(_, left, right) =>
      choice(context.constants.map(candidate =>
        val inRight = context.guard(candidate, context.row(right, constant), context.moduleClass(candidate))
        context.guard(candidate, context.row(left, constant), inRight)
      )*)
    case DatalogRule.ConstantJoin(_, relation, middle) =>
      val reached = context.accepted(context.row(relation, constant), relation)
      context.guard(middle, reached, context.row(relation, middle))
    case DatalogRule.Swap(_, body) =>
      choice(context.constants.map(candidate =>
        context.guard(constant, context.row(body, candidate), context.moduleClass(candidate))
      )*)

  /** Whether `relation(first, second)` is in the program's least fixed
    * point, by naive iteration (`reference_holds/4`).
    */
  def referenceHolds(program: DatalogProgram, relation: String, first: String, second: String): Boolean =
    type Tuple = (String, (String, String))
    def derived(rule: DatalogRule, tuples: Set[Tuple]): Set[Tuple] =
      def of(relation: String): Set[(String, String)] = tuples.collect { case (`relation`, pair) => pair }
      rule match
        case DatalogRule.Join(head, relations) =>
          relations.tail
            .foldLeft(of(relations.head))((pairs, next) =>
              for
                (x, y) <- pairs
                (middle, z) <- of(next)
                if middle == y
              yield (x, z)
            )
            .map(head -> _)
        case DatalogRule.Intersection(head, left, right) => (of(left) intersect of(right)).map(head -> _)
        case DatalogRule.ConstantJoin(head, relation, middle) =>
          for
            (x, y) <- of(relation)
            if of(relation).contains((y, middle))
            (from, w) <- of(relation)
            if from == middle
          yield head -> (x, w)
        case DatalogRule.Swap(head, body) => of(body).map(pair => head -> pair.swap)
    @tailrec
    def fixedPoint(tuples: Set[Tuple]): Set[Tuple] =
      val next = tuples ++ program.rules.flatMap(derived(_, tuples))
      if next == tuples then tuples else fixedPoint(next)
    fixedPoint(program.facts.toSet).contains(relation -> (first, second))

  /** The points, each with its program (the field, a constructor of
    * problems/mixin_datalog/program, read by `program`), the queried tuple
    * and the derivation its claim cites (`datalog_point/6`).
    */
  val points: Vector[(String, ProblemField, String, String, String, String)] =
    file.rows("datalog_point").map(arguments =>
      (
        ProblemData.text(arguments(0)),
        arguments(1),
        ProblemData.text(arguments(2)),
        ProblemData.text(arguments(3)),
        ProblemData.text(arguments(4)),
        ProblemData.text(arguments(5))
      )
    )

  /** The point's program, after the reference has found its tuple in the
    * least fixed point (`point_term/2`). Throws when it has not.
    */
  def pointTerm(name: String): Term =
    points.find(_._1 == name) match
      case Some((_, programName, relation, first, second, _)) =>
        val datalog = program(programName)
        if !referenceHolds(datalog, relation, first, second) then
          throw IllegalStateException(s"$relation($first, $second) of $name is not derived")
        datalogSurface(datalog, relation, first, second)
      case None => throw IllegalArgumentException(s"$name is no point of contest_mixin_datalog")

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((name, _, _, _, _, derivation) =>
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"$derivation; each rule application chooses one element of a union and each join dispatches a chosen constant to its row, a finite sequence of choices that reaches the second constant's marker in the first constant's row of the relation, the Church true, so the test yields \\\\a. a"
      )
    )

object MixinDatalog:

  /** The kind of a point's program, the constructors of
    * problems/mixin_datalog/program in order: composition, the three-way
    * join, the intersection, the constant join, then the transitive closure
    * and the symmetric transitive closure of the edges of a shape.
    * `written` is the program's name in the tests' names of their cases,
    * `closure(ring(6))` for instance, the text the data wrote before its
    * options became Scott data; it is not a key
    * of the data.
    */
  enum ProgramKind:
    case Composition
    case ThreeWay
    case Intersection
    case ConstantJoin
    case Closure(shape: ProgramShape)
    case Symmetric(shape: ProgramShape)

    def written: String = this match
      case Composition      => "composition"
      case ThreeWay         => "three_way"
      case Intersection     => "intersection"
      case ConstantJoin     => "constant_join"
      case Closure(shape)   => s"closure(${shape.written})"
      case Symmetric(shape) => s"symmetric(${shape.written})"

  /** The shape of the edges of a closure, the constructors of
    * problems/mixin_datalog/shape in order: the cycle and the chain over a,
    * b and c, then the ring and the line of a size. `written` is the
    * shape's name as `ProgramKind.written` prints it.
    */
  enum ProgramShape:
    case AbcCycle
    case AbcChain
    case Ring(size: Int)
    case Line(size: Int)

    def written: String = this match
      case AbcCycle   => "abc_cycle"
      case AbcChain   => "abc_chain"
      case Ring(size) => s"ring($size)"
      case Line(size) => s"line($size)"

  /** The number of constructors of problems/mixin_datalog/program, the
    * cases of `ProgramKind`.
    */
  val programKindCount: Int = ProblemData.caseCount[ProgramKind]

  /** The number of constructors of problems/mixin_datalog/shape, the cases
    * of `ProgramShape`.
    */
  val programShapeCount: Int = ProblemData.caseCount[ProgramShape]

  /** The kind a field writes, a constructor of
    * problems/mixin_datalog/program read by its position
    * (`ProblemData.alternative`), closure's and symmetric's field its shape.
    */
  def programKind(field: ProblemField): ProgramKind = ProblemData.alternative(field, programKindCount) match
    case (0, Vector())      => ProgramKind.Composition
    case (1, Vector())      => ProgramKind.ThreeWay
    case (2, Vector())      => ProgramKind.Intersection
    case (3, Vector())      => ProgramKind.ConstantJoin
    case (4, Vector(shape)) => ProgramKind.Closure(programShape(shape))
    case (5, Vector(shape)) => ProgramKind.Symmetric(programShape(shape))
    case (position, fields) =>
      throw IllegalArgumentException(s"the program of contest_mixin_datalog at position $position has ${fields.size} fields")

  /** The shape a field writes, a constructor of problems/mixin_datalog/shape
    * read by its position (`ProblemData.alternative`), ring's and line's
    * field its size.
    */
  def programShape(field: ProblemField): ProgramShape = ProblemData.alternative(field, programShapeCount) match
    case (0, Vector())     => ProgramShape.AbcCycle
    case (1, Vector())     => ProgramShape.AbcChain
    case (2, Vector(size)) => ProgramShape.Ring(ProblemData.small(size))
    case (3, Vector(size)) => ProgramShape.Line(ProblemData.small(size))
    case (position, fields) =>
      throw IllegalArgumentException(s"the shape of contest_mixin_datalog at position $position has ${fields.size} fields")
