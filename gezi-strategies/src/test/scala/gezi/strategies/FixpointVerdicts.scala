package gezi.strategies

import gezi.egraph.EGraph
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import scala.annotation.tailrec
import gezi.ir.{Apply, NoinlineLeaf}

/** A type of HM's verdict: a type variable (read as a constant of its own,
  * one for each name), the naturals, the booleans, a list, a function type.
  */
enum ExpectedType:
  case Variable(name: String)
  case NaturalType
  case BooleanType
  case ListType(element: ExpectedType)
  case Arrow(domain: ExpectedType, range: ExpectedType)

/** What HM over structures says of a program (`coverage_program/3`): it
  * types it and the root is judged the type; the root is judged a structure
  * and none is the type; it types it and the root is judged some monotype;
  * it rejects it.
  */
enum Verdict:
  case Typed(expected: ExpectedType)
  case TypedButNot(expected: ExpectedType)
  case TypedSome
  case Untyped

/** A rational tree as a finite graph: each node a variable or a functor over
  * other nodes, a Prolog list a chain of `[|]` nodes ending in `[]`.
  */
enum TreeNode:
  case Unbound
  case Functor(name: String, children: Vector[Int])

/** A rational tree: its nodes and its root. */
final case class RationalTree(nodes: Vector[TreeNode], root: Int):

  /** The root is a structure or a function type (`judged_structure/1`). */
  def judgedStructure: Boolean = nodes(root) match
    case TreeNode.Functor("structure", Vector(_)) | TreeNode.Functor("arrow", Vector(_, _)) => true
    case _                                                                                  => false

/** The types a root is judged: the clash of the run, HM's failed
  * unification, or the types of the zero universe its judgments hold.
  */
enum JudgedTypes:
  case Clash
  case Judged(types: Vector[RationalTree])

/** The test helper of `gezi/tests/fixpoint_verdicts.pl`, whose module
  * documentation (A JUDGMENT, A CLASH, A VERDICT) this follows: the
  * judgments of the baseline's e-graph read as types, and HM's verdicts. It
  * reads the classes of a finished run and decides nothing in the pipeline:
  * no module under `strategies/src/main` reads it, the types it reads are
  * read off the classes and never recorded in them, and HM's verdicts are
  * written by hand in `coverage`. It reads the zero universe of the knowledge
  * module hindley_milner_unions only, the one the HM baseline's tests run;
  * `type_read/4`, the Prolog helper's reading under other knowledge modules,
  * was used only by the probe
  * `benchmarks/classic_hindley_milner/fixpoint_egraph_probe.pl`, deleted in
  * d32e69ff0, and is not ported.
  *
  * The rational trees of the Prolog helper are cyclic Prolog terms unified by
  * SWI-Prolog; here a tree is a graph and two trees unify by the unification
  * of rational trees on a union of their nodes (`unify`).
  */
object FixpointVerdicts:

  // TODO: judgedTypes stood here. Its purpose: run a HOAS program through the front end and the baseline's e-graph,
  // and read the types the root is judged off the finished run's classes (`judged_types/5`), by `ZeroUniverse`.
  // It named library terms by StrategyTesting.programInput and LibraryFiles.programNames, a free variable
  // (blacklisted) and a table of library files deleted when the library became files reached by paths. Its replacement takes its programs over the library terms of fixture files read by projection.
  // The deleted code: git show 2908bffd5:lambda_jit/strategies/src/test/scala/lambdajit/strategies/FixpointVerdicts.scala.

  /** The instructions of the zero universe's heads, read by projection off
    * the fixture `TermTables.zeroUniverseTerms`.
    */
  lazy val zeroUniverseHeads: Map[String, Instruction] =
    StandardLibrary.entryMembers(LibraryFiles.buildRoot, TermTables.zeroUniverseTerms, Expansions.none)._1

  /** The reading of the zero universe's types off a finished run's graph,
    * its heads recognized by their instructions (`zeroUniverseHeads`).
    */
  final case class ZeroUniverse(graph: EGraph):

    private def instruction(name: String): Instruction =
      zeroUniverseHeads.getOrElse(name, throw IllegalArgumentException(s"${TermTables.zeroUniverseTerms.file} has no member $name"))

    /** The heads of the zero universe and the arguments each takes, the
      * instrument's own reading (`zero_arity/2`).
      */
    private val arities: Map[String, Int] = Map(
      "no_alternative" -> 0,
      "no_field" -> 0,
      "structure" -> 1,
      "function_type" -> 2,
      "alternative" -> 2,
      "field" -> 2
    )

    private def members(node: Int): Vector[Layer[Int]] = graph.classMembers(node).map(_.layer)

    /** The class holds the library term as a leaf (`head_named/3`). */
    private def headNamed(node: Int, name: String): Boolean =
      val named = instruction(name)
      members(node).exists {
        case NoinlineLeaf(found) => found == named
        case _                 => false
      }

    /** Every way the class holds a term of the head over classes
      * (`zero_head/4`), in the order of the members.
      */
    def zeroHeads(node: Int, head: String): Vector[Vector[Int]] = arities(head) match
      case 0 => if headNamed(node, head) then Vector(Vector()) else Vector()
      case 1 =>
        members(node).collect { case Apply(function, argument) if headNamed(function, head) => Vector(argument) }
      case _ =>
        members(node).collect { case Apply(partial, second) => (partial, second) }.flatMap { (partial, second) =>
          members(partial).collect {
            case Apply(function, first) if headNamed(function, head) => Vector(first, second)
          }
        }

    /** The groups of heads no class of a typed program holds two of
      * (`clash_group/1`).
      */
    private val clashGroups: Vector[Vector[String]] =
      Vector(Vector("structure", "function_type"), Vector("alternative", "no_alternative"), Vector("field", "no_field"))

    private lazy val roots: Vector[Int] = (0 until graph.nodeCount).toVector.filter(node => graph.root(node) == node)

    /** The run holds a clash: a class holds two heads of one group, or a
      * function type holds itself through function types alone, HM's occurs
      * check (`clash/2`).
      */
    def clash: Boolean =
      roots.exists(root => clashGroups.exists(group => group.count(zeroHeads(root, _).nonEmpty) >= 2)) ||
        roots.exists(root => zeroHeads(root, "function_type").nonEmpty && functionReaches(root))

    /** The domain or the range of a function type the class holds, or of a
      * function type one of them holds in turn, is the class
      * (`function_reaches/4`, read as reachability).
      */
    private def functionReaches(target: Int): Boolean =
      def parts(node: Int): Vector[Int] = zeroHeads(node, "function_type").flatten.map(graph.root)
      @tailrec
      def searched(frontier: List[Int], visited: Set[Int]): Boolean = frontier match
        case Nil => false
        case node :: rest =>
          val next = parts(node)
          if next.contains(target) then true
          else
            val fresh = next.filterNot(visited.contains).distinct
            searched(fresh.toList ++ rest, visited ++ fresh)
      searched(List(target), Set.empty)

  /** The rational tree of the zero universe a type of HM's verdict names,
    * the instrument's own reading of the library's data types by their
    * structures (`expected_tree/2`).
    */
  def expectedTree(expected: ExpectedType): RationalTree =
    final case class Building(nodes: Vector[TreeNode]):
      def added(node: TreeNode): (Building, Int) = (Building(nodes :+ node), nodes.size)
      def set(index: Int, node: TreeNode): Building = Building(nodes.updated(index, node))
    def list(building: Building, elements: Vector[Int]): (Building, Int) =
      elements.foldRight(building.added(TreeNode.Functor("[]", Vector()))) { case (element, (current, tail)) =>
        current.added(TreeNode.Functor("[|]", Vector(element, tail)))
      }
    def built(building: Building, expectedType: ExpectedType): (Building, Int) = expectedType match
      case ExpectedType.Variable(name) => building.added(TreeNode.Functor(s"skolem($name)", Vector()))
      case ExpectedType.BooleanType =>
        val (withFirst, first) = list(building, Vector())
        val (withSecond, second) = list(withFirst, Vector())
        val (withAlternatives, alternatives) = list(withSecond, Vector(first, second))
        withAlternatives.added(TreeNode.Functor("structure", Vector(alternatives)))
      case ExpectedType.NaturalType =>
        val (started, natural) = building.added(TreeNode.Unbound)
        val (withFirst, first) = list(started, Vector())
        val (withSecond, second) = list(withFirst, Vector(natural))
        val (withAlternatives, alternatives) = list(withSecond, Vector(first, second))
        (withAlternatives.set(natural, TreeNode.Functor("structure", Vector(alternatives))), natural)
      case ExpectedType.ListType(element) =>
        val (withElement, elementNode) = built(building, element)
        val (started, listNode) = withElement.added(TreeNode.Unbound)
        val (withFirst, first) = list(started, Vector())
        val (withSecond, second) = list(withFirst, Vector(elementNode, listNode))
        val (withAlternatives, alternatives) = list(withSecond, Vector(first, second))
        (withAlternatives.set(listNode, TreeNode.Functor("structure", Vector(alternatives))), listNode)
      case ExpectedType.Arrow(domain, range) =>
        val (withDomain, domainNode) = built(building, domain)
        val (withRange, rangeNode) = built(withDomain, range)
        withRange.added(TreeNode.Functor("arrow", Vector(domainNode, rangeNode)))
    val (building, root) = built(Building(Vector.empty), expected)
    RationalTree(building.nodes, root)

  /** The two rational trees unify, as Prolog unifies two cyclic terms
    * (`\+ \+ Judged = Tree`): their nodes put in one space, a union-find over
    * it, a variable joined to anything, two functors joined when their names
    * and arities agree and then their children unified, a pair already
    * joined not unified again.
    */
  def unify(left: RationalTree, right: RationalTree): Boolean =
    val offset = left.nodes.size
    val nodes = left.nodes ++ right.nodes.map {
      case TreeNode.Functor(name, children) => TreeNode.Functor(name, children.map(_ + offset))
      case TreeNode.Unbound                 => TreeNode.Unbound
    }
    @tailrec
    def find(parents: Map[Int, Int], node: Int): Int = parents.get(node) match
      case Some(parent) => find(parents, parent)
      case None         => node
    @tailrec
    def unified(pending: List[(Int, Int)], parents: Map[Int, Int]): Boolean = pending match
      case Nil => true
      case (first, second) :: rest =>
        val firstRoot = find(parents, first)
        val secondRoot = find(parents, second)
        if firstRoot == secondRoot then unified(rest, parents)
        else
          (nodes(firstRoot), nodes(secondRoot)) match
            case (TreeNode.Unbound, _) => unified(rest, parents.updated(firstRoot, secondRoot))
            case (_, TreeNode.Unbound) => unified(rest, parents.updated(secondRoot, firstRoot))
            case (TreeNode.Functor(firstName, firstChildren), TreeNode.Functor(secondName, secondChildren)) =>
              if firstName != secondName || firstChildren.size != secondChildren.size then false
              else unified(firstChildren.zip(secondChildren).toList ++ rest, parents.updated(firstRoot, secondRoot))
    unified(List((left.root, right.root + offset)), Map.empty)

  /** The judged types agree with what HM says of the program (`verdict/3`). */
  def agrees(verdict: Verdict, judged: JudgedTypes): Boolean =
    val structures = judged match
      case JudgedTypes.Clash         => Vector.empty
      case JudgedTypes.Judged(types) => types.filter(_.judgedStructure)
    verdict match
      case Verdict.Typed(expected) =>
        val tree = expectedTree(expected)
        structures.exists(unify(_, tree))
      case Verdict.TypedButNot(expected) =>
        val tree = expectedTree(expected)
        structures.nonEmpty && !structures.exists(unify(_, tree))
      case Verdict.TypedSome => structures.nonEmpty
      case Verdict.Untyped   => structures.isEmpty
