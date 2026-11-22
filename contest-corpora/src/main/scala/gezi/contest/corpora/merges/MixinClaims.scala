package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.contest.corpora.reductions.DynamicReferences
import gezi.contest.corpora.reductions.Encodings
import gezi.frontend.Term
import gezi.frontend.Term.*

/** A graph of the mixin family, by the name `graph/4` of the former
  * `contest_mixin_claims` module (`problems/mixin_claims`) knows it under.
  */
enum MixinGraphName:

  /** The ring n0 -> n1 -> ... -> n(size - 1) -> n0. */
  case Ring(size: Int)

  /** The graph with one more node z, which no edge enters. */
  case Isolated(graph: MixinGraphName)

  /** The graph of the edges over the nodes, for points written elsewhere. */
  case Explicit(edges: Vector[(String, String)], nodes: Vector[String])

  /** a -> b, b -> a, b -> c, reachable's choice direct first. */
  case DirectFirst

  /** a -> b, a -> c, b -> d, c -> d. */
  case Diamond

  /** Two rings of six joined by n3 -> m0. */
  case TwoRings

  /** A ring of ten with the chord n5 -> n2. */
  case ChordRing

  /** The tail t0 -> t1 -> t2 into a ring of eight. */
  case Lasso

  /** A ring of twelve, each node also pointing two ahead. */
  case DoubleSuccessorRing

/** A query of the mixin graphs: `reaches(From, To)`, `From.reachable.is_To`,
  * or `two_hop(From, To)`, `From.two_hop.is_To`.
  */
final case class MixinQuery(slot: String, from: String, to: String):

  /** The query as the claims write it, the text of the Prolog term
    * `reaches(From, To)` or `two_hop(From, To)` as `~q` wrote it.
    */
  def written: String = s"${if slot == "reachable" then "reaches" else slot}($from,$to)"

/** The port of the deleted Prolog file
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_mixin_claims.pl`; its data are
  * `problems/mixin_claims`): scored searches
  * in the mixin encoding of `MixinLibrary`: reachability over a module of
  * node classes, subset sum over a module of search levels on the binary
  * library, and the longest common subsequence over a module of strings on
  * the natural library. The tables of the subset and the common subsequence
  * points are read from the family's directory,
  * `gezi/problems/mixin_claims`; the graphs, their points and the
  * hierarchies, predicates with rules in the file, are ported here.
  */
final class MixinClaims(problems: ProblemFamilies, library: MixinLibrary):

  private val file = problems("mixin_claims")

  // ---- reachability ----

  /** One slot per node (`hierarchy(graph_module(Nodes), Nodes)`). */
  private def graphModule(nodes: Vector[String]): Hierarchy = Hierarchy("graph_module", nodes)

  /** One marker slot per node, then reachable, next and two_hop. */
  private def graphNode(nodes: Vector[String]): Hierarchy =
    Hierarchy("graph_node", nodes.map(marker) ++ Vector("reachable", "next", "two_hop"))

  private def marker(node: String): String = s"is_$node"

  /** The graph's edges in their order, its nodes and the order of
    * reachable's choice, `recursive_first` or `direct_first` (`graph/4`).
    */
  def graph(name: MixinGraphName): (Vector[(String, String)], Vector[String], String) = name match
    case MixinGraphName.Ring(size) =>
      val (edges, nodes) = MixinClaims.ringEdges("n", size)
      (edges, nodes, "recursive_first")
    case MixinGraphName.Isolated(inner) =>
      val (edges, nodes, order) = graph(inner)
      (edges, nodes :+ "z", order)
    case MixinGraphName.Explicit(edges, nodes) => (edges, nodes, "recursive_first")
    case MixinGraphName.DirectFirst =>
      (Vector("a" -> "b", "b" -> "a", "b" -> "c"), Vector("a", "b", "c"), "direct_first")
    case MixinGraphName.Diamond =>
      (Vector("a" -> "b", "a" -> "c", "b" -> "d", "c" -> "d"), Vector("a", "b", "c", "d"), "recursive_first")
    case MixinGraphName.TwoRings =>
      val (first, firstNodes) = MixinClaims.ringEdges("n", 6)
      val (second, secondNodes) = MixinClaims.ringEdges("m", 6)
      (first ++ second :+ ("n3" -> "m0"), firstNodes ++ secondNodes, "recursive_first")
    case MixinGraphName.ChordRing =>
      val (ring, nodes) = MixinClaims.ringEdges("n", 10)
      (ring :+ ("n5" -> "n2"), nodes, "recursive_first")
    case MixinGraphName.Lasso =>
      val (ring, ringNodes) = MixinClaims.ringEdges("r", 8)
      (Vector("t0" -> "t1", "t1" -> "t2", "t2" -> "r0") ++ ring, Vector("t0", "t1", "t2") ++ ringNodes, "recursive_first")
    case MixinGraphName.DoubleSuccessorRing =>
      val (ring, nodes) = MixinClaims.ringEdges("n", 12)
      (ring ++ (0 until 12).map(index => s"n$index" -> s"n${(index + 2) % 12}"), nodes, "recursive_first")

  /** The program of the query over the graph's module (`graph_surface/3`).
    * reachable takes a step budget, applied here: the node count as a
    * Scott unary numeral, enough for every path of the graph
    * (`reductions.Encodings.unary`).
    */
  def graphSurface(name: MixinGraphName, query: MixinQuery): Term =
    val (edges, nodes, order) = graph(name)
    library.withMixinLibrary(
      Vector.empty,
      _ =>
        val module = choice(nodes.map(node => nodeModuleMixin(edges, nodes, order, node))*)
        val fromClass = library.readSlot(graphModule(nodes), query.from, module)
        val slot = library.readSlot(graphNode(nodes), query.slot, fromClass)
        val reached = if query.slot == "reachable" then slot(Encodings.unary(nodes.length)) else slot
        library.readSlot(graphNode(nodes), marker(query.to), reached)
    )

  /** The module's mixin that implements the node's class, over the module's
    * self (`node_module_mixin/5`).
    */
  private def nodeModuleMixin(edges: Vector[(String, String)], nodes: Vector[String], order: String, node: String): Term =
    library.selfMixin(graphModule(nodes), node, module => nodeClass(edges, nodes, order, module, node))

  /** The mixins of the marker, of reachable, of next and of two_hop
    * (`node_class/6`). reachable is `\budget. budget top (\p. [the
    * successors' classes, each successor's reachable p])`: a budget of a
    * unary numeral that each step takes the predecessor of, top once it is
    * spent. Without the budget a walk round a cycle reads ⊥ in DdLP96's
    * reading (a choice is a meet, the recursion a least fixed point), and
    * every closed βη normal form, both Booleans included, would be an
    * answer of a query on a graph with a cycle, so no miss trap could hold
    * (FIXME: the claim families' answers rest on this budget,
    * https://github.com/Atry/private-overlay/issues/1989). With it the
    * recursion terminates and the selection theorem applies.
    */
  private def nodeClass(edges: Vector[(String, String)], nodes: Vector[String], order: String, module: Term, node: String): Term =
    val hierarchy = graphNode(nodes)
    val nexts = edges.collect { case (from, to) if from == node => to }
    val direct = nexts.map(successorClass(nodes, module, _))
    val reachable = λ(budget =>
      budget(Term.top)(λ(predecessor =>
        val recursive =
          nexts.map(next => library.readSlot(hierarchy, "reachable", successorClass(nodes, module, next))(predecessor))
        choice((if order == "recursive_first" then recursive ++ direct else direct ++ recursive)*)
      ))
    )
    choice(
      library.valueMixin(hierarchy, marker(node) -> library.trueTerm),
      library.valueMixin(hierarchy, "reachable" -> reachable),
      library.valueMixin(hierarchy, "next" -> choice(nexts.map(successorClass(nodes, module, _))*)),
      library.selfMixin(hierarchy, "two_hop", self =>
        library.readSlot(hierarchy, "next", library.readSlot(hierarchy, "next", self))
      )
    )

  private def successorClass(nodes: Vector[String], module: Term, next: String): Term =
    library.readSlot(graphModule(nodes), next, module)

  /** The graph points, each with its graph, its query and the path of its
    * finite head (`graph_point/4`).
    */
  val graphPoints: Vector[(String, MixinGraphName, MixinQuery, Vector[String])] = Vector(
    ("mixin_ring_three_reaches", MixinGraphName.Ring(3), MixinQuery("reachable", "n0", "n2"), Vector("n0", "n1", "n2")),
    ("mixin_ring_twenty_reaches", MixinGraphName.Ring(20), MixinQuery("reachable", "n0", "n19"), MixinClaims.ringPath(20)),
    ("mixin_ring_forty_reaches", MixinGraphName.Ring(40), MixinQuery("reachable", "n0", "n39"), MixinClaims.ringPath(40)),
    ("mixin_direct_first_reaches", MixinGraphName.DirectFirst, MixinQuery("reachable", "a", "c"), Vector("a", "b", "c")),
    ("mixin_diamond_two_hop", MixinGraphName.Diamond, MixinQuery("two_hop", "a", "d"), Vector("a", "b", "d")),
    (
      "mixin_two_rings_reach",
      MixinGraphName.TwoRings,
      MixinQuery("reachable", "n0", "m5"),
      Vector("n0", "n1", "n2", "n3", "m0", "m1", "m2", "m3", "m4", "m5")
    ),
    ("mixin_chord_ring_reach", MixinGraphName.ChordRing, MixinQuery("reachable", "n0", "n9"), (0 to 9).toVector.map(index => s"n$index")),
    (
      "mixin_lasso_reach",
      MixinGraphName.Lasso,
      MixinQuery("reachable", "t0", "r7"),
      Vector("t0", "t1", "t2") ++ (0 to 7).map(index => s"r$index")
    ),
    (
      "mixin_double_successor_ring_reach",
      MixinGraphName.DoubleSuccessorRing,
      MixinQuery("reachable", "n0", "n11"),
      Vector("n0", "n2", "n4", "n6", "n8", "n10", "n11")
    )
  )

  // ---- subset sum ----

  /** One slot per level, search_0 to search_count. */
  private def searchModule(count: Int): Hierarchy = Hierarchy("search_module", (0 to count).toVector.map(level => s"search_$level"))

  /** accumulated and found. */
  private val search: Hierarchy = Hierarchy("search", Vector("accumulated", "found"))

  /** `{search_0, accumulated : 0}.found`, read at church, over the module of
    * the levels and the binary library (`subset_surface/3`).
    */
  def subsetSurface(items: Vector[BigInt], target: BigInt): Term =
    val count = items.length
    library.withMixinLibrary(
      Vector("binary"),
      names =>
        val module = choice((0 to count).map(level => searchModuleMixin(names, items, target, level))*)
        val first = library.readSlot(searchModule(count), "search_0", module)
        val found = searchFound(first, library.binaryInstance(names, 0))
        library.readSlot(library.boolean, "church", found)
    )

  /** `{class, accumulated : accumulated}.found` (`search_found/3`). */
  private def searchFound(classTerm: Term, accumulated: Term): Term =
    library.readSlot(search, "found", choice(classTerm, library.valueMixin(search, "accumulated" -> accumulated)))

  /** The module's mixin that implements search_level (`search_module_mixin/5`). */
  private def searchModuleMixin(names: LibraryNames, items: Vector[BigInt], target: BigInt, level: Int): Term =
    library.selfMixin(searchModule(items.length), s"search_$level", module =>
      choice(searchNodeMixin(names, items, target, module, level))
    )

  /** The last level compares its accumulated sum with the target; every
    * other level chooses leaving its item out or taking it
    * (`search_node_mixin/7`).
    */
  private def searchNodeMixin(names: LibraryNames, items: Vector[BigInt], target: BigInt, module: Term, level: Int): Term =
    val count = items.length
    if level == count then
      library.selfMixin(search, "found", self =>
        library.slotApplied(library.binary, "equality", library.binaryInstance(names, target), library.readSlot(search, "accumulated", self))
      )
    else
      val nextName = s"search_${level + 1}"
      library.selfMixin(search, "found", self =>
        val leaveOut = searchFound(library.readSlot(searchModule(count), nextName, module), library.readSlot(search, "accumulated", self))
        val taken = library.slotApplied(
          library.binary,
          "plus",
          library.readSlot(search, "accumulated", self),
          library.binaryInstance(names, items(level))
        )
        val take = searchFound(library.readSlot(searchModule(count), nextName, module), taken)
        choice(leaveOut, take)
      )

  /** The subset points, each with its count of the first odd primes
    * (`subset_point/2`).
    */
  val subsetPoints: Vector[(String, Int)] =
    file.rows("subset_point").map(arguments => (ProblemData.text(arguments(0)), ProblemData.small(arguments(1))))

  // ---- longest common subsequence ----

  private val stringsModule = Hierarchy("strings_module", Vector("a", "b", "nil", "cons", "common_subsequence"))
  private val symbol = Hierarchy("symbol", Vector("accept"))
  private val list = Hierarchy("list", Vector("accept", "head", "tail"))
  private val commonSubsequence = Hierarchy("common_subsequence", Vector("left", "right", "need", "found"))

  /** `{common_subsequence, left : Left, right : Right, need : Need}.found`,
    * read at church; the Booleans and the unary need the natural library's,
    * the strings module let bound once (`common_subsequence_surface/4`).
    */
  def commonSubsequenceSurface(left: Vector[Char], right: Vector[Char], need: Int): Term =
    library.withMixinLibrary(
      Vector("natural"),
      names =>
        λ(module =>
          val found = commonSubsequenceFound(
            module,
            stringObject(module, left),
            stringObject(module, right),
            library.naturalInstance(names, need)
          )
          library.readSlot(library.boolean, "church", found)
        )(stringsModuleTerm(names))
    )

  /** The symbols' and lists' classes and common_subsequence
    * (`strings_module/2`).
    */
  private def stringsModuleTerm(names: LibraryNames): Term =
    choice(
      library.valueMixin(
        stringsModule,
        "a" -> choice(library.valueMixin(symbol, "accept" -> λ(onA => λ(_ => onA)))),
        "b" -> choice(library.valueMixin(symbol, "accept" -> λ(_ => λ(onB => onB)))),
        "nil" -> choice(library.valueMixin(list, "accept" -> λ(onNil => λ(_ => onNil)))),
        "cons" -> choice(library.valueMixin(list, "accept" -> λ(_ => λ(onCons => onCons))))
      ),
      library.selfMixin(stringsModule, "common_subsequence", module => choice(commonSubsequenceMixin(names, module)))
    )

  private def stringObject(module: Term, symbols: Vector[Char]): Term =
    symbols.foldRight(library.readSlot(stringsModule, "nil", module))((head, tail) =>
      choice(
        library.readSlot(stringsModule, "cons", module),
        library.valueMixin(list, "head" -> library.readSlot(stringsModule, head.toString, module), "tail" -> tail)
      )
    )

  /** `{common_subsequence, left : Left, right : Right, need : Need}.found`,
    * the class read from the module (`common_subsequence_found/5`).
    */
  private def commonSubsequenceFound(module: Term, left: Term, right: Term, need: Term): Term =
    library.readSlot(
      commonSubsequence,
      "found",
      choice(
        library.readSlot(stringsModule, "common_subsequence", module),
        library.valueMixin(commonSubsequence, "left" -> left, "right" -> right, "need" -> need)
      )
    )

  /** found over self's left, right and need, each read anew from self where
    * it is used (`common_subsequence_mixin/3`).
    */
  private def commonSubsequenceMixin(names: LibraryNames, module: Term): Term =
    library.selfMixin(commonSubsequence, "found", self =>
      def read(slot: String): Term = library.readSlot(commonSubsequence, slot, self)
      def falseClass: Term = library.libraryClass(names, "natural", "false")
      val leaveLeft = commonSubsequenceFound(module, listFieldRead(self, "left", "tail"), read("right"), read("need"))
      val leaveRight = commonSubsequenceFound(module, read("left"), listFieldRead(self, "right", "tail"), read("need"))
      val headsCompared = library.slotApplied(
        symbol,
        "accept",
        listFieldRead(self, "left", "head"),
        headMatch(names, module, self, 'a'),
        headMatch(names, module, self, 'b')
      )
      val found = choice(leaveLeft, leaveRight, headsCompared)
      val onRight = library.slotApplied(list, "accept", read("right"), falseClass, found)
      val onLeft = library.slotApplied(list, "accept", read("left"), falseClass, onRight)
      library.slotApplied(library.natural, "accept", read("need"), library.libraryClass(names, "natural", "true"), λ(_ => onLeft))
    )

  /** Left's head is the symbol: right's head is the symbol too, and both
    * tails are left out with need - 1, or it is not, false (`head_match/5`).
    */
  private def headMatch(names: LibraryNames, module: Term, self: Term, symbolName: Char): Term =
    val diagonal = commonSubsequenceFound(
      module,
      listFieldRead(self, "left", "tail"),
      listFieldRead(self, "right", "tail"),
      library.readSlot(library.natural, "predecessor", library.readSlot(commonSubsequence, "need", self))
    )
    val mismatch = library.libraryClass(names, "natural", "false")
    val (onA, onB) = if symbolName == 'a' then (diagonal, mismatch) else (mismatch, diagonal)
    library.slotApplied(symbol, "accept", listFieldRead(self, "right", "head"), onA, onB)

  /** self.field.slot, the field the list left or right (`list_field_read/4`). */
  private def listFieldRead(self: Term, field: String, slot: String): Term =
    library.readSlot(list, slot, library.readSlot(commonSubsequence, field, self))

  /** The common subsequence points, each with its length
    * (`common_subsequence_point/2`).
    */
  val commonSubsequencePoints: Vector[(String, Int)] =
    file.rows("common_subsequence_point").map(arguments =>
      (ProblemData.text(arguments(0)), ProblemData.small(arguments(1)))
    )

  // ---- the corpus's predicates ----

  /** The point's program. */
  def program(name: String): Term =
    graphPoints.find(_._1 == name).map((_, graphName, query, _) => graphSurface(graphName, query))
      .orElse(subsetPoints.find(_._1 == name).map((_, count) =>
        val items = DynamicReferences.subsetItems(count).map(BigInt(_))
        subsetSurface(items, items.sum)
      ))
      .orElse(commonSubsequencePoints.find(_._1 == name).map((_, length) =>
        val (left, right, need) = DynamicReferences.lcsPointStrings(length)
        commonSubsequenceSurface(left, right, need)
      ))
      .getOrElse(throw IllegalArgumentException(s"$name is no point of contest_mixin_claims"))

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    val yields = "so the test yields \\\\a. a"
    graphPoints.flatMap((name, _, query, path) =>
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"the path ${path.mkString("[", ",", "]")} of the query ${query.written} is a finite sequence of choices, each union of classes choosing the class of the path's next node or its reachable, and its end reads the marker of the target, the Church true, $yields"
      )
    ) ++ subsetPoints.flatMap((name, count) =>
      val items = DynamicReferences.subsetItems(count).map(BigInt(_))
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"${items.sum} is the sum of all of the items ${items.mkString("[", ",", "]")}: choosing the branch that takes the item at every level makes n finite binary additions and then the binary equality, which reaches the Church true, $yields"
      )
    ) ++ commonSubsequencePoints.flatMap((name, length) =>
      val (left, right, need) = DynamicReferences.lcsPointStrings(length)
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"${MergeDynamic.symbols(left)} and ${MergeDynamic.symbols(right)} have a common subsequence of length $need (the reference's table); following its matches through the three-way union reaches need zero in finitely many steps, whose found is the Church true, $yields"
      )
    )

/** The ring edges and paths of the mixin graphs. */
object MixinClaims:

  /** The ring prefix0 -> prefix1 -> ... -> prefix(size - 1) -> prefix0 and
    * its nodes (`ring_edges/4`).
    */
  def ringEdges(prefix: String, size: Int): (Vector[(String, String)], Vector[String]) =
    (
      (0 until size).toVector.map(index => s"$prefix$index" -> s"$prefix${(index + 1) % size}"),
      (0 until size).toVector.map(index => s"$prefix$index")
    )

  /** n0, n1, ..., n(size - 1) (`ring_path/2`). */
  def ringPath(size: Int): Vector[String] = (0 until size).toVector.map(index => s"n$index")
