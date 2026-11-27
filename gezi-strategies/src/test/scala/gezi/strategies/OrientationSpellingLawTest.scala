package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BindingNormalForm
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.OrientationCompilation
import gezi.orientation.StandardOrientationCompiler
import gezi.rewritetrace.Statements
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** The laws that the orientations the index compiles hold a lemma side's
  * thunks with holes in the front end's spelling, the spelling every program
  * is in: a side as the
  * baseline encoding splits it into its metavariables' fillings and the holes
  * left need not be (`λk. λa. λz. k a` has the thunk
  * `thunk(apply(slot 0, slot 1), [ignored], [k, a])`, which a program spells
  * `thunk(slot 0, [ignored], [apply(k, a)])`), and an orientation whose side
  * holds such a thunk looks for a code no program holds, so its lemma never
  * fires. The generated lemmas are two terms under the same one to three
  * binders.
  */
class OrientationSpellingLawTest extends GeneratedProperties:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  private val lemmas: Gen[LemmaSides[NoFacts.type]] =
    for
      count <- Gen.int(Range.linear(1, 3))
      left <- Gen.sized(size => HoasGenerators.openTerm(count, size.value / 2))
      right <- Gen.sized(size => HoasGenerators.openTerm(count, size.value / 2))
    yield
      def closed(body: HoasGenerators.Open) =
        def lambdas(outer: Vector[Term]): Term =
          if outer.size == count then body(outer) else Term.λ(bound => lambdas(outer :+ bound))
        Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](lambdas(Vector.empty).deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)
      LemmaSides(LemmaIdentifier(0), closed(left), closed(right))

  private def normalizedSides(sides: LemmaSides[NoFacts.type]): Vector[(Pattern[NoFacts.type], Pattern[NoFacts.type])] =
    val encoded =
      BaselineLemmaEncoding.encoded(StandardLibraryIndex(NoFacts, Vector.empty, Vector(sides), Vector.empty, Vector.empty), sides)
    Vector(encoded.left, encoded.right).map(side => (side, OrientationCompilation.normalized(side, Store(Set.empty, gezi.ir.TermConstruction(gezi.ir.NoFacts)))))

  private def thunks(pattern: Pattern[NoFacts.type]): Vector[Pattern.Thunk[NoFacts.type]] =
    val own = pattern match
      case thunk @ Pattern.Thunk(_, holes, _) if holes.nonEmpty => Vector(thunk)
      case _                                                    => Vector.empty
    own ++ pattern.children.flatMap(thunks)

  /** Purpose: catch an orientation whose side keeps a thunk the front end
    * never spells, whose lemma then never fires.
    */
  property("every thunk with holes of an orientation's side is its own spelling") {
    for sides <- lemmas.forAll
    yield
      val unspelled = normalizedSides(sides)
        .flatMap((_, normalized) => thunks(normalized))
        .filter { case Pattern.Thunk(code, holes, fillings) =>
          BindingNormalForm.respelled(code, holes, fillings.size).nonEmpty
        }
      Result.assert(unspelled.isEmpty).log(s"thunks not in the front end's spelling: $unspelled")
  }

  /** The leaf a metavariable stands for in an instance: an opaque term of its
    * own for each index, which the front end's spelling keeps as a leaf.
    */
  private def leaf(index: Int): Configured[NoFacts.type] = NoFacts.opaque(s"the leaf of metavariable $index")

  /** The instance of a pattern, metavariable i the leaf i; none for a
    * pattern with a closure, whose instance is no one term.
    */
  private def instance(pattern: Pattern[NoFacts.type]): Option[Configured[NoFacts.type]] = pattern match
    case Pattern.Metavariable(index)          => Some(leaf(index))
    case Pattern.InstructionReference(instruction) => Some(instruction)
    case Pattern.Closure(_)                   => None
    case Pattern.Apply(function, argument)    => instance(function).zip(instance(argument)).map(NoFacts.application(_, _))
    case Pattern.Parallel(left, right)        => instance(left).zip(instance(right)).map(NoFacts.parallel(_, _))
    case Pattern.Choice(left, right)          => instance(left).zip(instance(right)).map(NoFacts.choice(_, _))
    case Pattern.Thunk(code, holes, fillings) =>
      val made = fillings.flatMap(instance)
      Option.when(made.size == fillings.size)(NoFacts.thunkOrInstance(code, holes, made))

  /** Purpose: catch a respelling that changes what the side stands for, or
    * spells it otherwise than the front end: the instance of the normalized
    * pattern is the front end's spelling (`BindingNormalForm.spelled`) of the
    * instance of the side as the encoding states it, each metavariable a leaf
    * of its own. A side with an eta-shaped lambda, which `normalized` reads
    * as a closure, is left out.
    */
  property("an encoded side's instance, spelled by the front end, is its normalized pattern's instance") {
    for sides <- lemmas.forAll
    yield
      val pairs = normalizedSides(sides).flatMap((stated, normalized) => instance(stated).zip(instance(normalized)))
      Result.all(pairs.toList.map((stated, normalized) =>
        Result.diff(normalized, BindingNormalForm.spelled(stated))(_ eq _).log(s"$stated normalized to $normalized")
      ))
  }

  /** Purpose: catch an index that looks for another spelling than the graph
    * builds (`normalized` and `EGraph.layerMade` spelling one thunk in two
    * ways, such as merging two fillings that hold one metavariable):
    * the instance of a
    * side as the encoding states it and the instance of its normalized
    * pattern, the same leaves at the metavariables, are one node of the
    * graph. A side with an eta-shaped lambda, which `normalized` reads as a
    * closure, is left out.
    */
  property("an encoded side and its normalized pattern are one node of the graph") {
    for sides <- lemmas.forAll
    yield
      val pairs = normalizedSides(sides).flatMap((stated, normalized) => instance(stated).zip(instance(normalized)))
      Result.all(pairs.toList.map((stated, normalized) => oneNode(stated, normalized)))
  }

  /** The graph's store: each metavariable's leaf noinline, a leaf node of a
    * class of its own. Four leaves are more than the metavariables of any
    * generated lemma or pattern.
    */
  private val leafStore: Store[NoFacts.type] = Store(Set.tabulate(4)(leaf), gezi.ir.TermConstruction(gezi.ir.NoFacts))

  private def oneNode(stated: Configured[NoFacts.type], normalized: Configured[NoFacts.type]): Result =
    val (graph, statedNode) = EGraph.empty(leafStore, Map.empty, explained = false).instructionAdded(stated)
    val (_, normalizedNode) = graph.instructionAdded(normalized)
    Result.diff(normalizedNode, statedNode)(_ == _).log(s"$stated and $normalized")

  /** Thunk patterns with metavariables repeated among their fillings, which
    * no encoded side holds (the front end makes equal subterms one slot): the
    * thunk of a generated lambda of two or three binders with its first hole
    * dropped, as the β rule leaves it, each filling a metavariable 0 or 1.
    */
  private val nonlinearThunks: Gen[Pattern[NoFacts.type]] =
    for
      count <- Gen.int(Range.linear(2, 3))
      body <- Gen.sized(size => HoasGenerators.openTerm(count, size.value / 2))
      metavariables <- Gen.int(Range.constant(0, 1)).list(Range.singleton(count + 8))
    yield
      def lambdas(outer: Vector[Term]): Term =
        if outer.size == count then body(outer) else Term.λ(bound => lambdas(outer :+ bound))
      Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](lambdas(Vector.empty).deBruijnTerm(Map.empty))(using gezi.ir.NoFacts).layer match
        case gezi.ir.Thunk(code, _ +: holes, _) =>
          val arity = Statements.thunkArity(code, holes)
          Pattern.Thunk(code, holes, metavariables.take(arity).toVector.map(Pattern.Metavariable(_)))
        case other => throw IllegalStateException(s"a lambda of $count binders is no thunk: $other")

  /** Purpose: catch `normalized` merging two fillings that hold one
    * metavariable, which the graph keeps apart (`EGraph.layerMade` spells by
    * position): the instance of such a thunk and of its normalized pattern
    * are one node.
    */
  property("a thunk with a metavariable in two fillings and its normalized pattern are one node") {
    for thunk <- nonlinearThunks.forAll
    yield
      val stated = instance(thunk)
      val normalized = instance(OrientationCompilation.normalized(thunk, Store(Set.empty, gezi.ir.TermConstruction(gezi.ir.NoFacts))))
      Result.all(stated.zip(normalized).toList.map((left, right) => oneNode(left, right)))
  }

  /** The unions the lemma `counted` made in a saturation of the program under
    * the lemmas, with the built-in rules, within 8 instances.
    */
  private def lemmaUnions(
      lemmas: Vector[LemmaSides[NoFacts.type]],
      counted: LemmaIdentifier,
      rules: Set[BuiltInRule],
      program: Configured[NoFacts.type],
      stop: StopSignal
  ): Int =
    val index = StandardLibraryIndex(NoFacts, Vector.empty, lemmas, Vector.empty, Vector.empty)
    val saturator = StandardSaturator(
      SaturationOptions(lemmas.map(_.lemma), rules, 8, BaselineLemmaEncoding, ClosureCompilation, StandardIndexer.of[gezi.ir.NoFacts.type], StandardOrientationCompiler, MemoRetention.Kept, gezi.ir.TermConstruction(gezi.ir.NoFacts))
    )
    saturator
      .saturated(index, Vector(program), true, stop)
      .graph
      .unions
      .count(_.justification match
        case Justification.Lemma(lemma, _) => lemma == counted
        case _                             => false)

  private def side(text: String): Configured[NoFacts.type] = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](Lambdalattice.term(text))(using gezi.ir.NoFacts)

  /** Three lemmas whose sides hold a thunk in another spelling than the
    * front end's, each with a program it fires on: a side holding `λz. k a`, which the
    * encoding splits into the fillings k and a, against `λz. K A` with K and
    * A closed, which the front end spells with the one filling `K A`.
    */
  private val witnesses: Vector[(LemmaSides[NoFacts.type], (Term, Term) => Term)] = Vector(
    (
      LemmaSides(LemmaIdentifier(0), side("λk. λa. ((λz. k a) + (λz. k a))"), side("λk. λa. λz. k a")),
      (function, argument) => Term.choice(Term.λ(_ => function(argument)), Term.λ(_ => function(argument)))
    ),
    (
      LemmaSides(LemmaIdentifier(0), side("λk. λa. λz. k a"), side("λk. λa. ((λz. k a) + (λz. k a))")),
      (function, argument) => Term.λ(_ => function(argument))
    ),
    (
      LemmaSides(LemmaIdentifier(0), side("λk. λa. (λz. k a) (λq. q)"), side("λk. λa. k a")),
      (function, argument) => Term.λ(_ => function(argument))(Term.λ(bound => bound))
    )
  )

  /** Purpose: catch a lemma whose side holds a thunk in another spelling
    * than the front end's never firing on a program it matches (the three
    * witnesses, each with 0 lemma unions before the orientation respelled
    * its sides).
    */
  stoppableProperty("each of #1641's lemmas fires on a program that holds its side") { stopped =>
    for
      function <- HoasGenerators.closedTerm.forAll
      argument <- HoasGenerators.closedTerm.forAll
    yield Result.all(witnesses.toList.map((lemma, program) =>
      val input = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](program(function, argument).deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)
      val unions = lemmaUnions(Vector(lemma), lemma.lemma, BuiltInRule.beforeOptIn, input, StopSignal.completedWith(stopped))
      Result.assert(unions > 0).log(s"the lemma $lemma made $unions unions on $input")
    ))
  }

  /** A lemma that adds `λz. k a` as stated, `thunk(apply(slot 0, slot 1),
    * [ignored], [k, a])`, a node in no front end's spelling, and a lemma
    * whose matched side is that thunk as stated.
    */
  private val chained: Vector[LemmaSides[NoFacts.type]] = Vector(
    LemmaSides(LemmaIdentifier(0), side("λk. λa. (λx. x) (k a)"), side("λk. λa. λz. k a")),
    LemmaSides(LemmaIdentifier(1), side("λk. λa. λz. k a"), side("λk. λa. ((λz. k a) + (λz. k a))"))
  )

  /** Purpose: catch an orientation that matches only the respelled side and
    * so no longer matches a node another lemma added in the stated spelling,
    * a match main makes: on `(λx. x) (K A)`, the first lemma of `chained`
    * adds `λz. K A` as stated, and the second, whose matched side is that
    * thunk, fires on it. No built-in rule, so that only the lemmas act.
    */
  stoppableProperty("a lemma whose stated side another lemma adds still fires on it") { stopped =>
    for
      function <- HoasGenerators.closedTerm.forAll
      argument <- HoasGenerators.closedTerm.forAll
    yield
      val input = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](
        Term.λ(bound => bound)(function(argument)).deBruijnTerm(Map.empty)
      )(using gezi.ir.NoFacts)
      val unions = lemmaUnions(chained, LemmaIdentifier(1), Set.empty, input, StopSignal.completedWith(stopped))
      Result.assert(unions > 0).log(s"the second lemma made $unions unions on $input")
  }

  /** Purpose: catch a respelled orientation's instance that a certificate
    * cannot state: under the higher-order saturator, on a program holding the
    * matched side of one of the witnesses' lemmas in the front end's spelling, the
    * lemma fires through the respelled orientation, the article of the
    * program's equation to the lemma's other side as stated takes a respelling
    * step (`Axiom.Respell`) and the OpenTheory tool accepts it, and its trace
    * replays to that side's replay spelling.
    */
  stoppableProperty("under the higher-order saturator, #1641's lemmas fire and their articles check through the respelling equation") { stopped =>
    for
      function <- HoasGenerators.closedTerm.forAll
      argument <- HoasGenerators.closedTerm.forAll
      witness <- Gen.element1(witnesses.head, witnesses.tail*).forAll
    yield
      val (lemma, program) = witness
      val index = StandardLibraryIndex(NoFacts, Vector.empty, Vector(lemma), Vector.empty, Vector.empty)
      val saturator = HigherOrderSaturator(
        SaturationOptions(Vector(lemma.lemma), BuiltInRule.beforeOptIn, 8, BaselineLemmaEncoding, ClosureCompilation, StandardIndexer.of[gezi.ir.NoFacts.type], StandardOrientationCompiler, MemoRetention.Kept, gezi.ir.TermConstruction(gezi.ir.NoFacts)),
        None,
        None,
        gezi.saturation.OpeningCriterionChoice.CallsAHead
      )
      val input = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](program(function, argument).deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)
      val run = saturator.saturated(index, Vector(input), true, StopSignal.completedWith(stopped))
      val unions = run.graph.unions.count(_.justification match
        case Justification.Lemma(_, _) => true
        case _                         => false)
      val output = gezi.rewritetrace.Statements.instance(
        gezi.rewritetrace.Statements.lemma(lemma.left, lemma.right).right,
        Map(
          "metavariable0" -> Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](function.deBruijnTerm(Map.empty))(using gezi.ir.NoFacts),
          "metavariable1" -> Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](argument.deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)
        )
      )
      val proof = GraphProof.proof(run.graph, Vector((input, output)), saturator.lemmas(index))
      val derivation = gezi.proofs.OpentheoryArticle.derivation(index, input, output, proof)
      val respellings = gezi.proofs.RewriteTrace.of(derivation).count(_.reason match
        case gezi.proofs.RewriteReason.Respell(_, _, _) => true
        case _                                         => false
      )
      val article = java.nio.file.Files.createTempFile("respelled_orientation", ".art")
      val checked =
        try
          gezi.proofs.OpentheoryArticle.written(index, input, output, proof, article)
          gezi.proofs.ProofTestFiles.toolChecked(article)
        finally java.nio.file.Files.delete(article)
      Result
        .all(
          List(
            Result.assert(unions > 0).log(s"the lemma made no union on $input"),
            Result.assert(respellings > 0).log("the article takes no respelling step"),
            Result.diff(checked, (0, ""))(_ == _).log("the OpenTheory tool's exit status and standard error"),
            Result
              .assert(gezi.proofs.RewriteTrace.trace(derivation).output(input) eq gezi.rewritetrace.ReplaySpelling.term(output))
              .log("the trace does not replay to the other side's spelling")
          )
        )
        .log(s"the lemma $lemma on $input")
  }
