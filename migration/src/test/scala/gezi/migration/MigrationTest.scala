package gezi.migration

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.FreeNames
import gezi.frontend.Lambdalattice
import gezi.frontend.LambdalatticeMalformed
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import gezi.ir.Configured
import gezi.ir.LemmaIdentifier
import gezi.ir.NoFacts
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.ir.TermConstruction
import gezi.locations.Span
import gezi.orientation.LemmaSides
import snapshot4s.generated.snapshotConfig

/** The migrations of generated closed texts.
  *
  *   - Law: the text with parentheses added around generated nodes and then
  *     removed (`SpellingMigration.parenthesesRemoved`) reads to the term of
  *     the text, and no pair of parentheses left can be removed alone with the
  *     term kept. Its purpose is to catch a removal kept that changes the term,
  *     and a removable pair the walk misses or the shift of positions
  *     misplaces.
  *   - Law: a text that uses enclosing names, as a file of a directory tree
  *     uses its directories' selves, with parentheses removed in their scope
  *     reads in that scope to the term it read to, and the parentheses around
  *     the names are gone. Its purpose is to catch a removal checked by a
  *     reading outside the scope, which rejects every such text.
  *   - Law: with some of the pairs candidates, the removal keeps the term,
  *     every other pair stays a pair at the position the removal moved it to,
  *     and no character but parentheses and spaces changes. Its purpose is to
  *     catch a removal of a pair that was no candidate, which in a term
  *     migration would respell the text it copies.
  *   - Law: a term migration by a lemma (`TermMigration.migrated`), the
  *     choice's commutativity or the β step of K, leaves the text outside its
  *     sites as it was, and each site's text read alone is an instance of the
  *     lemma's left side, its replacement of the right side's (the migrated
  *     text and the original are one class, which the migration checks itself
  *     and throws on). Its purpose is to catch an edit at a shifted position, a
  *     site that is no instance, and a replacement written from other bindings.
  *   - Snapshot: texts and their migrations by both lemmas, from a fixed seed.
  *     Its purpose is to record the text a migration writes, an output as
  *     complex as the printer and the splicing.
  */
class MigrationTest extends GeneratedProperties with SeededSnapshots:

  given NoFacts.type = NoFacts

  private val uri: java.net.URI =
    java.net.URI.create("file:///generated.lambdalattice")

  private val store: Store[NoFacts.type] =
    Store[NoFacts.type](Set.empty, TermConstruction(NoFacts))

  private def metavariable(index: Int): Pattern[NoFacts.type] =
    Pattern.Metavariable(index)

  /** M + N = N + M, law (1), a theorem of the formal definition. */
  private val commutativity: LemmaSides[NoFacts.type] =
    LemmaSides[NoFacts.type](
      LemmaIdentifier(0),
      2,
      Pattern.Choice(metavariable(0), metavariable(1)),
      Pattern.Choice(metavariable(1), metavariable(0))
    )

  /** K M N = M, two steps of the β rule, K being λx. λy. x. */
  private val constant: LemmaSides[NoFacts.type] =
    val k = Defunctionalization.thunkInstruction[NoFacts.type](
      Lambdalattice.term("λx. λy. x")
    )
    LemmaSides[NoFacts.type](
      LemmaIdentifier(1),
      2,
      Pattern.Apply(
        Pattern.Apply(Pattern.InstructionReference(k), metavariable(0)),
        metavariable(1)
      ),
      metavariable(0)
    )

  private val closedText: Gen[String] =
    HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** A closed text with K applied in it, its binders named otherwise than the
    * lemma's.
    */
  private val textWithConstant: Gen[String] =
    for
      context <- closedText
      first <- closedText
      second <- closedText
    yield s"$context + (λk. λl. k) ($first) ($second)"

  /** A choice of closed texts, so that the choice and its right side are closed
    * and the commutativity matches them, the outer one rewritten.
    */
  private val textWithChoices: Gen[String] =
    closedText
      .list(Range.linear(2, 4))
      .map(_.map(member => s"($member)").mkString(" + "))

  /** A text and the lemma that migrates it. */
  private val migrations: Gen[(String, LemmaSides[NoFacts.type])] =
    Gen.choice1(
      textWithChoices.map((_, commutativity)),
      textWithConstant.map((_, constant))
    )

  private def read(text: String): Option[gezi.frontend.DeBruijnTerm] =
    try Some(Lambdalattice.located(text, FreeNames.Rejected).term)
    catch case LambdalatticeMalformed(_) => None

  /** The text with parentheses written around the nodes at the positions drawn,
    * each position an index into the text's written node spans.
    */
  private def parenthesized(text: String, positions: Vector[Int]): String =
    val spans = nodeSpans(Lambdalattice.located(text, FreeNames.Rejected).spans)
    val chosen =
      positions.map(position => spans(position % spans.size)).distinct
    val codePoints = SpellingMigration.codePointsOf(text)
    val opens = chosen.groupBy(_.start).view.mapValues(_.size).toMap
    val closes = chosen.groupBy(_.end).view.mapValues(_.size).toMap
    SpellingMigration.textOf(
      (0 to codePoints.size).toVector.flatMap(at =>
        Vector.fill(closes.getOrElse(at, 0))(')'.toInt) ++ Vector.fill(
          opens.getOrElse(at, 0)
        )('('.toInt) ++
          codePoints.lift(at).toVector
      )
    )

  private def nodeSpans(spans: gezi.frontend.SyntaxSpans): Vector[Span] =
    spans match
      case gezi.frontend.SyntaxSpans.Written(span, _, children, _) =>
        span +: children.flatMap(nodeSpans)
      case gezi.frontend.SyntaxSpans.Generated(span, _, written, _) =>
        span +: written.flatMap(entry => nodeSpans(entry._2))

  property(
    "removing parentheses keeps the term and leaves no pair removable alone"
  ) {
    val generated =
      for
        text <- closedText
        positions <- Gen
          .int(Range.linear(0, 1000))
          .list(Range.linear(0, 6))
          .map(_.toVector)
      yield parenthesized(text, positions)
    generated
      .forAllWithLog(identity)
      .map(text =>
        val term = read(text)
        val removed = SpellingMigration.parenthesesRemoved(text)
        val codePoints = SpellingMigration.codePointsOf(removed)
        val removable = SpellingMigration
          .parentheses(Lambdalattice.located(removed, FreeNames.Rejected).spans)
          .filter(pair =>
            read(
              SpellingMigration.textOf(
                codePoints
                  .patch(pair.end - 1, Vector(' '.toInt), 1)
                  .patch(pair.start, Vector(' '.toInt), 1)
              )
            ) == term
          )
        val problems =
          (if read(removed) == term then Vector.empty
           else Vector(s"`$removed` reads another term")) ++
            removable.map(pair => s"the pair $pair of `$removed` is removable")
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  property(
    "removing parentheses in the scope of enclosing names keeps the term read in that scope"
  ) {
    val generated =
      for
        text <- closedText
        positions <- Gen
          .int(Range.linear(0, 1000))
          .list(Range.linear(0, 6))
          .map(_.toVector)
        enclosing <- Gen
          .element1("uri", "file", "corpora", "library")
          .list(Range.linear(1, 4))
          .map(_.toVector)
      yield (
        enclosing,
        enclosing
          .map(name => s"($name)")
          .mkString(" ") + s" (${parenthesized(text, positions)})"
      )
    generated
      .forAllWithLog((enclosing, text) => s"$enclosing $text")
      .map((enclosing, text) =>
        val removed = SpellingMigration.parenthesesRemoved(enclosing, text)
        val problems =
          (if Lambdalattice
               .locatedInScope(enclosing, removed)
               ._1 == Lambdalattice.locatedInScope(enclosing, text)._1
           then Vector.empty
           else
             Vector(s"`$removed` reads another term in the scope of $enclosing")
          ) ++
            (if removed
                 .contains(enclosing.map(name => s"($name)").mkString(" "))
             then Vector(s"`$removed` keeps the names' parentheses")
             else Vector.empty)
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  property(
    "removing candidate parentheses touches no other pair and no other character"
  ) {
    val generated =
      for
        text <- closedText
        positions <- Gen
          .int(Range.linear(0, 1000))
          .list(Range.linear(1, 6))
          .map(_.toVector)
        candidateDraws <- Gen.boolean.list(Range.singleton(6)).map(_.toVector)
      yield (parenthesized(text, positions), candidateDraws)
    generated
      .forAllWithLog(_._1)
      .map((text, candidateDraws) =>
        val pairs = SpellingMigration
          .parentheses(Lambdalattice.located(text, FreeNames.Rejected).spans)
        val (candidates, others) =
          pairs.zipWithIndex.partition((_, index) => candidateDraws(index % 6))
        val (removed, moved) =
          SpellingMigration
            .parenthesesRemoved(text, candidates.map(_._1), others.map(_._1))
        val left = SpellingMigration
          .parentheses(Lambdalattice.located(removed, FreeNames.Rejected).spans)
          .toSet
        def withoutParentheses(written: String): String =
          written.filterNot(character => "() ".contains(character))
        val problems =
          (if read(removed) == read(text) then Vector.empty
           else Vector(s"`$removed` reads another term")) ++
            moved
              .filterNot(left.contains)
              .map(pair =>
                s"the pair $pair, no candidate, is not in `$removed`"
              ) ++
            (if withoutParentheses(removed) == withoutParentheses(text) then
               Vector.empty
             else Vector(s"`$removed` changes other characters"))
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  /** The instruction of a closed text read alone. */
  private def instructionOf(text: String): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction[NoFacts.type](Lambdalattice.term(text))

  /** Where the migration does not keep the text outside its sites, or a site
    * and its replacement are not the instances of the lemma's sides.
    */
  private def migrationProblems(
      text: String,
      lemma: LemmaSides[NoFacts.type]
  ): Vector[String] =
    val migrated = TermMigration.migrated(text, uri, lemma, store, budget = 200)
    val original = SpellingMigration.codePointsOf(text)
    val written = SpellingMigration.codePointsOf(migrated.text)
    def outside(
        codePoints: Vector[Int],
        spans: Vector[Span]
    ): Vector[Vector[Int]] =
      (0 +: spans.map(_.end))
        .zip(spans.map(_.start) :+ codePoints.size)
        .map((from, to) => codePoints.slice(from, to))
    val kept =
      if outside(original, migrated.sites.map(_.original)) == outside(
          written,
          migrated.sites.map(_.replaced)
        )
      then Vector.empty
      else Vector(s"`${migrated.text}` changes text outside its sites")
    val instances = migrated.sites.flatMap(site =>
      val before = instructionOf(site.original.of(original))
      val after = instructionOf(site.replaced.of(written))
      val matched = Matching.bindings(lemma.left, before, lemma.arity)
      if matched.exists(bindings =>
          Configured
            .same(TermMigration.instantiated(lemma.right, bindings), after)
        )
      then Vector.empty
      else
        Vector(
          s"`${site.original.of(original)}` to `${site.replaced.of(written)}` is no instance of the lemma"
        )
    )
    kept ++ instances

  property(
    "a term migration keeps the text outside its sites and writes the instances of the sides"
  ) {
    val generated = migrations
    generated
      .forAllWithLog((text, lemma) => s"lemma ${lemma.lemma.number}: $text")
      .map((text, lemma) =>
        val problems = migrationProblems(text, lemma)
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  test("the texts term migrations write") {
    val generated = migrations
    assertSeededSnapshot(
      generated,
      20261112L,
      8,
      "migration/term_migrations.txt"
    )(
      (text, lemma) => s"lemma ${lemma.lemma.number}: $text",
      identity[String]
    )((text, lemma) =>
      TermMigration.migrated(text, uri, lemma, store, budget = 200).text
    )
  }
