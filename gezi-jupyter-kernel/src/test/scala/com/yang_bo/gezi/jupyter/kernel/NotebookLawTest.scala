package com.yang_bo.gezi.jupyter.kernel

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import com.yang_bo.gezi.directorysugar.DirectoryTree
import com.yang_bo.gezi.frontend.Literal
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Head
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.weakhead.WeakHead

private given notebookLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the notebook's mixin cells, on generated keys and generated
  * closed normal forms. Its purpose is to catch a cell content whose output
  * keys the kernel misreads (a key dropped, reordered, or found in a content
  * that is no chain of + of partial functions), an import written outside the
  * partial functions that changes a member's value rather than only the output,
  * an order of the cells that changes a member, a cell run again that does not
  * replace its earlier version, and a content that closes the parenthesis the
  * kernel writes around it, and a content that a console would wait on for more
  * lines though no line could make it read, or send though it is not finished.
  */
class NotebookLawTest extends GeneratedProperties:

  private val readingLimit: Long = 100000

  private val tree: Configured[NoFacts.type] =
    DirectoryTree.rootOf(Files.createTempDirectory("notebook-tree"))

  /** A short location, whatever directory the tests run in: no law depends on
    * it, and a cell's reading costs in proportion to the bits of its location's
    * keys (`NotebookCell.read`).
    */
  private val location: NotebookLocation = NotebookLocation(
    Vector("file", "n", "law")
  )

  private def text(term: Term): String = LambdalatticeText.text(term)

  /** Distinct keys, each a short string of letters, "io" among the first keys'
    * choices so that both kinds of key paths occur.
    */
  private val keys: Gen[Vector[String]] =
    Gen
      .list(
        Gen.choice1(
          Gen.constant("io"),
          Gen.string(Gen.lower, Range.linear(1, 4))
        ),
        Range.linear(1, 4)
      )
      .map(_.distinct.toVector)

  private def chain(members: Vector[(String, Term)]): String =
    members
      .map((key, value) => s"(λ\"$key\". (${text(value)}))")
      .mkString(" + ")

  /** The answers of the member at the key, each the set of its heads. */
  private def answers(notebook: Notebook, key: String): Set[Set[Head]] =
    WeakHead
      .heads(
        Mode.TablingWeakHead,
        notebook.member(OutputKey(Vector(Literal.text(key)), Vector(key)))
      )
      .collected
      .result(
        ReadingState.knowingTop(
          readingLimit,
          com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
        )
      ) match
      case Computed.Done(sets, _) => sets.map(_.heads.toSet).toSet
      case Computed.Stopped(_)    =>
        throw IllegalStateException(
          s"the member $key ran past $readingLimit steps"
        )

  property(
    "a chain of + of partial functions outputs its key paths in order, and a content with its import outside outputs none"
  ) {
    for
      written <- keys.forAll
      values <- Gen
        .list(HoasGenerators.normalForm, Range.singleton(written.size))
        .forAll
    yield
      val content = chain(written.zip(values))
      val outputs = CellContent.outputKeys(content)
      Result
        .diff(
          outputs.map(_.literals),
          written.map(key => Vector(Literal.text(key)))
        )(_ == _)
        .and(Result.diff(outputs.map(_.isIo), written.map(_ == "io"))(_ == _))
        .and(
          Result.diff(
            CellContent.outputKeys(s"(λm. m) ($content)"),
            Vector.empty[OutputKey]
          )(_ == _)
        )
  }

  property(
    "an import outside the partial functions changes no member, only the output"
  ) {
    for
      written <- keys.forAll
      values <- Gen
        .list(HoasGenerators.normalForm, Range.singleton(written.size))
        .forAll
    yield
      val content = chain(written.zip(values))
      val inside = Notebook(location, tree, Vector.empty).added(
        NotebookCell.read("cell", content, location)
      )
      val outside = Notebook(location, tree, Vector.empty).added(
        NotebookCell.read("cell", s"(λm. m) ($content)", location)
      )
      Result.all(
        written.toList.map(key =>
          Result.diff(answers(outside, key), answers(inside, key))(_ == _)
        )
      )
  }

  property("the cells' order changes no member") {
    for
      key <- Gen.string(Gen.lower, Range.linear(1, 4)).forAll
      values <- Gen.list(HoasGenerators.normalForm, Range.linear(2, 4)).forAll
      seed <- Gen.int(Range.linear(0, 1000)).forAll
    yield
      val cells = values.toVector.zipWithIndex.map((value, index) =>
        NotebookCell.read(s"cell $index", chain(Vector(key -> value)), location)
      )
      val shuffled = new scala.util.Random(seed).shuffle(cells)
      val inOrder =
        cells.foldLeft(Notebook(location, tree, Vector.empty))(_.added(_))
      val inShuffle =
        shuffled.foldLeft(Notebook(location, tree, Vector.empty))(_.added(_))
      Result.diff(answers(inShuffle, key), answers(inOrder, key))(_ == _)
  }

  property(
    "a cell run again under its id is as if its earlier version never ran"
  ) {
    for
      key <- Gen.string(Gen.lower, Range.linear(1, 4)).forAll
      earlier <- HoasGenerators.normalForm.forAll
      later <- HoasGenerators.normalForm.forAll
      other <- HoasGenerators.normalForm.forAll
    yield
      val empty = Notebook(location, tree, Vector.empty)
      val replaced = empty
        .added(
          NotebookCell.read("first", chain(Vector(key -> earlier)), location)
        )
        .added(
          NotebookCell.read("second", chain(Vector(key -> other)), location)
        )
        .added(
          NotebookCell.read("first", chain(Vector(key -> later)), location)
        )
      val fresh = empty
        .added(
          NotebookCell.read("first", chain(Vector(key -> later)), location)
        )
        .added(
          NotebookCell.read("second", chain(Vector(key -> other)), location)
        )
      Result.diff(replaced, fresh)(_ == _)
  }

  property(
    "a content that closes a parenthesis it did not open does not read, though it would close the kernel's own"
  ) {
    for
      function <- HoasGenerators.normalForm.forAll
      argument <- HoasGenerators.normalForm.forAll
    yield
      val balanced = NotebookCell.read(
        "cell",
        s"(${text(function)}) (${text(argument)})",
        location
      )
      val _ = intercept[com.yang_bo.gezi.frontend.LambdalatticeMalformed](
        NotebookCell.read(
          "cell",
          s"${text(function)}) (${text(argument)}",
          location
        )
      )
      Result.diff(balanced.outputs, Vector.empty[OutputKey])(_ == _)
  }

  property(
    "a content left open ends too soon, and one closed too often does not"
  ) {
    for term <- HoasGenerators.normalForm.forAll
    yield
      def problem(content: String) =
        intercept[com.yang_bo.gezi.frontend.LambdalatticeMalformed](
          NotebookCell.read("cell", content, location)
        ).problem
      val open = s"(${text(term)}"
      val closed = s"${text(term)})"
      Result
        .diff(NotebookCell.endsTooSoon(problem(open), open, location), true)(
          _ == _
        )
        .and(
          Result.diff(
            NotebookCell.endsTooSoon(problem(closed), closed, location),
            false
          )(_ == _)
        )
  }
