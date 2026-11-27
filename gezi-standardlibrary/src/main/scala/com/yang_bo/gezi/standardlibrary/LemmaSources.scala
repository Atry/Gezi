package com.yang_bo.gezi.standardlibrary

import java.nio.file.Path
import com.yang_bo.gezi.directorysugar.DirectoryTree
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.DeBruijnTermOf
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.Literal
import com.yang_bo.gezi.frontend.SyntaxSpans
import com.yang_bo.gezi.locations.Span
import com.yang_bo.gezi.ir.{Configured, NoFacts}

/** A lemma declaration as a knowledge file's text writes it: the lemma's name
  * and the spans, in the text's code points, of its two sides.
  */
final case class LemmaDeclarationSource(name: String, left: Span, right: Span)

/** Where the lemmas of a knowledge file are written, for a trace's debug
  * information: each lemma, shared as a β-redex, has the location of where it
  * is written.
  *
  * The library reads the knowledge as one term, and a declaration knows no
  * knowledge file (`StandardLibrary.compiled`); this reading stands beside the
  * library and changes nothing it reads. A file's text is read as its directory
  * tree reads it, in the scope of its tree's names (`DirectoryTree.scope`),
  * with the spans of its nodes (`Lambdalattice.locatedInScope`), and a lemma
  * declaration is found by its structure, `λs. s NAME LEFT RIGHT PROOF`
  * (`KnowledgeFileReading`), its name the trie of a string literal,
  * `λk. k "name"`, read from the bits the literal spreads into, as the host
  * reads a name.
  */
object LemmaSources:

  /** The lemma declarations the text of the knowledge file at the path writes,
    * in the order of the text. Throws the errors of
    * `Lambdalattice.locatedInScope` for a text it does not read.
    */
  def declared(path: Path, text: String): Vector[LemmaDeclarationSource] =
    val (term, spans) =
      Lambdalattice.locatedInScope(DirectoryTree.scope(path), text)
    declarations(term, spans).map(_.source)

  /** The texts of the index's lemmas (`texts`) among the knowledge files under
    * the roots, keyed by each lemma's two sides, as a trace's writer takes them
    * (`com.yang_bo.gezi.rewritetrace.TraceText.writtenWith`). A file is read only when its
    * text quotes one of the lemmas' names, the cheap test before its parse; a
    * directory named `target`, a build's output, is not walked.
    */
  def textsUnder(
      visible: Path,
      roots: Vector[Path],
      index: StandardLibraryIndex[NoFacts.type]
  ): Map[
    (Configured[NoFacts.type], Configured[NoFacts.type]),
    com.yang_bo.gezi.locations.LemmaText[NoFacts.type]
  ] =
    val lemmas = index.lemmaNames.flatMap(named =>
      index.lemmaSides.find(_.lemma == named.lemma).map(sides => (named, sides))
    )
    val quoted = lemmas.map((named, _) => s"\"${named.name}\"")
    val files = roots
      .filter(java.nio.file.Files.isDirectory(_))
      .flatMap(root =>
        scala.util.Using.resource(java.nio.file.Files.walk(root))(walked =>
          scala.jdk.CollectionConverters
            .ListHasAsScala(walked.toList)
            .asScala
            .toVector
        )
      )
      .filter(path => path.getFileName.toString.endsWith(".lambdalattice"))
      .filterNot(path =>
        (0 until path.getNameCount).exists(place =>
          path.getName(place).toString == "target"
        )
      )
      .distinct
      .filter(path =>
        val text = java.nio.file.Files
          .readString(path, java.nio.charset.StandardCharsets.UTF_8)
        quoted.exists(text.contains)
      )
    val sidesOf = lemmas
      .map((named, sides) => named.lemma -> (sides.left, sides.right))
      .toMap
    texts(visible, files, lemmas).flatMap((lemma, text) =>
      sidesOf.get(lemma).map(_ -> text)
    )

  /** Each attributed lemma as its file writes it (`attributed`): the file's
    * URI, its sides' spans and text, and the names the sides use that the file
    * binds outside the declaration, each with its value. A name's value is read
    * by walking a side's term in the file against the closed term of the
    * lemma's IR side (`Defunctionalization.instructionTerm`): where the file's
    * term has a free name, the closed term has that name's value. Throws
    * `IllegalStateException` when a side's term is not the closed term with
    * values for its free names, and when one name has two values.
    */
  def texts(
      visible: Path,
      files: Vector[Path],
      lemmas: Vector[(LemmaNamed, LemmaSides[NoFacts.type])]
  ): Map[com.yang_bo.gezi.ir.LemmaIdentifier, com.yang_bo.gezi.locations.LemmaText[NoFacts.type]] =
    val sidesOf = lemmas.map((named, sides) => named.lemma -> sides).toMap
    attributed(visible, files, lemmas).toVector
      .groupBy((_, found) => found._1)
      .toVector
      .flatMap((file, attributions) =>
        val text = java.nio.file.Files
          .readString(file, java.nio.charset.StandardCharsets.UTF_8)
        val codePoints = codePointsOf(text)
        def slice(span: Span): String = codePoints
          .slice(span.start, span.end)
          .map(Character.toString(_))
          .mkString
        val (term, spans) =
          Lambdalattice.locatedInScope(DirectoryTree.scope(file), text)
        val byName = declarations(term, spans)
          .map(found => found.source.name -> found)
          .toMap
        attributions.flatMap((lemma, found) =>
          val (_, source) = found
          val sides = sidesOf.getOrElse(
            lemma,
            throw IllegalStateException(
              s"an attributed lemma $lemma has no sides"
            )
          )
          byName
            .get(source.name)
            .map(declared =>
              val names = (namesOf(
                declared.left,
                declared.leftSpans,
                sides.left,
                slice
              ) ++
                namesOf(
                  declared.right,
                  declared.rightSpans,
                  sides.right,
                  slice
                )).distinct
              names
                .groupBy(_._1)
                .find(_._2.size > 1)
                .foreach((name, values) =>
                  throw IllegalStateException(
                    s"the name $name of the lemma ${source.name} has ${values.size} values"
                  )
                )
              lemma -> com.yang_bo.gezi.locations.LemmaText(
                file.toUri,
                source.left,
                source.right,
                slice(source.left),
                slice(source.right),
                names
              )
            )
        )
      )
      .toMap

  /** The free names of a side's term in its file, each with its value: the
    * subterm of the side's closed term at the name's place. Recursive on the
    * side's depth, as `declarations` is.
    *
    * The closed term is read back one layer at a time (`layerTerm`), each part
    * an instruction of the IR left a `Constant` until the file's term has
    * structure there: a name's value is the instruction at its place, and the
    * library terms a side names are never read back whole (measured 2026-11-19
    * on `contest-entries-wren` in `EntryTracesTest`: reading each side back
    * whole took 2,448 of the test's 10,646 samples).
    */
  private def namesOf(
      side: DeBruijnTerm,
      spans: SyntaxSpans,
      instruction: Configured[NoFacts.type],
      slice: Span => String
  ): Vector[(String, Configured[NoFacts.type])] =
    given NoFacts.type = NoFacts
    def walked(
        term: DeBruijnTerm,
        at: SyntaxSpans,
        read: DeBruijnTermOf[Configured[NoFacts.type]],
        depth: Int
    ): Vector[(String, Configured[NoFacts.type])] =
      val closed: DeBruijnTermOf[Configured[NoFacts.type]] =
        (term.layer, read.layer) match
          case (com.yang_bo.gezi.frontend.Variable(_), _)    => read
          case (_, com.yang_bo.gezi.frontend.Constant(part)) => layerTerm(part)
          case _                                 => read
      (term.layer, closed.layer) match
        case (com.yang_bo.gezi.frontend.Variable(index), com.yang_bo.gezi.frontend.Constant(part))
            if index >= depth =>
          Vector(slice(at.span) -> part)
        case (com.yang_bo.gezi.frontend.Variable(index), _) if index >= depth =>
          Vector(
            slice(at.span) -> com.yang_bo.gezi.frontend.Defunctionalization
              .thunkInstruction[NoFacts.type](closed)
          )
        case (com.yang_bo.gezi.frontend.Variable(index), com.yang_bo.gezi.frontend.Variable(other))
            if index == other =>
          Vector.empty
        case (com.yang_bo.gezi.frontend.Lambda(body), com.yang_bo.gezi.frontend.Lambda(closedBody)) =>
          walked(body, at.child(0), closedBody, depth + 1)
        case (
              com.yang_bo.gezi.ir.Apply(function, argument),
              com.yang_bo.gezi.ir.Apply(closedFunction, closedArgument)
            ) =>
          walked(function, at.child(0), closedFunction, depth) ++ walked(
            argument,
            at.child(1),
            closedArgument,
            depth
          )
        case (
              com.yang_bo.gezi.ir.Choice(left, right),
              com.yang_bo.gezi.ir.Choice(closedLeft, closedRight)
            ) =>
          walked(left, at.child(0), closedLeft, depth) ++ walked(
            right,
            at.child(1),
            closedRight,
            depth
          )
        case (
              com.yang_bo.gezi.ir.Parallel(left, right),
              com.yang_bo.gezi.ir.Parallel(closedLeft, closedRight)
            ) =>
          walked(left, at.child(0), closedLeft, depth) ++ walked(
            right,
            at.child(1),
            closedRight,
            depth
          )
        case _ =>
          throw IllegalStateException(
            s"a lemma side's text ${slice(at.span)} reads as $term, the side's term has $closed there"
          )
    walked(side, spans, layerTerm(instruction), 0)

  /** The readback of the instruction one layer deep: its parts, and a thunk's
    * fillings, as `Constant`s (`Defunctionalization.instructionTerm` with them
    * as stops). The parts are closed, so no variable of the layer reaches into
    * them.
    */
  private def layerTerm(instruction: Configured[NoFacts.type])(using
      NoFacts.type
  ): DeBruijnTermOf[Configured[NoFacts.type]] =
    val parts: Set[Configured[NoFacts.type]] = instruction.layer match
      case com.yang_bo.gezi.ir.Apply(function, argument) => Set(function, argument)
      case com.yang_bo.gezi.ir.Choice(left, right)       => Set(left, right)
      case com.yang_bo.gezi.ir.Parallel(left, right)     => Set(left, right)
      case com.yang_bo.gezi.ir.Thunk(_, _, fillings)     => fillings.toSet
      case _                                 => Set.empty
    com.yang_bo.gezi.frontend.Defunctionalization.instructionTerm(instruction, parts)

  /** The code points of the text, in which the spans count. */
  private def codePointsOf(text: String): Vector[Int] =
    @scala.annotation.tailrec
    def from(index: Int, found: Vector[Int]): Vector[Int] =
      if index >= text.length then found
      else
        val point = text.codePointAt(index)
        from(index + Character.charCount(point), found :+ point)
    from(0, Vector.empty)

  /** A declaration with the terms and the spans of its two sides. */
  private final case class Declared(
      source: LemmaDeclarationSource,
      left: DeBruijnTerm,
      leftSpans: SyntaxSpans,
      right: DeBruijnTerm,
      rightSpans: SyntaxSpans
  )

  /** The declaration of each of the library's lemmas among the knowledge files:
    * the file whose declaration of the lemma's name reads, in the file's own
    * scope, as the lemma's two sides, as the library reads a knowledge file
    * (`StandardLibrary.entryTerm`, `entryGroup`, `slotRead`), with that
    * declaration's spans in the file's text. A lemma no file declares so has
    * none. The library itself still knows no file per declaration; this reading
    * stands beside it.
    */
  def attributed(
      visible: Path,
      files: Vector[Path],
      lemmas: Vector[(LemmaNamed, LemmaSides[NoFacts.type])]
  ): Map[com.yang_bo.gezi.ir.LemmaIdentifier, (Path, LemmaDeclarationSource)] =
    // A file is read as the library reads it, which evaluates its imports,
    // only when its text declares one of the names: the text is the cheap
    // reading. One reading state runs through the files, so that the
    // library files their imports reach are expanded once (each file read
    // under a fresh state took 0.7 s to 1.5 s, cores 4-7, 2026-11-17).
    given NoFacts.type = NoFacts
    val names = lemmas.map(_._1.name).toSet
    val (read, _) = files.foldLeft(
      (
        Vector.empty[
          (
              Path,
              Map[String, (Configured[NoFacts.type], Configured[NoFacts.type])],
              Map[String, LemmaDeclarationSource]
          )
        ],
        com.yang_bo.gezi.knowledgereading.KnowledgeReading.compilationState
      )
    ) { case ((gathered, state), file) =>
      val texts =
        declared(
          file,
          java.nio.file.Files
            .readString(file, java.nio.charset.StandardCharsets.UTF_8)
        ).map(found => found.name -> found).toMap
      if !texts.keySet.exists(names.contains) then (gathered, state)
      else
        val (group, afterEntry) = StandardLibrary.entryGroup(
          StandardLibrary.entryTerm(visible, file, state)
        )
        val knowledge =
          com.yang_bo.gezi.knowledgereading.KnowledgeReading.term(group, Set.empty)
        val (declarations, afterLemmas) =
          StandardLibrary.slotRead(knowledge, KnowledgeSlot.Lemmas, afterEntry)
        val sides = declarations.collect {
          case Declaration.ReadLemma(name, left, right, _) =>
            name -> (left, right)
        }.toMap
        (gathered :+ ((file, sides, texts)), afterLemmas)
    }
    lemmas
      .flatMap((named, lemmaSides) =>
        read.view
          .flatMap((file, sides, texts) =>
            texts
              .get(named.name)
              .filter(_ =>
                sides
                  .get(named.name)
                  .exists((left, right) =>
                    Configured.same(left, lemmaSides.left) && Configured
                      .same(right, lemmaSides.right)
                  )
              )
              .map(found => named.lemma -> (file, found))
          )
          .headOption
      )
      .toMap

  /** The declarations in the term, outermost first in preorder. Recursive on
    * the term's depth: a knowledge file is a few hundred layers deep at most,
    * its longest chain the bits of a string literal.
    */
  private def declarations(
      term: DeBruijnTerm,
      spans: SyntaxSpans
  ): Vector[Declared] =
    val here = term match
      case DeBruijnTerm.Lambda(
            DeBruijnTerm.Apply(
              DeBruijnTerm.Apply(
                DeBruijnTerm.Apply(
                  DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), name),
                  left
                ),
                right
              ),
              _
            )
          ) =>
        nameOf(name).map(written =>
          val body = spans.child(0)
          val leftSpans = body.child(0).child(0).child(1)
          val rightSpans = body.child(0).child(1)
          Declared(
            LemmaDeclarationSource(written, leftSpans.span, rightSpans.span),
            left,
            leftSpans,
            right,
            rightSpans
          )
        )
      case _ => None
    here.toVector ++ children(term).zipWithIndex.flatMap((child, index) =>
      declarations(child, spans.child(index))
    )

  /** The terms one layer below, in the order of their spans. */
  private def children(term: DeBruijnTerm): Vector[DeBruijnTerm] =
    term.layer match
      case com.yang_bo.gezi.frontend.Lambda(body)        => Vector(body)
      case com.yang_bo.gezi.ir.Apply(function, argument) => Vector(function, argument)
      case com.yang_bo.gezi.ir.Choice(left, right)       => Vector(left, right)
      case com.yang_bo.gezi.ir.Parallel(left, right)     => Vector(left, right)
      case _                                 => Vector.empty

  /** The text a name's trie wraps, `λk. k b1 … bn` with each bi the closed
    * Scott boolean of a bit, high bit first, eight to a byte; none for a term
    * of another shape or bytes that are no CBOR text string.
    */
  private def nameOf(term: DeBruijnTerm): Option[String] =
    @scala.annotation.tailrec
    def bits(
        spine: DeBruijnTerm,
        found: List[Boolean]
    ): Option[Vector[Boolean]] = spine match
      case DeBruijnTerm.Variable(0) => Some(found.toVector)
      case DeBruijnTerm.Apply(
            function,
            DeBruijnTerm.Lambda(
              DeBruijnTerm.Lambda(DeBruijnTerm.Variable(index))
            )
          ) if index == 0 || index == 1 =>
        bits(function, (index == 1) :: found)
      case _ => None
    term match
      case DeBruijnTerm.Lambda(spine) =>
        bits(spine, Nil)
          .filter(read => read.nonEmpty && read.size % 8 == 0)
          .flatMap(read =>
            val bytes = Vector.tabulate(read.size / 8)(place =>
              read
                .slice(place * 8, place * 8 + 8)
                .foldLeft(0)((high, bit) => high * 2 + (if bit then 1 else 0))
                .toByte
            )
            Literal.textRead(Literal(IArray.from(bytes))).toOption
          )
      case _ => None
