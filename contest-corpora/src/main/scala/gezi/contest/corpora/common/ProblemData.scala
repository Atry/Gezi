package gezi.contest.corpora.common

import java.nio.file.Path
import gezi.directorysugar.DirectoryTree
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.knowledgereading.Reading
import gezi.weakhead.Computation
import gezi.hotspot.Cache
import gezi.hotspot.Retention
import gezi.hotspot.ExpansionSource
import gezi.weakhead.Expansions
import gezi.weakhead.ReadingState
import gezi.weakhead.TableSharing
import gezi.ir.Value
import gezi.weakhead.Values
import gezi.ir.{Configured, NoFacts}

/** The corpora are read under no facts. */
private given problemDataNoFacts: NoFacts.type = NoFacts

/** A field of a row of a problem table, as the file wrote it: a term the
  * reader has opened and not evaluated. What it is (a text, a number, a
  * list, a constructor, a program) is the reader's question, answered by
  * the decoders of `ProblemData`, each read from `reading`, the state of the
  * family the field was read from (`ProblemFamily`), which keeps its
  * complete tables where every read of the family finds them, so that the
  * decodings of many fields share the tables of what they read alike, such
  * as `from_cbor` of a byte many texts hold.
  * The state is not
  * part of the field's identity: two fields are equal when their
  * instructions are.
  */
final case class ProblemField(instruction: Configured[NoFacts.type])(reading: ReadingState[NoFacts.type]):

  /** The text of the field, a Scott list of bytes, read once, when first
    * asked for (`ProblemData.text`).
    */
  lazy val text: String = ProblemData.read(KnowledgeReading.text(Value.of(instruction)), reading)

  /** The integer of the field, the library's Scott integer, which a table
    * writes as `from_cbor` of `integer/cbor` given the identity and an
    * integer literal, `(integer 12)`,
    * read by structure once, when first asked for (`ProblemData.integer`).
    */
  lazy val integer: BigInt = ProblemData.read(KnowledgeReading.integer(Value.of(instruction)), reading)

  /** The truth of the field, a Scott boolean of
    * corpora/library/prelude/boolean, `true` (`λt. λf. t`) or `false`
    * (`λt. λf. f`), read by structure once, when first asked for
    * (`ProblemData.truth`).
    */
  lazy val truth: Boolean = ProblemData.read(KnowledgeReading.truth(Value.of(instruction)), reading)

  /** The items of the field as a list, read once, when first asked for
    * (`ProblemData.list`), so that an item's own decodings are read once
    * too.
    */
  lazy val items: Vector[ProblemField] =
    ProblemData.read(KnowledgeReading.items(Value.of(instruction)).map(_.map(ProblemData.field(_, reading))), reading)

  /** The two fields of an open program, read from the field's state. */
  private[common] def openFields: Vector[Value[NoFacts.type]] = ProblemData.read(KnowledgeReading.fields(Value.of(instruction), 2), reading)

  /** The alternative a Scott constructor of `count` alternatives takes and
    * its fields (`ProblemData.alternative`), read from the field's state.
    */
  private[common] def alternativeOf(count: Int): (Int, Vector[ProblemField]) =
    ProblemData.read(KnowledgeReading.alternative(Value.of(instruction), count), reading) match
      case (position, fields) => (position, fields.map(sibling))

  /** A field read as this one is, from the same state. */
  private[common] def sibling(value: Value[NoFacts.type]): ProblemField = ProblemData.field(value, reading)

/** The data of one problem family, the directory `problems/<family>`
  * of Gezi, `family` the path of the directory under
  * `problems`, such as `mixin_builtin` or `cses/dice_combinations`: its files read from the directory by their names
  * (`programs`, `tables`), and their constructors read
  * under weak head as `KnowledgeReading` reads knowledge, with no semantics
  * of their own.
  *
  * A file is a table or a program. A table is the Scott list of its rows,
  * each row the constructor `λ_p. _p F1 … Fn` of its fields. A program is a
  * term, the leading abstractions its parameters. A family's directory is
  * read once, when first used; `root` is the directory `gezi`.
  *
  * The families stand in `gezi/problems`, beside the source tree
  * `gezi/corpora` and not in it: every compile of the standard library
  * reads that whole tree (`StandardLibrary`), so problem data in it would be
  * parsed by every library compile, a cost no reader of the library needs. A
  * family is read as a tree of its own.
  *
  * `expansions` are the URI expansions its owner carries
  * (`ProblemFamilies.sharedExpansions`), from which the family's first
  * read starts: they hold those of the imports every table reads at its
  * top (`ProblemData.importExpansions`), which the family does not read
  * again. `sharing` is where every read of the family keeps its complete
  * tables and finds those other reads kept (`TableSharing`), the owner's.
  */
final class ProblemFamily(root: Path, val family: String, expansions: Expansions[NoFacts.type], sharing: TableSharing):

  private lazy val directory: Path = root.resolve("problems").resolve(family)

  /** The names of the files of the directory. */
  private lazy val names: Vector[String] = DirectoryTree.fileKeys(directory)

  private def path(name: String): Path =
    if !names.contains(name) then throw IllegalArgumentException(s"problems/$family has no file $name")
    directory.resolve(name + DirectoryTree.fileExtension)

  /** The family's directory looked up off the tree's root once
    * (`DirectoryTree.mixin`), from which each file is looked up by its own
    * key: the root's levels are partial functions of the bits of each level
    * of the absolute path, which were converted again for each file read.
    */
  private lazy val directoryMixin: Configured[NoFacts.type] = DirectoryTree.mixin[NoFacts.type](root, directory)

  /** The instance of the file of the name: `DirectoryTree.instance` of its
    * path, the same instruction, looked up off `directoryMixin`.
    */
  private def instance(name: String): Configured[NoFacts.type] =
    val reached = DirectoryTree.lookedUp(directoryMixin, Vector(path(name).getFileName.toString.stripSuffix(DirectoryTree.fileExtension)))
    NoFacts.application(reached, reached)

  /** The term of each program file, by its name, each read once, when first
    * asked for: the one field of the tuple the file returns
    * (`KnowledgeReading.soleField`), read as a table
    * is, from `readingState`, off the file's instance in the tree whose visible
    * subtree is `root` (`DirectoryTree.instance`), so that a program imports
    * what it uses by projecting it off its scope, such as `prelude_clauses`'
    * `natural_equal`, `fixpoint natural_equal_body`.
    * The field is not
    * evaluated: it is the term as written, each imported name the term it
    * imports, and a program with no head, such as `easy_terms/omega`, is
    * read as it is written. Throws `IllegalArgumentException` naming the file
    * for a file that is no tuple of one field.
    */
  private lazy val programs: Map[String, LazyList[Configured[NoFacts.type]]] =
    names.map(name => name -> LazyList.fill(1)(programField(name))).toMap

  private def programField(name: String): Configured[NoFacts.type] =
    try
      KnowledgeReading
        .run(
          KnowledgeReading.soleField(Value.of(instance(name))).map(Values.instruction),
          ProblemData.readingLimit,
          readingState
        )
        ._1
    catch
      case KnowledgeReadingError(reason) =>
        throw IllegalArgumentException(s"problems/$family/$name is no tuple of one field: $reason")

  /** The URI expansions every table and program of the family is read from:
    * the owner's (`Expansions`), which hold those of the members `from_cbor`
    * of `text/cbor` and of `integer/cbor` that the tables import at their
    * tops (`ProblemData.textImport`, `ProblemData.integerImport`), grown by a
    * read of the heads of the family's directory in the tree (off
    * `directoryMixin`), so that a read lists no directory and parses no file
    * the tables share: a read does not start from a fresh state. Read once, when first asked for:
    * the expansions are the contents of the files, which do not change while
    * the owner holds them.
    */
  private lazy val familyExpansions: Expansions[NoFacts.type] =
    KnowledgeReading
      .run(
        KnowledgeReading.headsTerm(Value.of(directoryMixin)),
        ProblemData.readingLimit,
        KnowledgeReading.startingState.copy(expansions = expansions, sharing = sharing)
      )
      ._2
      .expansions

  /** The state each read of the family starts from: no table of its own,
    * the family's expansions, and the owner's sharing, through which a read
    * finds complete the tables an earlier read kept, among them those of the
    * root's projection to the directory, which every file of the family is
    * looked up from and every import of a program projects again.
    * How long they
    * stay there is the cache service's choice, not this module's. Each read
    * starts from it, so the files are read in any order.
    */
  private def readingState: ReadingState[NoFacts.type] =
    KnowledgeReading.startingState.copy(expansions = familyExpansions, sharing = sharing)

  /** The rows of each file read as a table, by its name, each read once,
    * when first asked for, from `readingState`: the file's instance in the
    * tree whose visible subtree is `root` (`DirectoryTree.instance`), a
    * tuple whose one field is the table (`KnowledgeReading.soleField`), so
    * that a table imports the library's `text/cbor` at its top and
    * writes each text as `from_cbor` of the identity and a string literal, a Scott list of
    * bytes; a table that writes integers
    * imports `integer/cbor` likewise and writes each as `from_cbor` of the
    * identity and an integer literal, the library's Scott integer.
    * A program file is no table,
    * and is never read as one.
    */
  private lazy val tables: Map[String, LazyList[Vector[Vector[ProblemField]]]] =
    names.map(name =>
      name -> LazyList.fill(1)(
        KnowledgeReading
          .run(
            KnowledgeReading
              .soleField(Value.of(instance(name)))
              .flatMap(KnowledgeReading.items)
              .flatMap(items =>
                Computation.traversed(items)(item => KnowledgeReading.alternative(item, 1).map(_._2.map(ProblemData.field(_, readingState))))
              ),
            ProblemData.readingLimit,
            readingState
          )
          ._1
      )
    ).toMap

  /** The rows of the table, in the order of the file, each the vector of its
    * fields. Throws when a row is no constructor of one alternative.
    */
  def rows(table: String): Vector[Vector[ProblemField]] =
    tables.getOrElse(table, throw IllegalArgumentException(s"problems/$family has no file $table")).head

  /** The rows of the table whose fields at the positions of `texts` (from 0)
    * are those texts.
    */
  def rowsWith(table: String, texts: Map[Int, String]): Vector[Vector[ProblemField]] =
    rows(table).filter(fields => texts.forall((position, text) => ProblemData.text(fields(position)) == text))

  /** The one row of the table whose fields at the positions of `texts` are
    * those texts. Throws when there is not exactly one.
    */
  def row(table: String, texts: Map[Int, String]): Vector[ProblemField] =
    rowsWith(table, texts) match
      case Vector(single) => single
      case found =>
        throw IllegalArgumentException(s"problems/$family/$table: ${found.size} rows with the texts $texts, not one")

  /** The rows of the table keyed by the text of their first field, each
    * with its other fields. Throws when two rows share a key.
    */
  def keyed(table: String): Map[String, Vector[ProblemField]] =
    val entries = rows(table).map(fields => (ProblemData.text(fields.head), fields.tail))
    if entries.map(_._1).distinct.size != entries.size then
      throw IllegalArgumentException(s"problems/$family/$table: two rows share a key")
    entries.toMap

  /** The program at the position `result` of the one row of the table
    * whose fields at the positions of `texts` are those texts, its leading
    * abstractions instantiated by the arguments in the order of their
    * positions: the row's parameters, whose places hold the parameters'
    * names, in the order the conversion abstracted them.
    */
  def template(table: String, texts: Map[Int, String], arguments: Map[Int, ProblemTerm], result: Int): ProblemTerm =
    ProblemData.program(row(table, texts)(result), arguments.toVector.sortBy(_._1).map(_._2))

  /** The program file, its leading abstractions instantiated by the
    * arguments in order.
    */
  def program(name: String, arguments: ProblemTerm*): ProblemTerm =
    ProblemData.program(
      ProblemField(programs.getOrElse(name, throw IllegalArgumentException(s"problems/$family has no file $name")).head)(readingState),
      arguments.toVector
    )

/** The problem families under `root`, the directory `gezi`: one
  * `ProblemFamily` for each directory of `problems`, each read once,
  * when first used, all of them from `sharedExpansions`. `expansions` are
  * the URI expansions the owner carries (`Expansions`), and `cache` the cache
  * service it carries, in which every family's reads keep their complete
  * tables (`sharing`).
  */
final class ProblemFamilies(root: Path, expansions: Expansions[NoFacts.type], cache: Cache):

  /** Where every read of every family keeps its complete tables: the
    * owner's cache service, with strong references, so that they stay until
    * the service is cleared. The expansion source is one for all the families: they read
    * one tree of files, which does not change while this object reads it, so
    * a table one family keeps, such as those of `text/cbor`'s import, is the
    * least fixed point another family's read would compute.
    */
  private val sharing: TableSharing = TableSharing.Shared(cache, Retention.Strong, ExpansionSource.fresh())

  /** The owner's URI expansions grown by those every family's tables share:
    * the imports of `text/cbor` and of `integer/cbor` at their tops
    * (`ProblemData.textImport`, `ProblemData.integerImport`) and the
    * directory `problems`, so that each family lists only its own
    * directory. Read once, when first asked for.
    */
  lazy val sharedExpansions: Expansions[NoFacts.type] =
    ProblemData.directoryExpansions(root, root.resolve("problems"), ProblemData.importExpansions(root, expansions))

  /** The families by the paths of their directories under `problems`, the
    * names joined by `/`: every directory, those under a family's directory
    * included, such as `cses/dice_combinations`, which holds a point table
    * of the CSES port.
    * A family is read only when first used, so a directory that holds no
    * table costs nothing.
    */
  private lazy val families: Map[String, ProblemFamily] =
    val problems = root.resolve("problems")
    if !problems.toFile.isDirectory then throw IllegalArgumentException(s"$root has no directory problems")
    directoriesUnder(problems, Vector.empty)
      .map(names => names.mkString("/"))
      .map(family => family -> ProblemFamily(root, family, sharedExpansions, sharing))
      .toMap

  /** The paths of the directories under the directory, each the names
    * from it down, after the prefix.
    */
  private def directoriesUnder(directory: Path, prefix: Vector[String]): Vector[Vector[String]] =
    Option(directory.toFile.listFiles())
      .getOrElse(throw IllegalArgumentException(s"$directory is no directory"))
      .toVector
      .filter(_.isDirectory)
      .flatMap(found =>
        val names = prefix :+ found.getName
        names +: directoriesUnder(found.toPath, names)
      )

  /** The family of the name, the path of its directory under `problems`
    * (`families`). Throws for a name no directory has.
    */
  def apply(family: String): ProblemFamily =
    families.getOrElse(family, throw IllegalArgumentException(s"problems has no family $family"))

/** The decoders of the fields of problem tables, each reading the field
  * under weak head with fresh neutral variables (`KnowledgeReading`).
  */
object ProblemData:

  /** The evaluator steps the reading of one table or one field may spend.
    * Measured 2026-11-10 (the same probe): a table at most 3,368 steps
    * (hard_answers/hard_intended), a field read as a text at most 35,532 (a
    * row of hard_claims/unread_finite_head) and as a list at most 4,656; the
    * limit is about 10 times the largest.
    */
  private[common] val readingLimit: Long = 400000L

  /** The file `text/cbor`, a tuple of 4 fields whose first is `from_cbor`, every table imports at its top,
    * under Gezi's directory: the tables' convention, read first into
    * the expansions the reads of a family start from (`ProblemFamily.familyExpansions`).
    */
  private[common] val textImport: String = "corpora/library/text/cbor.lambdalattice"

  /** The file `integer/cbor`, a tuple of 2 fields whose first is `from_cbor`,
    * which a table that writes integers imports at its top, `(integer 12)`:
    * read first into the state the tables of a family share, as `textImport`
    * is.
    */
  private[common] val integerImport: String = "corpora/library/integer/cbor.lambdalattice"

  /** The expansions grown by a read of the first field, `from_cbor`, of
    * `textImport` and of `integerImport` under the root's tree.
    */
  private[common] def importExpansions(root: Path, expansions: Expansions[NoFacts.type]): Expansions[NoFacts.type] =
    KnowledgeReading
      .run(
        KnowledgeReading
          .fields(Value.of(DirectoryTree.instance[NoFacts.type](root, root.resolve(textImport))), 4)
          .map {
            case Vector(fromCbor, _, _, _) => KnowledgeReading.term(fromCbor, Set.empty)
            case other => throw IllegalArgumentException(s"text/cbor has ${other.size} fields, not 4")
          }
          .flatMap(_ =>
            KnowledgeReading
              .fields(Value.of(DirectoryTree.instance[NoFacts.type](root, root.resolve(integerImport))), 2)
              .map {
                case Vector(fromCbor, _) => KnowledgeReading.term(fromCbor, Set.empty)
                case other => throw IllegalArgumentException(s"integer/cbor has ${other.size} fields, not 2")
              }
          ),
        readingLimit,
        KnowledgeReading.startingState.copy(expansions = expansions)
      )
      ._2
      .expansions

  /** The expansions grown by a read of the heads of the directory's mixin
    * under the root's tree, which lists it and the directories above it.
    */
  private[common] def directoryExpansions(root: Path, directory: Path, expansions: Expansions[NoFacts.type]): Expansions[NoFacts.type] =
    KnowledgeReading
      .run(
        KnowledgeReading.headsTerm(Value.of(DirectoryTree.mixin[NoFacts.type](root, directory))),
        readingLimit,
        KnowledgeReading.startingState.copy(expansions = expansions)
      )
      ._2
      .expansions

  /** The reading's value, from the state, its tables left where the state
    * keeps them (`TableSharing`).
    */
  private[common] def read[Result](reading: Reading[NoFacts.type, Result], state: ReadingState[NoFacts.type]): Result =
    KnowledgeReading.run(reading, readingLimit, state)._1

  private[common] def field(value: Value[NoFacts.type], state: ReadingState[NoFacts.type]): ProblemField = ProblemField(Values.instruction(value))(state)

  /** The text of a Scott list of bytes, which a table writes as
    * `from_cbor` of the identity and a string literal: an atom or a string
    * of the data is written as one. An integer that a reader reads as a
    * number is written as the library's Scott integer instead (`integer`),
    * and a Boolean as a Scott boolean (`truth`).
    */
  def text(field: ProblemField): String = field.text

  /** The integer of a field that writes the library's Scott integer
    * (`ProblemField.integer`).
    */
  def integer(field: ProblemField): BigInt = field.integer

  /** The integer of a field that writes the library's Scott integer, one
    * that fits an `Int`. Throws `IllegalArgumentException` for one that does
    * not.
    */
  def small(field: ProblemField): Int =
    val value = integer(field)
    if !value.isValidInt then throw IllegalArgumentException(s"not a small integer: $value")
    value.toInt

  /** The items of a list. */
  def list(field: ProblemField): Vector[ProblemField] = field.items

  /** The texts of a list of texts. */
  def texts(field: ProblemField): Vector[String] = list(field).map(text)

  /** The small integers (`small`) of a list of Scott integers. */
  def smalls(field: ProblemField): Vector[Int] = list(field).map(small)

  /** The alternative a Scott constructor of `count` alternatives takes, by
    * its position among them, and its fields: an option of the data read by
    * structure, never by a name: an option that cannot make a reading unsound
    * is a Scott ADT. The
    * constructors are those of the option's file, which the table imports.
    * Throws for a value of no such constructor or of several.
    */
  def alternative(field: ProblemField, count: Int): (Int, Vector[ProblemField]) =
    field.alternativeOf(count)

  /** The number of cases of the enum, from its sum mirror: the number of
    * constructors of the option's file whose cases, in its order, the enum
    * lists. Unlike `values`, it counts the cases that carry fields.
    */
  inline def caseCount[Enumeration](using mirror: scala.deriving.Mirror.SumOf[Enumeration]): Int =
    scala.compiletime.constValue[Tuple.Size[mirror.MirroredElemTypes]]

  /** The Church Boolean of corpora/library/prelude/boolean a field writes,
    * `λt. λf. t` (true) or `λt. λf. f` (false), read by its position
    * (`alternative`). Throws for a value with fields.
    */
  def boolean(field: ProblemField): Boolean = alternative(field, 2) match
    case (0, Vector()) => true
    case (1, Vector()) => false
    case (position, fields) =>
      throw IllegalArgumentException(s"a Church Boolean at position $position has ${fields.size} fields")

  /** The truth of a field that writes a Scott boolean of
    * corpora/library/prelude/boolean (`ProblemField.truth`).
    */
  def truth(field: ProblemField): Boolean = field.truth

  /** The program, its leading abstractions instantiated by the arguments in
    * order, as the front end's HOAS term.
    */
  def program(field: ProblemField, arguments: Vector[ProblemTerm]): ProblemTerm =
    DeBruijnTerms.instantiated(Defunctionalization.instructionTerm[NoFacts.type](field.instruction), arguments)

  /** A program with free variables, `λ_open. _open "m" Program`: m, and the
    * program instantiated by the arguments in order, its parameters' and
    * then its m free variables'.
    */
  def openProgram(field: ProblemField): (Int, Vector[ProblemTerm] => ProblemTerm) =
    field.openFields match
      case Vector(count, program) =>
        val programField = field.sibling(program)
        (small(field.sibling(count)), arguments => ProblemData.program(programField, arguments))
      case other => throw IllegalArgumentException(s"not an open program: $other")
