package gezi.contest.corpora.reductions

import java.nio.file.Paths
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.knowledgereading.KnowledgeReading
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import gezi.ir.Value

/** The data file of the library terms (`TermTables.problemLibraryTerms`)
  * imports the files it names: every member of the data file, read off it by
  * projection, is the field of the same name read off its own library file by
  * the same projection, at the field's position in that file's tuple, and holds
  * no opaque node, no URI node among them. It would catch a wrong import path
  * or position in the data file, a member at another position than its name's
  * in the table, or a member whose read-back still refers to the tree. The law
  * is checked on every name of the table.
  */
class StandardLibraryTermsLawTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of StandardLibraryTermsLawTest, "every member of the library terms' file is the field of its own library file, with no opaque node", takes 16.751 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(30, "s")

  private val root =
    Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  /** The library file under `corpora/library` whose field each key is, and the
    * field's position in the file's tuple: each file with the keys of its
    * fields in their positions, `_` for a field no key names.
    */
  private val fields: Map[String, (String, Int)] =
    Vector(
      "native_types/natural" -> Vector("zero", "successor", "nat_fold"),
      "native_types/combinators" -> Vector("identity", "_", "compose"),
      "native_types/list" -> Vector("nil", "cons", "list_fold"),
      "native_types/boolean" -> Vector("true", "false"),
      "native_types/fixpoint" -> Vector("fixpoint"),
      "native_arithmetic/native_arithmetic" -> Vector("double", "even"),
      "fixed_width/word_representation" -> Vector("word_end", "word_cell"),
      "fixed_width/word_multiplication" -> Vector("_", "_", "word_multiply"),
      "binary/natural" -> Vector("binary_zero", "binary_even", "binary_odd"),
      "binary/arithmetic" -> Vector(
        "merge_binary_increment",
        "merge_binary_plus",
        "merge_binary_times",
        "merge_binary_equality"
      ),
      "binary/order" -> Vector("_", "binary_maximum", "binary_minimum"),
      "binary/binary_bitwise_or" -> Vector("binary_bitwise_or")
    ).flatMap((file, keys) =>
      keys.zipWithIndex.collect {
        case (key, position) if key != "_" => key -> (file, position)
      }
    ).toMap

  private def opaqueNodes(instruction: NoFactsTerm): Int =
    def walk(
        pending: List[NoFactsTerm],
        seen: Set[NoFactsTerm],
        count: Int
    ): Int = pending match
      case Nil                                 => count
      case head :: rest if seen.contains(head) => walk(rest, seen, count)
      case head :: rest if head.opaque => walk(rest, seen + head, count + 1)
      case head :: rest                =>
        walk(head.layer.children.toList ++ rest, seen + head, count)
    walk(List(instruction), Set.empty, 0)

  /** The field at the position of the tuple the library file returns, read back
    * to a closed instruction, as `StandardLibrary.entryMember` reads the one
    * field of a file: the file's term by projection off the tree
    * (`StandardLibrary.entryTerm`), its fields taken by
    * `KnowledgeReading.alternative`, within
    * `StandardLibrary.memberReadingLimit`.
    */
  private def fieldOf(file: String, position: Int): NoFactsTerm =
    val reading = StandardLibrary.entryTerm(
      root,
      root.resolve(s"corpora/library/$file.lambdalattice"),
      KnowledgeReading.startingState
    )
    KnowledgeReading
      .run(
        KnowledgeReading
          .alternative(Value.of(reading.term), 1)
          .map((_, found) =>
            KnowledgeReading.term(
              found
                .lift(position)
                .getOrElse(
                  fail(s"$file has ${found.size} fields, none at $position")
                ),
              Set.empty
            )
          ),
        StandardLibrary.memberReadingLimit,
        reading.state
      )
      ._1

  /** Each name's member off the data file equals its field off its own file
    * under `corpora/library`, and holds no opaque node.
    */
  private def checked(table: TermTable): Unit =
    val fromData = StandardLibrary.entryMembers(root, table, Expansions.none)._1
    table.names.foreach { key =>
      val (own, position) = fields(key)
      assert(
        fromData.get(key).exists(Configured.same(_, fieldOf(own, position))),
        key
      )
      assertEquals(fromData.get(key).map(opaqueNodes), Some(0), key)
    }

  test(
    "every member of the library terms' file is the field of its own library file, with no opaque node"
  ) {
    assertEquals(fields.keySet, TermTables.problemLibraryTerms.names.toSet)
    checked(TermTables.problemLibraryTerms)
  }
