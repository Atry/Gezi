package gezi.standardlibrary

/** The text of a knowledge term as `KnowledgeFileReading` reads it:
  * the
  * fixed-width mixin of `KnowledgeSlot`, each slot a set of Scott tuples.
  * A term of
  * a member is given as its text, such as a name an import at the text's top
  * binds (`importing`), and is written as it is; the caller parenthesizes a
  * term that is no atom. A name in a member is the trie of a string
  * literal, which the host reads (`text`); a number is a literal read by the
  * library's `from_cbor` (`natural`), so a text that writes one imports it
  * (`literalImports`). The writers
  * serve the tests' generated trees only; no other caller.
  */
object KnowledgeText:

  /** A member of a key: its text. */
  final case class Member(text: String)

  /** An import at a text's top of the file reached from the bound name
    * `tree` by the labels, instantiated and its tuple matched.
    */
  enum Import:
    /** The tuple's fields bound to the binders, in order (`_` for a field
      * not used).
      */
    case Positional(tree: String, labels: Vector[String], binders: Vector[String])

    /** A tuple of one field, a Scott tuple of terms (`groupFile`, the form
      * a host reads by position, `StandardLibrary.entryMembers`), bound to
      * `group`, and its fields matched in order, `group λbinders.`.
      */
    case Grouped(tree: String, labels: Vector[String], group: String, binders: Vector[String])

  /** A text whose top binds `omega` and imports the files, each line
    * `omega (class) λbinders.`, a group's fields matched after it, around
    * the body.
    */
  def importing(imports: Vector[Import], body: String): String =
    def file(tree: String, labels: Vector[String]): String =
      labels.foldLeft(tree)((mixin, label) => s"omega ($mixin) ${quoted(label)}")
    val written = imports.map {
      case Import.Positional(tree, labels, binders) => s"omega (${file(tree, labels)}) λ${binders.mkString(" ")}.\n"
      case Import.Grouped(tree, labels, group, binders) =>
        s"omega (${file(tree, labels)}) λ$group.\n$group λ${binders.mkString(" ")}.\n"
    }
    s"(λtuple. tuple λmixin. mixin mixin) λomega.\n${written.mkString}($body)"

  /** A file's text that returns a tuple of one field, the Scott tuple of
    * the terms' texts in order (the form a host reads by position,
    * `StandardLibrary.entryMembers`), with no import.
    */
  def groupFile(terms: Vector[String]): String =
    s"λexport. ${exported(terms.map(term => s"($term)").mkString("λs. s\n", "\n", "\n"))}\n"

  /** The bound name of the library's `from_cbor` of integers, the first
    * field of `corpora/library/integer/cbor`, through which the values
    * written by `natural` are read.
    */
  val integerFromCbor: String = "integer_from_cbor"

  /** The import of `integerFromCbor` (the first of the 2 fields of
    * `integer/cbor`), from the common directory `corpora` reached from the
    * bound name `tree` by the labels (none when `tree` is `corpora`).
    */
  def literalImports(tree: String, labels: Vector[String]): Vector[Import] =
    Vector(Import.Positional(tree, labels ++ Vector("library", "integer", "cbor"), Vector(integerFromCbor, "_")))

  /** A knowledge value of the text: the trie of its string literal,
    * `(λk. k "…")`, whose bits the host reads (`KnowledgeReading.trieText`);
    * it needs no import.
    */
  def text(written: String): String = s"(λk. k ${quoted(written)})"

  /** A knowledge value of the natural: `from_cbor` of the identity
    * continuation and the integer literal, which the text's top imports
    * (`literalImports`). Throws `IllegalArgumentException` for a negative
    * number.
    */
  def natural(number: Int): String =
    if number < 0 then throw IllegalArgumentException(s"a natural, not $number")
    s"($integerFromCbor (λx. x) $number)"

  /** A file's text that returns a tuple of one field, `λexport. … export
    * (body)` (the binder `export` of the whole file),
    * the imports
    * under `export`.
    */
  def file(imports: Vector[Import], body: String): String =
    s"λexport. ${importing(imports, exported(body))}\n"

  /** The body handed to the file's `export`, the one field of its tuple. */
  def exported(body: String): String = s"export ($body)"

  /** A string literal of the text. */
  def quoted(text: String): String =
    "\"" + text.flatMap {
      case '"'   => "\\\""
      case '\\'  => "\\\\"
      case other => other.toString
    } + "\""

  /** A member of `natives` or `representations`: the pair of the term and a
    * name.
    */
  def named(term: String, name: String): String = s"(λs. s $term ${text(name)})"

  /** A member of `jvm_types`: the pair of the term and the JVM type's
    * constructor, written closed,
    * `λalternative_0. … λalternative_n. alternative_position`: the term the
    * published list `corpora/compiler/backend_vocabulary/jvm_types` gives for
    * it, since α-equivalent terms are one term, and a text read outside the
    * source trees reaches no library.
    */
  def jvmType(term: String, name: JvmTypeName): String =
    val alternatives = JvmTypeName.values.indices.map(alternative => s"λalternative_$alternative. ").mkString
    s"(λs. s $term (${alternatives}alternative_${name.ordinal}))"

  /** The library's Scott list of the items' texts, nil `λn. λc. n` and a
    * cell `λn. λc. c h t` (`Literals.textTerm`'s encoding), closed, so that
    * it needs no import: a bracket is a CBOR array literal and no list of
    * terms.
    */
  def scottList(items: Vector[String]): String =
    items.foldRight("(λn. λc. n)")((item, tail) => s"(λn. λc. c ($item) $tail)")

  /** A member of `families`. */
  def family(term: String, arity: Int, constructors: Vector[String]): String =
    s"(λs. s $term ${natural(arity)} ${scottList(constructors)})"

  /** A member of `fields`, its criteria written by `parameter` and
    * `recursive`.
    */
  def constructorFields(term: String, constructor: String, criteria: Vector[String]): String =
    s"(λs. s $term $constructor ${scottList(criteria)})"

  /** The field criterion of the type's parameter of the index, the first
    * of the three constructors of `corpora/compiler/backend_vocabulary/field_criteria`
    * written closed.
    */
  def parameter(index: Int): String = s"(λparameter _ _. parameter ${natural(index)})"

  /** The field criterion of the type itself, the second constructor of
    * `field_criteria`, of no field.
    */
  val recursive: String = "(λ_ recursive _. recursive)"

  /** The binder of a contribution's group (`mixin`). */
  val groupBinder: String = "knowledge_group"

  /** The binder of a contribution's slot (`mixin`). */
  val slotBinder: String = "knowledge_slot"

  /** The fixed-width mixin of the slots' members, each member a
    * contribution `λ_ _ knowledge_group _. knowledge_group λ_ _ knowledge_slot _ … _. knowledge_slot (member)`,
    * each `_` before a group's or a slot's binders the mixin's self
    * (`KnowledgeSlot`), the slots in the order given, one contribution a
    * line, joined by `+`. Throws `IllegalArgumentException` when no slot has
    * a member, since a mixin of no contribution is top, which a text cannot
    * write without a path to the library's file, or when a member's text
    * holds a binder's name, which the binder would capture.
    */
  def mixin(slots: Vector[(KnowledgeSlot, Vector[Member])]): String =
    val written = slots.flatMap((slot, members) => members.map(slot -> _))
    if written.isEmpty then throw IllegalArgumentException("a knowledge text of no member: there is nothing to write")
    written
      .map { (slot, member) =>
        if member.text.contains(groupBinder) || member.text.contains(slotBinder) then
          throw IllegalArgumentException(s"the member ${member.text} holds the name of a contribution's binder")
        def binders(width: Int, chosen: Int, name: String): String =
          (0 until width).map(position => if position == chosen then name else "_").mkString(" ")
        val group = binders(KnowledgeSlot.width, slot.group, groupBinder)
        val position = binders(KnowledgeSlot.groupWidths(slot.group), slot.position, slotBinder)
        s"(λ_ $group. $groupBinder λ_ $position. $slotBinder (${member.text}))"
      }
      .mkString("  ", "\n+ ", "\n")
