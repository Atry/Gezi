package gezi.proofs

import io.bullet.borer.Dom
import io.bullet.borer.Json
import java.nio.charset.StandardCharsets

/** A component of a name of Lean's kernel: a string, or a number. */
enum NameComponent:
  case Text(value: String)
  case Number(value: BigInt)

/** A universe level of Lean's kernel, over the indices of its parts in
  * the export: `0` is the level zero, which every export holds without a
  * record.
  */
enum ExportLevel:
  case Successor(level: Int)
  case Maximum(first: Int, second: Int)
  case ImpredicativeMaximum(first: Int, second: Int)
  case Parameter(name: Int)

/** An expression of Lean's kernel that a certificate writes, over the
  * indices of its parts in the export, as the export's key: an export holds
  * each expression once (nanoda refuses a second copy). The kinds a
  * certificate never writes (binders, projections, `let`) are not keys,
  * and the closure's expressions of those kinds are never looked up.
  */
enum ExportExpression:
  case Constant(name: Int, levels: Vector[Int])
  case Application(function: Int, argument: Int)
  case NaturalLiteral(value: BigInt)
  case StringLiteral(value: String)
  case Sort(level: Int)

/** An export in the format of lean4export (version 3.1.0), as NDJSON
  * lines: the closure that lean4export wrote, then the records written
  * here, each name, level and expression once and numbered after the
  * closure's ([[RoundCertificates]]). A checker such as nanoda reads the lines in order.
  */
final case class LeanExport(
    names: Map[Vector[NameComponent], Int],
    levels: Map[ExportLevel, Int],
    expressions: Map[ExportExpression, Int],
    nextName: Int,
    nextLevel: Int,
    nextExpression: Int,
    written: Vector[String]
):

  /** The index of a name, its records written for its prefixes first. */
  def name(components: Vector[NameComponent]): (LeanExport, Int) =
    names.get(components) match
      case Some(index) => (this, index)
      case None =>
        val (withPrefix, prefix) = name(components.init)
        val record = components.last match
          case NameComponent.Text(value)   => s"""{"in":${withPrefix.nextName},"str":{"pre":$prefix,"str":${LeanExport.quoted(value)}}}"""
          case NameComponent.Number(value) => s"""{"in":${withPrefix.nextName},"num":{"i":$value,"pre":$prefix}}"""
        (
          withPrefix.copy(
            names = withPrefix.names.updated(components, withPrefix.nextName),
            nextName = withPrefix.nextName + 1,
            written = withPrefix.written :+ record
          ),
          withPrefix.nextName
        )

  /** The index of a dotted name of string components, `List.cons`. */
  def dottedName(dotted: String): (LeanExport, Int) =
    name(dotted.split('.').toVector.map(NameComponent.Text(_)))

  /** The index of a level. */
  def level(value: ExportLevel): (LeanExport, Int) =
    levels.get(value) match
      case Some(index) => (this, index)
      case None =>
        val body = value match
          case ExportLevel.Successor(level)                    => s""""succ":$level"""
          case ExportLevel.Maximum(first, second)              => s""""max":[$first,$second]"""
          case ExportLevel.ImpredicativeMaximum(first, second) => s""""imax":[$first,$second]"""
          case ExportLevel.Parameter(name)                     => s""""param":$name"""
        (
          copy(
            levels = levels.updated(value, nextLevel),
            nextLevel = nextLevel + 1,
            written = written :+ s"""{"il":$nextLevel,$body}"""
          ),
          nextLevel
        )

  /** The index of an expression. */
  def expression(value: ExportExpression): (LeanExport, Int) =
    expressions.get(value) match
      case Some(index) => (this, index)
      case None =>
        val body = value match
          case ExportExpression.Constant(name, levels)       => s""""const":{"name":$name,"us":[${levels.mkString(",")}]}"""
          case ExportExpression.Application(function, argument) => s""""app":{"arg":$argument,"fn":$function}"""
          case ExportExpression.NaturalLiteral(value)        => s""""natVal":"$value""""
          case ExportExpression.StringLiteral(value)         => s""""strVal":${LeanExport.quoted(value)}"""
          case ExportExpression.Sort(level)                  => s""""sort":$level"""
        (
          copy(
            expressions = expressions.updated(value, nextExpression),
            nextExpression = nextExpression + 1,
            written = written :+ s"""{"ie":$nextExpression,$body}"""
          ),
          nextExpression
        )

  /** The index of the constant `dotted` at the level zero for each of its
    * `levelParameters` universe parameters: every constant a certificate
    * names is used at `Type`, or is no polymorphic constant.
    */
  def constant(dotted: String, levelParameters: Int): (LeanExport, Int) =
    val (named, nameIndex) = dottedName(dotted)
    named.expression(ExportExpression.Constant(nameIndex, Vector.fill(levelParameters)(0)))

  /** The index of the constant of the string components `components`, at
    * the level zero for each of its `levelParameters` universe parameters:
    * a component may hold a dot, as a name Lean writes between guillemets.
    */
  def constantNamed(components: Vector[String], levelParameters: Int): (LeanExport, Int) =
    val (named, nameIndex) = name(components.map(NameComponent.Text(_)))
    named.expression(ExportExpression.Constant(nameIndex, Vector.fill(levelParameters)(0)))

  /** The index of `function` applied to `arguments` in order. */
  def applied(function: Int, arguments: Vector[Int]): (LeanExport, Int) =
    arguments.foldLeft((this, function)) { case ((current, applied), argument) =>
      current.expression(ExportExpression.Application(applied, argument))
    }

  /** The index of the constant `dotted` applied to `arguments`. */
  def constantApplied(dotted: String, levelParameters: Int, arguments: Vector[Int]): (LeanExport, Int) =
    val (withConstant, head) = constant(dotted, levelParameters)
    withConstant.applied(head, arguments)

  /** The definition `dotted : type := value`, with no universe parameter,
    * unfolded by the checker as a regular definition of height 1.
    */
  def definition(dotted: String, typeExpression: Int, value: Int): LeanExport =
    val (named, nameIndex) = dottedName(dotted)
    named.copy(written =
      named.written :+ s"""{"def":{"all":[$nameIndex],"hints":{"regular":1},"levelParams":[],"name":$nameIndex,"safety":"safe","type":$typeExpression,"value":$value}}"""
    )

  /** The theorem `dotted : type := value`, with no universe parameter. */
  def theorem(dotted: String, typeExpression: Int, value: Int): LeanExport =
    val (named, nameIndex) = dottedName(dotted)
    named.copy(written =
      named.written :+ s"""{"thm":{"all":[$nameIndex],"levelParams":[],"name":$nameIndex,"type":$typeExpression,"value":$value}}"""
    )

object LeanExport:

  /** The export that continues `closure`, the lines lean4export wrote:
    * its names, levels and the expressions of the kinds a certificate
    * writes are keyed, so that a record written after them reuses theirs.
    * Throws `IllegalArgumentException` on a line that is no record of the
    * format.
    */
  def continuing(closure: Vector[String]): LeanExport =
    val empty = LeanExport(Map(Vector.empty -> 0), Map.empty, Map.empty, 1, 1, 0, closure)
    val (continued, _) = closure.foldLeft((empty, Map(0 -> Vector.empty[NameComponent]))) { case ((current, nameOfIndex), line) =>
      continuedBy(current, nameOfIndex, line)
    }
    continued

  /** The export and its names by index after one more line of the closure. */
  private def continuedBy(
      current: LeanExport,
      nameOfIndex: Map[Int, Vector[NameComponent]],
      line: String
  ): (LeanExport, Map[Int, Vector[NameComponent]]) =
      val fields = recordFields(line)
      if fields.contains("in") then
        val index = integer(fields("in"))
        val (prefixField, component) =
          fields.get("str") match
            case Some(record) =>
              val parts = objectFields(record)
              (parts("pre"), NameComponent.Text(text(parts("str"))))
            case None =>
              val parts = objectFields(fields("num"))
              (parts("pre"), NameComponent.Number(natural(parts("i"))))
        val prefixIndex = integer(prefixField)
        val prefix = nameOfIndex.getOrElse(
          prefixIndex,
          throw IllegalArgumentException(s"the name $index names an unknown prefix $prefixIndex")
        )
        (
          current.copy(names = current.names.updated(prefix :+ component, index), nextName = math.max(current.nextName, index + 1)),
          nameOfIndex.updated(index, prefix :+ component)
        )
      else if fields.contains("il") then
        val index = integer(fields("il"))
        val level =
          if fields.contains("succ") then ExportLevel.Successor(integer(fields("succ")))
          else if fields.contains("max") then
            val (first, second) = pair(fields("max"))
            ExportLevel.Maximum(first, second)
          else if fields.contains("imax") then
            val (first, second) = pair(fields("imax"))
            ExportLevel.ImpredicativeMaximum(first, second)
          else ExportLevel.Parameter(integer(fields("param")))
        (current.copy(levels = current.levels.updated(level, index), nextLevel = math.max(current.nextLevel, index + 1)), nameOfIndex)
      else if fields.contains("ie") then
        val index = integer(fields("ie"))
        val keyed: Option[ExportExpression] =
          if fields.contains("const") then
            val parts = objectFields(fields("const"))
            Some(ExportExpression.Constant(integer(parts("name")), integers(parts("us"))))
          else if fields.contains("app") then
            val parts = objectFields(fields("app"))
            Some(ExportExpression.Application(integer(parts("fn")), integer(parts("arg"))))
          else if fields.contains("natVal") then Some(ExportExpression.NaturalLiteral(BigInt(text(fields("natVal")))))
          else if fields.contains("strVal") then Some(ExportExpression.StringLiteral(text(fields("strVal"))))
          else if fields.contains("sort") then Some(ExportExpression.Sort(integer(fields("sort"))))
          else None
        val withExpression = keyed.fold(current)(key => current.copy(expressions = current.expressions.updated(key, index)))
        (withExpression.copy(nextExpression = math.max(withExpression.nextExpression, index + 1)), nameOfIndex)
      else (current, nameOfIndex)

  /** A string as a JSON string literal. */
  def quoted(value: String): String =
    val escaped = value.flatMap {
      case '"'                       => "\\\""
      case '\\'                      => "\\\\"
      case character if character < ' ' => f"\\u${character.toInt}%04x"
      case character                 => character.toString
    }
    s""""$escaped""""

  private def recordFields(line: String): Map[String, Dom.Element] =
    objectFields(Json.decode(line.getBytes(StandardCharsets.UTF_8)).to[Dom.Element].value)

  private def objectFields(element: Dom.Element): Map[String, Dom.Element] = element match
    case map: Dom.MapElem =>
      map.toMap.collect { case (Dom.StringElem(key), value) => key -> value }
    case other => throw IllegalArgumentException(s"an export record holds $other where an object stands")

  private def integer(element: Dom.Element): Int = element match
    case Dom.IntElem(value)  => value
    case Dom.LongElem(value) => Math.toIntExact(value)
    case other               => throw IllegalArgumentException(s"an export record holds $other where an index stands")

  private def natural(element: Dom.Element): BigInt = element match
    case Dom.IntElem(value)  => BigInt(value)
    case Dom.LongElem(value) => BigInt(value)
    case Dom.StringElem(value) => BigInt(value)
    case other               => throw IllegalArgumentException(s"an export record holds $other where a number stands")

  private def integers(element: Dom.Element): Vector[Int] = element match
    case array: Dom.ArrayElem => array.elems.toVector.map(integer)
    case other                => throw IllegalArgumentException(s"an export record holds $other where a list stands")

  private def pair(element: Dom.Element): (Int, Int) = integers(element) match
    case Vector(first, second) => (first, second)
    case parts                 => throw IllegalArgumentException(s"an export level holds ${parts.size} parts where two stand")

  private def text(element: Dom.Element): String = element match
    case Dom.StringElem(value) => value
    case other                 => throw IllegalArgumentException(s"an export record holds $other where a string stands")
