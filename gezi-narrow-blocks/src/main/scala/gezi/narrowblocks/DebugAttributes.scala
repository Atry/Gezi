package gezi.narrowblocks

import java.net.URI
import gezi.locations.Location
import gezi.locations.SourceMap

/** Whether a class of narrow blocks is given the debugging attributes of the
  * places its blocks come from, and from what: the backend can write the source
  * locations into the bytecode it generates, and an option turns that off.
  * Locations are for people and tools: no block's computation reads them, and
  * the methods' instructions are the same with or without them.
  */
enum DebugAttributes:

  /** No `SourceFile`, `LineNumberTable` or `SourceDebugExtension`. */
  case Omitted

  /** The attributes of the blocks' places: the map of each block root's
    * occurrence, in the blocks' order (`NarrowBlockCompilation.locatedBlocks`),
    * and the text of each file a location names, in which its lines are
    * counted.
    */
  case Written(rootMaps: Vector[SourceMap], texts: Map[URI, String])

/** The lines a class of blocks is given (`DebugAttributes.lines`): the
  * `SourceFile` it names, the line at the start of each block's method, in the
  * blocks' order, none for a block with no place, and, when the blocks come
  * from several files, the JSR-45 source map (`SourceDebugExtension`) that
  * reads each of the class's lines as a line of its file, the class's lines
  * then being numbered 1 on in the order first met.
  */
final case class ClassLines(
    sourceFile: String,
    blockLines: Vector[Option[Int]],
    sourceMap: Option[String]
)

object DebugAttributes:

  /** The name of the stratum the source map defines and makes the default
    * (JSR-45, "Debugging Support for Other Languages", section 3.3).
    */
  val stratum: String = "Lambdalattice"

  /** The lines of the class of the blocks, none when the attributes are omitted
    * or no block has a place in a file of the texts. A block's place is the
    * least, by file and line, of its root's locations (`sourceLine`). Throws
    * `IllegalArgumentException` for maps of another number than the blocks.
    */
  def lines(debug: DebugAttributes, blocks: Int): Option[ClassLines] =
    debug match
      case Omitted                  => None
      case Written(rootMaps, texts) =>
        require(
          rootMaps.size == blocks,
          s"${rootMaps.size} maps of $blocks blocks"
        )
        val placed = rootMaps.map(map =>
          map.locations
            .flatMap(sourceLine(_, texts))
            .minByOption((uri, line) => (uri.toString, line))
        )
        val files = placed.flatten.map(_._1).distinct
        files.headOption.map(first =>
          if files.size == 1 then
            ClassLines(fileName(first), placed.map(_.map(_._2)), None)
          else
            val outputLines = placed.flatten.distinct.zipWithIndex
              .map((place, index) => place -> (index + 1))
              .toMap
            val fileIdentifiers =
              files.zipWithIndex.map((file, index) => file -> (index + 1)).toMap
            val sourceFile = fileName(first)
            val written =
              Vector("SMAP", sourceFile, stratum, s"*S $stratum", "*F") ++
                files.flatMap(file =>
                  Vector(
                    s"+ ${fileIdentifiers(file)} ${fileName(file)}",
                    file.getPath
                  )
                ) ++
                ("*L" +: outputLines.toVector.sortBy(_._2).map {
                  case ((file, line), output) =>
                    s"$line#${fileIdentifiers(file)}:$output"
                }) :+
                "*E"
            ClassLines(
              sourceFile,
              placed.map(_.map(outputLines)),
              Some(written.mkString("", "\n", "\n"))
            )
        )

  /** The file and the line, from 1, of a location: a span's where its text is
    * given; a call's at its call site, where the program the call is written in
    * reads it; a rewrite's at the place it rewrote; none for a file whose text
    * is not given.
    */
  def sourceLine(
      location: Location,
      texts: Map[URI, String]
  ): Option[(URI, Int)] = location match
    case Location.Source(uri, span) =>
      texts.get(uri).map(text => (uri, lineOf(text, span.start)))
    case Location.Inlined(_, callSite) => sourceLine(callSite, texts)
    case Location.Rewritten(_, from)   => sourceLine(from, texts)

  /** The line, from 1, of the code point at the offset of the text: one more
    * than the line feeds before it. Throws `IllegalArgumentException` for an
    * offset beyond the text.
    */
  def lineOf(text: String, offset: Int): Int =
    @scala.annotation.tailrec
    def counted(index: Int, read: Int, lines: Int): Int =
      if read == offset then lines
      else
        require(
          index < text.length,
          s"the offset $offset is beyond the text's $read code points"
        )
        val codePoint = text.codePointAt(index)
        counted(
          index + Character.charCount(codePoint),
          read + 1,
          if codePoint == '\n' then lines + 1 else lines
        )
    counted(0, 0, 1)

  /** The last segment of the URI's path, the name `SourceFile` takes. */
  private def fileName(uri: URI): String =
    Option(uri.getPath)
      .flatMap(_.split('/').filter(_.nonEmpty).lastOption)
      .getOrElse(uri.toString)
