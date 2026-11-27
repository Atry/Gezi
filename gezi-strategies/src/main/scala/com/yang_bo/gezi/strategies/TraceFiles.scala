package com.yang_bo.gezi.strategies

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import com.yang_bo.gezi.rewritetrace.Trace
import com.yang_bo.gezi.rewritetrace.TracePageText
import com.yang_bo.gezi.rewritetrace.TraceStart
import com.yang_bo.gezi.rewritetrace.TraceText
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The files of a trace written beside an article: the trace's text,
  * `<name>.trace.lambdalattice` for the article `<name>.art`; the text of the
  * term it starts from, which the trace does not hold (`TraceStart`),
  * `<name>.trace.start.lambdalattice`; and the player's page of both,
  * `<name>.trace.html`, which embeds the two texts and loads the player from
  * the directory `trace-player/` beside it (`TracePageText.playerPage`). The
  * writers of articles, a schedule (`Schedule`) and an entry's lemma route,
  * write their traces through it.
  */
object TraceFiles:

  /** The trace file of the article: its name with `.art` replaced by
    * `.trace.lambdalattice`. Throws `IllegalArgumentException` for an article
    * whose name does not end in `.art`.
    */
  def traceFile(article: Path): Path =
    val name = article.getFileName.toString
    if !name.endsWith(".art") then
      throw IllegalArgumentException(s"the article $article is no .art file")
    article.resolveSibling(name.stripSuffix(".art") + ".trace.lambdalattice")

  /** The player's page of a trace file: its name with `.lambdalattice` replaced
    * by `.html`, beside it.
    */
  def pageFile(traceFile: Path): Path =
    traceFile.resolveSibling(
      traceFile.getFileName.toString.stripSuffix(".lambdalattice") + ".html"
    )

  /** The file of the start of a trace file: its name with `.lambdalattice`
    * replaced by `.start.lambdalattice`, beside it.
    */
  def startFile(traceFile: Path): Path =
    traceFile.resolveSibling(
      traceFile.getFileName.toString.stripSuffix(
        ".lambdalattice"
      ) + ".start.lambdalattice"
    )

  /** Writes the trace from the start to `traceFile(article)`, the start's text
    * (`TraceStart.written`, with no source) to `startFile` of it and the page
    * to `pageFile` of it.
    */
  def written[C <: NativeSpecializer & Singleton](
      article: Path,
      start: Configured[C],
      trace: Trace[C]
  )(using C, com.yang_bo.gezi.ir.StorageAccess): Unit =
    textWrittenAt(
      traceFile(article),
      TraceStart.written(start, None),
      TraceText.written(trace)
    )

  /** Writes the text of a trace (`TraceText.written`) to the file, whose name
    * ends in `.lambdalattice`, the text of its start (`TraceStart.written`) to
    * `startFile` of it, and the page of both to `pageFile` of it.
    */
  def textWrittenAt(file: Path, startText: String, traceText: String): Unit =
    Files.writeString(file, traceText, StandardCharsets.UTF_8)
    Files.writeString(startFile(file), startText, StandardCharsets.UTF_8)
    val page = pageFile(file)
    Files.writeString(
      page,
      TracePageText.playerPage(page.getFileName.toString, startText, traceText),
      StandardCharsets.UTF_8
    )
