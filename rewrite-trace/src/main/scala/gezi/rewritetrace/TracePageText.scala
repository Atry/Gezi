package gezi.rewritetrace

/** The HTML of a player's page, with the trace embedded in it: the text of the term the
  * trace starts from (`TraceStart`) and the trace's text, each embedded in a
  * `<script type="application/x-lambdalattice">` told apart by its `data-role`,
  * `start` or `trace` (a trace holds no start, and the page embeds both), and the
  * player's script and the style sheets referred to by relative paths, so
  * that the page opened from `file://` plays. It is here, beside the trace's
  * text, so that the writer of traces on the JVM writes the page beside each
  * trace and the player (`trace-player`, Scala.js) reads it by
  * the same names.
  */
object TracePageText:

  /** The media type of the embedded texts. */
  val traceType: String = "application/x-lambdalattice"

  /** The `data-role` of the embedded text of the start. */
  val startRole: String = "start"

  /** The `data-role` of the embedded text of the trace. */
  val traceRole: String = "trace"

  /** The id of the element the player is drawn into. */
  val containerIdentifier: String = "trace-player"

  /** The directory, relative to a page `playerPage` writes, that holds the
    * player's script and style sheets: the sbt task
    * `trace-player/demonstrationPage` puts them there, and a directory of
    * pages (a judge's output, a site) holds one copy of it beside them. The
    * layout is one fixed layout, so that the
    * writer of a page needs to be told nothing about where the player is.
    */
  val playerDirectory: String = "trace-player"

  /** The player's script, relative to the page. */
  val playerScript: String = s"$playerDirectory/main.js"

  /** The player's style sheets, relative to the page: Bootstrap and
    * Bootstrap Icons from their webjars (under `lib/`, as sbt-web lays them
    * out) and the player's own.
    */
  val playerStyleSheets: Vector[String] = Vector(
    s"$playerDirectory/lib/bootstrap/dist/css/bootstrap.min.css",
    s"$playerDirectory/lib/bootstrap-icons/font/bootstrap-icons.min.css",
    s"$playerDirectory/player.css"
  )

  /** `page` with the player at `playerDirectory`. */
  def playerPage(title: String, start: String, trace: String): String =
    page(title, start, trace, playerScript, playerStyleSheets)

  /** The page of the title (written as text), the start's text, the trace's
    * text, the player's script and the style sheets, the paths relative to
    * the page. A text
    * that holds `</script`, in any case, would end its script element; it is
    * not escaped but rejected, by `IllegalArgumentException`, as
    * is a path or a title that holds a character HTML would read as markup.
    */
  def page(title: String, start: String, trace: String, script: String, styleSheets: Vector[String]): String =
    (script +: styleSheets).foreach(attribute =>
      require(!attribute.exists("<>&\"".contains(_)), s"'$attribute' holds a character HTML reads as markup")
    )
    document(title, start, trace, styleSheets.map(path => s"""<link rel="stylesheet" href="$path">"""), s"""<script src="$script"></script>""")

  /** The page with the player's script and style sheets in it, not linked:
    * a page that loads nothing else, for a place that serves it where a
    * request it made would carry no credentials, such as Jupyter Server's
    * `/files/`, which serves an HTML file under the policy
    * `sandbox allow-scripts`, so that the page's origin is opaque and the
    * requests for a linked player are answered by the login's redirect
    * (measured 2026-11-19 with Jupyter Server under JupyterLab 4.4.1; the
    * kernel's `CellTraces`). A style sheet that loads a file must have it as
    * a `data:` URL. A script that holds `</script`, or a style sheet that holds
    * `</style`, in any case, is rejected by `IllegalArgumentException`, as in
    * `page`.
    */
  def selfContainedPage(title: String, start: String, trace: String, script: String, styleSheets: Vector[String]): String =
    require(!script.toLowerCase.contains("</script"), "the player's script holds </script")
    styleSheets.foreach(sheet => require(!sheet.toLowerCase.contains("</style"), "a style sheet holds </style"))
    document(title, start, trace, styleSheets.map(sheet => s"<style>$sheet</style>"), s"<script>$script</script>")

  /** The page of the title (written as text), the start's text and the
    * trace's text, with the elements of the head that bring the style sheets
    * and the element that brings the player's script, which the callers
    * check.
    */
  private def document(title: String, start: String, trace: String, styles: Vector[String], scriptElement: String): String =
    require(!start.toLowerCase.contains("</script"), "the start's text holds </script")
    require(!trace.toLowerCase.contains("</script"), "the trace's text holds </script")
    require(!title.exists("<>&\"".contains(_)), s"'$title' holds a character HTML reads as markup")
    (Vector(
      "<!doctype html>",
      """<html lang="en">""",
      "<head>",
      """<meta charset="utf-8">""",
      """<meta name="viewport" content="width=device-width, initial-scale=1">""",
      s"<title>$title</title>"
    ) ++ styles ++ Vector(
      "</head>",
      "<body>",
      s"""<main id="$containerIdentifier"></main>""",
      s"""<script type="$traceType" data-role="$startRole">$start</script>""",
      s"""<script type="$traceType" data-role="$traceRole">$trace</script>""",
      scriptElement,
      "</body>",
      "</html>"
    )).mkString("", "\n", "\n")

  /** The page that lists the player's pages of a directory of them, such as
    * the top of a judge's output directory, which lists its points: the title, then for each group, such as a point, its name and a
    * link to each of its pages, by its path relative to this page, the link's
    * text the path. Its style sheets are the player's, at `playerDirectory`
    * beside this page. A title, a name or a path that holds a character HTML
    * would read as markup is rejected by `IllegalArgumentException`.
    */
  def indexPage(title: String, groups: Vector[(String, Vector[String])]): String =
    (title +: groups.flatMap((name, pages) => name +: pages)).foreach(text =>
      require(!text.exists("<>&\"".contains(_)), s"'$text' holds a character HTML reads as markup")
    )
    val links = playerStyleSheets.map(path => s"""<link rel="stylesheet" href="$path">""")
    val listed = groups.flatMap((name, pages) =>
      Vector(s"""<h2 class="h5 mt-4">$name</h2>""", """<ul class="list-unstyled">""") ++
        pages.map(page => s"""<li><a href="$page">$page</a></li>""") :+ "</ul>"
    )
    (Vector(
      "<!doctype html>",
      """<html lang="en">""",
      "<head>",
      """<meta charset="utf-8">""",
      """<meta name="viewport" content="width=device-width, initial-scale=1">""",
      s"<title>$title</title>"
    ) ++ links ++ Vector(
      "</head>",
      "<body>",
      """<main class="container my-4">""",
      s"""<h1 class="h3">$title</h1>"""
    ) ++ listed ++ Vector(
      "</main>",
      "</body>",
      "</html>"
    )).mkString("", "\n", "\n")
