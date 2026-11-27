package gezi.standardlibrary

import java.nio.file.Files
import java.nio.file.Path
import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.ir.Code
import gezi.ir.Hole
import scala.concurrent.Future
import scala.jdk.StreamConverters.*
import gezi.ir.{Configured, NativeSpecializer}

/** The finite terms of the IR as the Lean package `gezi/lean` writes them, and
  * the runner of its `lake`: the port of `gezi/tests/lean_finite_terms.pl` and
  * of the Lean side of `defunctionalization_agreement.plt`. A finite term (D1
  * of `lean/README.md`, "Design decisions") is an instruction with every
  * instruction under it written out by its layer. The tests need `lake` on the
  * path.
  */
object LeanFiniteTerms:

  /** The Lean package. */
  val leanDirectory: Path = LibraryFiles.buildRoot.resolve("lean")

  /** The finite term of an instruction, every instruction under it written out
    * by its layer, in the Prolog syntax of the front end's instructions, as
    * Lean's printer `finiteText` writes it. Throws `IllegalArgumentException`
    * for an opaque instruction under it, whose layer is not known.
    */
  def finiteText[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C): String = instruction.layer match
    case gezi.ir.Thunk(code, holes, fillings) =>
      s"thunk(${codeText(code)},${holesText(holes)},[${fillings.map(finiteText).mkString(",")}])"
    case gezi.ir.Apply(function, argument) =>
      s"apply(${finiteText(function)},${finiteText(argument)})"
    case gezi.ir.Choice(left, right) =>
      s"choice(${finiteText(left)},${finiteText(right)})"
    case gezi.ir.Parallel(left, right) =>
      s"parallel(${finiteText(left)},${finiteText(right)})"
    case opaque =>
      throw IllegalArgumentException(
        s"a finite term holds no opaque instruction, here $opaque"
      )

  private def codeText(code: Code): String = code match
    case Code.Slot(index)               => s"slot($index)"
    case Code.Apply(function, argument) =>
      s"apply(${codeText(function)},${codeText(argument)})"
    case Code.Thunk(inner, holes, fillings) =>
      s"thunk(${codeText(inner)},${holesText(holes)},[${fillings.map(codeText).mkString(",")}])"
    case Code.Choice(left, right) =>
      s"choice(${codeText(left)},${codeText(right)})"
    case Code.Parallel(left, right) =>
      s"parallel(${codeText(left)},${codeText(right)})"

  private def holesText(holes: Vector[Hole]): String =
    holes
      .map {
        case Hole.Bound(slot) => slot.toString
        case Hole.Ignored     => "ignored"
      }
      .mkString("[", ",", "]")

  /** The finite term of an instruction as a Lean term of `Ir.FiniteTerm`. */
  def finiteLeanText[C <: NativeSpecializer & Singleton](
      instruction: Configured[C]
  )(using C): String = instruction.layer match
    case gezi.ir.Thunk(code, holes, fillings) =>
      s"(.thunk ${codeLeanText(code)} ${holesLeanText(holes)} [${fillings.map(finiteLeanText).mkString(", ")}])"
    case gezi.ir.Apply(function, argument) =>
      s"(.apply ${finiteLeanText(function)} ${finiteLeanText(argument)})"
    case gezi.ir.Choice(left, right) =>
      s"(.choice ${finiteLeanText(left)} ${finiteLeanText(right)})"
    case gezi.ir.Parallel(left, right) =>
      s"(.parallel ${finiteLeanText(left)} ${finiteLeanText(right)})"
    case opaque =>
      throw IllegalArgumentException(
        s"a finite term holds no opaque instruction, here $opaque"
      )

  /** A code as a Lean term of `Ir.Code`. */
  def codeLeanText(code: Code): String = code match
    case Code.Slot(index)               => s"(.slot $index)"
    case Code.Apply(function, argument) =>
      s"(.apply ${codeLeanText(function)} ${codeLeanText(argument)})"
    case Code.Thunk(inner, holes, fillings) =>
      s"(.thunk ${codeLeanText(inner)} ${holesLeanText(holes)} [${fillings.map(codeLeanText).mkString(", ")}])"
    case Code.Choice(left, right) =>
      s"(.choice ${codeLeanText(left)} ${codeLeanText(right)})"
    case Code.Parallel(left, right) =>
      s"(.parallel ${codeLeanText(left)} ${codeLeanText(right)})"

  /** Holes as a Lean term of `List Ir.Hole`. */
  def holesLeanText(holes: Vector[Hole]): String =
    holes
      .map {
        case Hole.Bound(slot) => s"(.slot $slot)"
        case Hole.Ignored     => ".ignored"
      }
      .mkString("[", ", ", "]")

  /** A source program as a Lean term of `Defunctionalization.Program`, a
    * constant naming the Lean definition of its instruction.
    */
  def sourceProgramLeanText[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]],
      identifiers: Map[Configured[C], String]
  )(using C): String = term match
    case DeBruijnTerm.Variable(index) => s"(.boundVariable $index)"
    case DeBruijnTerm.Lambda(body)    =>
      s"(.abstraction ${sourceProgramLeanText(body, identifiers)})"
    case DeBruijnTerm.Apply(function, argument) =>
      s"(.application ${sourceProgramLeanText(function, identifiers)} ${sourceProgramLeanText(argument, identifiers)})"
    case DeBruijnTerm.Choice(left, right) =>
      s"(.choice ${sourceProgramLeanText(left, identifiers)} ${sourceProgramLeanText(right, identifiers)})"
    case DeBruijnTerm.Parallel(left, right) =>
      s"(.parallel ${sourceProgramLeanText(left, identifiers)} ${sourceProgramLeanText(right, identifiers)})"
    case DeBruijnTerm.Constant(instruction) =>
      s"(.constant ${identifiers(instruction)})"
    case DeBruijnTerm.Free(name) =>
      throw IllegalArgumentException(
        s"a source program names its library terms by instruction, here $name"
      )

  /** A term of the calculus with no constant, as a Lean term of
    * `Semantics.Term`.
    */
  def calculusLeanText(term: DeBruijnTerm): String = term match
    case DeBruijnTerm.Variable(index) => s"(.boundVariable $index)"
    case DeBruijnTerm.Lambda(body)    =>
      s"(.abstraction ${calculusLeanText(body)})"
    case DeBruijnTerm.Apply(function, argument) =>
      s"(.application ${calculusLeanText(function)} ${calculusLeanText(argument)})"
    case DeBruijnTerm.Choice(left, right) =>
      s"(.choice ${calculusLeanText(left)} ${calculusLeanText(right)})"
    case DeBruijnTerm.Parallel(left, right) =>
      s"(.parallel ${calculusLeanText(left)} ${calculusLeanText(right)})"
    case other =>
      throw IllegalArgumentException(s"$other is no term of the calculus")

  /** The base of an identifier in lower camel case. */
  def lowerCamelCase(base: String): String =
    base.split('_').toVector match
      case first +: words =>
        first + words
          .map(word => word.take(1).toUpperCase + word.drop(1))
          .mkString
      case _ => base

  /** The Lean definitions that print a finite term in the Prolog syntax of the
    * front end's instructions, a hole `.slot N` as N.
    */
  val printer: String =
    """mutual
      |partial def codeText : Code → String
      |  | .slot index => s!"slot({index})"
      |  | .apply function argument => s!"apply({codeText function},{codeText argument})"
      |  | .thunk code holes fillings =>
      |      s!"thunk({codeText code},{holesText holes},[{",".intercalate (fillings.map codeText)}])"
      |  | .choice left right => s!"choice({codeText left},{codeText right})"
      |  | .parallel left right => s!"parallel({codeText left},{codeText right})"
      |partial def holesText (holes : List Hole) : String :=
      |  "[" ++ ",".intercalate (holes.map fun | .slot index => toString index | .ignored => "ignored")
      |    ++ "]"
      |end
      |
      |partial def finiteText : FiniteTerm → String
      |  | .thunk code holes fillings =>
      |      s!"thunk({codeText code},{holesText holes},[{",".intercalate (fillings.map finiteText)}])"
      |  | .apply function argument => s!"apply({finiteText function},{finiteText argument})"
      |  | .choice left right => s!"choice({finiteText left},{finiteText right})"
      |  | .parallel left right => s!"parallel({finiteText left},{finiteText right})"
      |""".stripMargin

  /** The non-empty lines the program prints, run by `lake env lean` after the
    * printer, in a file that imports the module of the package, built first.
    * Each `lake` is stopped when `stopped` completes (`lakeOutput`).
    */
  def leanLines(
      module: String,
      program: String,
      stopped: Future[Unit]
  ): Vector[String] =
    lakeOutput(Seq("build", module), stopped)
    val file = Files.createTempFile("defunctionalization_agreement", ".lean")
    // Joined, not written with a margin: the printer and the program hold
    // lines that start with `|`, which a margin would strip.
    val text = Vector(
      s"import $module",
      "",
      "open LambdaJit LambdaJit.Semantics LambdaJit.Defunctionalization",
      "",
      // A marker's code, spelled as a tag, a partial
      // function of a literal applied to the literal's bits, nests about 105 applications; at Lean's default of
      // 512 the programs' elaboration reached the maximum recursion depth (measured 2026-11-19,
      // DefunctionalizationAgreementTest, three of its five tests), as LeanStatements' header records.
      "set_option maxRecDepth 1024",
      "",
      printer,
      program
    ).mkString("\n")
    Files.writeString(file, text)
    val output =
      try lakeOutput(Seq("env", "lean", file.toString), stopped)
      finally Files.delete(file)
    output.lines.toScala(Vector).filter(_.nonEmpty)

  /** What `lake` with the arguments writes on its standard output, run in the
    * package (`LeanProcesses.lakeOutput`).
    */
  def lakeOutput(arguments: Seq[String], stopped: Future[Unit]): String =
    LeanProcesses.lakeOutput(leanDirectory, arguments, stopped)
