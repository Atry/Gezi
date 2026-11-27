package gezi.generatedinputs

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The lambdalattice text of a closed HOAS term: its de Bruijn term rendered by
  * `Lambdalattice.text`, so that the laws parsing this text check the printer
  * as well as the parser. A closed instruction in the term (`Term.closed`, such
  * as a library term read off a file by projection) is written out by the de
  * Bruijn term of its instruction (`Defunctionalization.instructionTerm`), so
  * that the text is closed and stands alone, naming no library term.
  */
object LambdalatticeText:

  /** The text of the term. */
  def text(term: Term): String =
    Lambdalattice.text(term.deBruijnTerm(Map.empty), Map.empty)

  /** The text of a term that holds closed terms of the configuration as
    * constants, each written out as its own term.
    */
  def textOver[C <: NativeSpecializer & Singleton](
      term: TermOf[Configured[C]]
  )(using C): String =
    Lambdalattice.text(
      closedInstructionsWrittenOut[C](term.deBruijnTerm(Map.empty)),
      Map.empty
    )

  /** The text with each space replaced by a piece of layout drawn from spaces,
    * line breaks, blank lines and `#` comments, so that a law sees layout as an
    * author writes it. The text is one `text` writes, whose spaces all stand
    * between tokens, since it holds no literal.
    */
  def withLayout(text: String): hedgehog.Gen[String] =
    val pieces = text.split(" ", -1).toVector
    hedgehog.Gen
      .element1(" ", "  ", "\n", "\n\n  ", " # a remark\n", "\n# a remark\n  ")
      .list(hedgehog.Range.singleton(pieces.size - 1))
      .map(layouts =>
        pieces.head + pieces.tail
          .zip(layouts)
          .map((piece, layout) => layout + piece)
          .mkString
      )

  /** The term with each closed instruction (`DeBruijnTerm.Constant`, the de
    * Bruijn term of a `Term.closed`) written out as its de Bruijn term, so that
    * a printer that has no name for a constant prints it: this object's text,
    * and the exchange format of contest-corpora's reference suites.
    */
  def closedInstructionsWrittenOut[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]]
  )(using C): DeBruijnTerm =
    inlined[C](term).result

  /** The term with each closed instruction written out as its de Bruijn term.
    * The instruction is closed, so its term goes under the binders around the
    * constant unshifted. Trampolined (`TailCalls`), so that a deep term, such
    * as the deep terms of `LambdalatticeTextLawTest`, takes no stack frame per
    * level.
    */
  private def inlined[C <: NativeSpecializer & Singleton](
      term: DeBruijnTermOf[Configured[C]]
  )(using C): TailRec[DeBruijnTerm] =
    term match
      case DeBruijnTerm.Constant(instruction) =>
        if instruction.opaque then
          throw IllegalArgumentException(
            s"an opaque instruction has no term to write out: $instruction"
          )
        tailcall(
          inlined[C](Defunctionalization.instructionTerm[C](instruction))
        )
      case DeBruijnTerm.Lambda(body) =>
        tailcall(inlined[C](body)).map(DeBruijnTerm.Lambda[Nothing](_))
      case DeBruijnTerm.Apply(function, argument) =>
        tailcall(inlined[C](function)).flatMap(left =>
          tailcall(inlined[C](argument))
            .map(DeBruijnTerm.Apply[Nothing](left, _))
        )
      case DeBruijnTerm.Choice(left, right) =>
        tailcall(inlined[C](left)).flatMap(first =>
          tailcall(inlined[C](right))
            .map(DeBruijnTerm.Choice[Nothing](first, _))
        )
      case DeBruijnTerm.Parallel(left, right) =>
        tailcall(inlined[C](left)).flatMap(first =>
          tailcall(inlined[C](right))
            .map(DeBruijnTerm.Parallel[Nothing](first, _))
        )
      case DeBruijnTerm.Variable(index) =>
        done(DeBruijnTerm.Variable[Nothing](index))
      case DeBruijnTerm.Free(name) => done(DeBruijnTerm.Free[Nothing](name))

/** The HOAS term of a closed de Bruijn term, so that a term read back from the
  * IR renders as lambdalattice text (`LambdalatticeText.text`). Recursive on
  * the term's depth: for the small terms of snapshots.
  */
object DeBruijnHoas:

  /** The HOAS term; throws `IllegalArgumentException` for a variable no
    * abstraction binds, for a constant and for a free name.
    */
  def term[K](deBruijn: DeBruijnTermOf[K]): Term =
    converted(deBruijn, List.empty)

  private def converted[K](
      deBruijn: DeBruijnTermOf[K],
      bound: List[Term]
  ): Term =
    import gezi.frontend.DeBruijnTerm
    deBruijn match
      case DeBruijnTerm.Variable(index) =>
        bound
          .lift(index)
          .getOrElse(
            throw IllegalArgumentException(s"no binder for the variable $index")
          )
      case DeBruijnTerm.Lambda(body) =>
        Term.λ(variable => converted(body, variable :: bound))
      case DeBruijnTerm.Apply(function, argument) =>
        converted(function, bound)(converted(argument, bound))
      // TODO: the cases of a constant and of a free name stood here. Their purpose: a constant became the library
      // name the map `names` gives its instruction, and a free name that name, both as Term.define. They named library
      // terms by Term.define, a free variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
      // Their replacement is the HOAS case of a
      // closed instruction, which takes the constant's instruction; the map `names` is removed with it. The deleted code:
      // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/generatedinputs/LambdalatticeText.scala.
      case DeBruijnTerm.Constant(constant) =>
        throw IllegalArgumentException(
          s"no HOAS term for the constant $constant: a closed term of a configuration has none"
        )
      case DeBruijnTerm.Free(name) =>
        throw IllegalArgumentException(
          s"no HOAS term for the free name $name: the case Term.Define is deleted"
        )
      case DeBruijnTerm.Choice(left, right) =>
        Term.choice(converted(left, bound), converted(right, bound))
      case DeBruijnTerm.Parallel(left, right) =>
        converted(left, bound) ∥ converted(right, bound)
