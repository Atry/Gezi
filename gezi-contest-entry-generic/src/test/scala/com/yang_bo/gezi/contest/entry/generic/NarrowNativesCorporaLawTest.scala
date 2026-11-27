package com.yang_bo.gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.NativeArgument
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.jit.NativeName
import com.yang_bo.gezi.jit.NativeValue
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTables
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NormalForms
import com.yang_bo.gezi.weakhead.ReadingState

private given narrowNativesCorporaLawTestNoFacts: NoFacts.type = NoFacts

/** The law of the natives the boolean branch's programs call: on generated
  * canonical binary naturals, `wren_binary_increment` gives the natural that
  * the library's `merge_binary_increment` applied to the operand reads as under
  * tabling(weak_head), and `wren_binary_equality` the boolean, the library's
  * `true` or `false`, that `merge_binary_equality` applied to the two operands
  * reads as, compared by their normal forms. Its purpose is to catch a native
  * that computes something else than the library file it stands for (an
  * increment off by one at a carry, an equality that answers the reverse),
  * which a narrow block would then compute in place of the definition.
  */
class NarrowNativesCorporaLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The problem generators' library terms (`TermTables.problemLibraryTerms`).
    */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(buildRoot, TermTables.problemLibraryTerms, Expansions.none)
      ._1

  private def term(name: String): Configured[NoFacts.type] =
    terms.getOrElse(
      name,
      throw IllegalArgumentException(
        s"${TermTables.problemLibraryTerms.file} has no member $name"
      )
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms)

  /** The steps within which the reference reads a program: the most these laws'
    * programs took, measured 2026-11-21 over a run of the property, was 1,617
    * steps (operands of up to 12 binary digits); a reading that does not finish
    * within the limit fails the law.
    */
  private val referenceLimit: Long = 10000

  /** tabling(weak_head)'s normal forms of the closed term; none when the
    * reading does not finish.
    */
  private def referenceNormalForms(
      program: Configured[NoFacts.type]
  ): Option[Vector[Configured[NoFacts.type]]] =
    NormalForms
      .normalForms(Mode.TablingWeakHead, program)
      .result(
        ReadingState.knowingTop(
          referenceLimit,
          com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
        )
      ) match
      case Computed.Done(normalForms, _) => Some(normalForms)
      case Computed.Stopped(_)           => None

  /** The canonical binary numeral of the value, of the library's binary_zero,
    * binary_even and binary_odd.
    */
  private def numeral(value: BigInt): Configured[NoFacts.type] =
    if value == 0 then term("binary_zero")
    else
      NoFacts.application(
        term(if value.testBit(0) then "binary_odd" else "binary_even"),
        numeral(value >> 1)
      )

  /** The native of the name in the standard set, applied to the naturals. */
  private def native(name: String, operands: Vector[BigInt]): NativeValue =
    NativeBackend.standard
      .natives(NativeName.Function(name))
      .implementation(
        operands
          .map(operand => NativeArgument.Represented(BinaryNatural(operand)))
      )

  /** A canonical binary natural, up to 12 binary digits. */
  private val natural: Gen[BigInt] =
    Gen.long(Range.linear(0L, 4095L)).map(BigInt(_))

  stoppableProperty(
    "wren_binary_increment and wren_binary_equality answer as their library files read"
  ) { _ =>
    for
      first <- natural.forAll
      drawn <- natural.forAll
      // Half the time the operands are equal, so that equality is checked where it holds.
      repeated <- Gen.boolean.forAll
    yield
      val second = if repeated then first else drawn
      val incremented = native("wren_binary_increment", Vector(first)) match
        case BinaryNatural(value) => Some(numeral(value))
        case _                    => None
      val equal = native("wren_binary_equality", Vector(first, second)) match
        case NativeValue.Truth(value) =>
          Some(term(if value then "true" else "false"))
        case _ => None
      Result
        .all(
          List(
            Result
              .assert(incremented.nonEmpty)
              .log("wren_binary_increment gave no natural"),
            Result
              .diff(
                incremented.flatMap(referenceNormalForms),
                referenceNormalForms(
                  NoFacts
                    .application(term("merge_binary_increment"), numeral(first))
                )
              )(_ == _)
              .log("the increment's and the library's"),
            Result
              .assert(equal.nonEmpty)
              .log("wren_binary_equality gave no boolean"),
            Result
              .diff(
                equal.flatMap(referenceNormalForms),
                referenceNormalForms(
                  NoFacts.application(
                    NoFacts.application(
                      term("merge_binary_equality"),
                      numeral(first)
                    ),
                    numeral(second)
                  )
                )
              )(_ == _)
              .log("the equality's and the library's")
          )
        )
        .log(s"the operands $first and $second")
  }
