package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.net.URI
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.ChoiceSpine
import gezi.ir.Configured
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts

/** `Defunctionalization.mixinInstruction` against the general conversion of
  * the same term. Its purpose is to catch a slot numbered differently from
  * the conversion's, which would make one term two instructions.
  */
class MixinInstructionLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  /** Keys, each with an entry drawn from few, so that members share entries. */
  private val keyedEntries: Gen[Vector[(Literal, NoFactsTerm)]] =
    val member =
      for
        key <- Gen.string(Gen.alphaNum, Range.linear(0, 6))
        entry <- Gen.int(Range.constant(0, 2))
      yield Literal.text(key) -> NoFacts.uri(URI.create(s"file:///mixin-law/e$entry"))
    member.list(Range.linear(2, 6)).map(_.toVector)

  /** `λd1. … λdn. (λ"k1". U1 d1 … dn) + … + (λ"kp". Up d1 … dn)`. */
  private def written(members: Vector[(Literal, NoFactsTerm)], selves: Int): DeBruijnTermOf[NoFactsTerm] =
    val partialFunctions = members.map((literal, entry) =>
      val applied = (selves - 1 to 0 by -1).foldLeft(DeBruijnTerm.Constant(entry): DeBruijnTermOf[NoFactsTerm])((function, index) =>
        DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(index))
      )
      Literals.partialFunction(literal, applied)
    )
    val body = ChoiceSpine.nested[DeBruijnTermOf[NoFactsTerm]](partialFunctions, DeBruijnTerm.Choice(_, _))
    (1 to selves).foldLeft(body)((inner, _) => DeBruijnTerm.Lambda(inner))

  property("a mixin built from its keys is the instruction the conversion gives") {
    for
      members <- keyedEntries.forAll
      selves <- Gen.int(Range.linear(1, 12)).forAll
    yield
      Result.diff(Defunctionalization.mixinInstruction[NoFacts.type](members, selves), Defunctionalization.thunkInstruction[NoFacts.type](written(members, selves)))(Configured.same(_, _))
  }
