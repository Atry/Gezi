package gezi.contest.entry.generic

import java.nio.file.Path
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions
import scala.util.Random

/** The generated hot sites of the hot ladder's iterated shape, over the
  * library terms of `TermTables.hotSiteTerms`, which `contest-entries-solo` types and
  * compiles to narrow blocks: what `CancelGraceLawTest` and
  * `CompilationPlaceLawTest` run. A site's draws happen inside the bodies of
  * `λ`, which run again each time the term is written, so a caller writes a
  * site once (`locallyNamelessTerm`) and uses that.
  *
  * @param terms
  *   the library terms, by their names in the fixture file
  */
final case class HotSites[C <: NativeSpecializer & Singleton](terms: Map[String, Configured[C]]):

  /** A term of the sites, a HOAS term whose constants are terms of `C`. */
  private type SiteTerm = TermOf[Configured[C]]

  private def term(key: String): SiteTerm = Term.closed(terms.getOrElse(key, throw IllegalArgumentException(s"no fixture member $key")))

  /** The binary numeral of the value, written with the site's bound
    * constructors (zero, even, odd), least significant digit outermost.
    */
  private def numeral(constructors: Vector[SiteTerm], value: BigInt): SiteTerm =
    if value == 0 then constructors(0)
    else if value.testBit(0) then constructors(2)(numeral(constructors, value >> 1))
    else constructors(1)(numeral(constructors, value >> 1))

  /** The iterated call of the hot ladder, `fixpoint` over a binary count. */
  private def iterate: SiteTerm =
    term("fixpoint")(λ(self => λ(n => λ(g => λ(s =>
      n(s)(λ(m => self(m)(g)(self(m)(g)(s))))(λ(m => g(self(m)(g)(self(m)(g)(s)))))
    )))))

  /** A site of `sites` iterated calls in the hot ladder's iterated shape, each of
    * a drawn count of `bits` binary digits and a drawn function of one to
    * three steps by the bound operations, the library's terms let bound as
    * the hot ladder's generator binds them.
    */
  def site(random: Random, sites: Int, bits: Int): SiteTerm =
    val libraryNames = HotSites.keys.dropRight(1).map(term)
    lets(libraryNames :+ iterate, Vector.empty, bound =>
      val constructors = bound.take(3)
      val operations = bound.slice(3, 7)
      (1 to sites).foldLeft(numeral(constructors, BigInt(bits, random))) { (state, _) =>
        val steps = 1 + random.nextInt(3)
        val function = λ(input =>
          (1 to steps).foldLeft(input)((value, _) =>
            operations(random.nextInt(operations.size))(value)(numeral(constructors, BigInt(8, random)))
          )
        )
        bound(7)(numeral(constructors, BigInt(bits, random).setBit(bits - 1)))(function)(state)
      }
    )

  /** A nested hot site in the hot ladder's iterated shape: the outer iterated
    * call's function the inner iterated call written η-expanded,
    * `λt. iterate n g t`, which `contest-entries-solo`'s knowledge compiles to a narrow
    * block, its counts drawn of `bits` binary digits and its function of one
    * to three steps by the bound operations.
    */
  def nested(random: Random, bits: Int): SiteTerm =
    val libraryNames = HotSites.keys.dropRight(1).map(term)
    lets(libraryNames :+ iterate, Vector.empty, bound =>
      val constructors = bound.take(3)
      val operations = bound.slice(3, 7)
      val steps = 1 + random.nextInt(3)
      val function = λ(input =>
        (1 to steps).foldLeft(input)((value, _) =>
          operations(random.nextInt(operations.size))(value)(numeral(constructors, BigInt(8, random)))
        )
      )
      val inner = numeral(constructors, BigInt(bits, random).setBit(bits - 1))
      val outer = numeral(constructors, BigInt(bits, random).setBit(bits - 1))
      bound(7)(outer)(λ(t => bound(7)(inner)(function)(t)))(numeral(constructors, BigInt(8, random)))
    )

  /** The values let bound in order, `(\x0. … (\xn. body) vn …) v0`, and
    * the body given the bound variables.
    */
  private def lets(values: Vector[SiteTerm], bound: Vector[SiteTerm], body: Vector[SiteTerm] => SiteTerm): SiteTerm =
    if bound.size == values.size then body(bound)
    else λ(variable => lets(values, bound :+ variable, body))(values(bound.size))

object HotSites:

  /** The names of the library terms the generated sites are built from
    * (`TermTables.hotSiteTerms`), the fixed point combinator last.
    */
  val keys: Vector[String] = Vector(
    "binary_zero", "binary_even", "binary_odd", "merge_binary_plus", "binary_maximum", "binary_minimum", "binary_bitwise_or", "fixpoint"
  )

  /** The library terms, each a member of the fixture file read by
    * projection off the tree whose visible subtree is `buildRoot`
    * (`StandardLibrary.entryMembers`), held as a closed instruction.
    */
  def read(buildRoot: Path): HotSites[NoFacts.type] =
    HotSites(StandardLibrary.entryMembers(buildRoot, TermTables.hotSiteTerms, Expansions.none)._1)

  /** The sites' library terms in the configuration of the specializer, each crossed from no facts in its spelling
    * there (`NativeSpecializer.crossedAllFromNoFacts`).
    */
  def crossed[C <: NativeSpecializer & Singleton](sites: HotSites[NoFacts.type], specializer: C): HotSites[C] =
    val crossedTerms = specializer.crossedAllFromNoFacts(sites.terms.values)
    HotSites(sites.terms.map((key, term) => key -> crossedTerms(term)))
