package gezi.jit

import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary

/** The unique spelling's premise (`UniqueSpellingPremiseCheck`, proofs section
  * 23) on the natives' library's facts (`NativesTesting.nativesOn`), the facts
  * the JIT's storage tests build their storages from: every constructor of
  * every stored representation and of every declared family is shown a member
  * of its criterion's unfolding, and the families of a finite value parameter
  * agree with the backend's facts. Its purpose is to catch facts of that
  * library whose constructor or field criteria are not the criterion's own, a
  * check that leaves the naturals, the booleans or the lists unchecked, and, by
  * a constructor applied to another family's criterion, a check that accepts
  * every constructor. The in-tree entries' facts are checked by
  * `contest-in-tree-entries`' `EntriesPremiseTest`.
  */
class UniqueSpellingPremiseTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => premise.nonMembers,
      _ => JitTesting.libraryInstruction[encoding.type]("nat_type")
    )

  private lazy val facts = BackendFacts.of(NativesTesting.nativesOn)
  private lazy val encoding: StorageEncoding = facts.storageEncoding
  private given encoding.type = encoding
  private lazy val premise = UniqueSpellingPremiseCheck(encoding)

  /** A pure key of the facts as a value of the configuration. */
  private def pureValue(key: gezi.ir.Pure): JitValue[encoding.type] =
    gezi.ir.Value.of(gezi.ir.Configured.fromPure(encoding)(key))

  test(
    "every constructor of a stored criterion and of a declared family is shown a member of its unfolding"
  ) {
    val natType =
      gezi.ir.Value.of(JitTesting.libraryInstruction[encoding.type]("nat_type"))
    assert(
      Vector(
        Representation.BigInteger,
        Representation.Truth,
        Representation.ListOf(natType)
      ).forall(premise.stored.contains),
      s"the naturals, the booleans or the naturals' lists are not checked: ${premise.stored}"
    )
    val listCriteria = premise.stored.collect {
      case list @ Representation.ListOf(_) =>
        encoding.operations.criterionOf(list)
    }
    assert(
      premise.stored.exists {
        case Representation.ListOf(element) => listCriteria.contains(element)
        case _                              => false
      },
      s"no list of lists is checked: ${premise.stored}"
    )
    assertEquals(premise.nonMembers, Vector.empty)
    assertEquals(premise.declaredNonMembers, Vector.empty)
    assertEquals(premise.parameterizedDisagreements, Vector.empty)
  }

  // The check separates: a field criterion other than T's own is not shown.
  test("a constructor applied to another field criterion is no member") {
    val successor = pureValue(
      facts.constructorDefine(
        NativeName.Constructor(BigIntegerFamily.identity, 1)
      )
    )
    assert(
      !premise.member(
        JitTesting.criterionOf(encoding)(Representation.BigInteger),
        successor,
        Vector(JitTesting.criterionOf(encoding)(Representation.Truth))
      )
    )
  }

  /** The law that a criterion whose one head is `λx₁ … xₙ. (Θ g) x₁ … xₙ`, the
    * criterion `Θ g` for `g = λt x₁ … xₙ. t x₁ … xₙ`, n from 1 to 3, shows no
    * member and ends. Derived before the run: the tabled reading of `Θ g` gives
    * g's body at `Θ g`, a head η-shaped over `Θ g`, which the check reads as
    * `Θ g`'s heads again, so the readings never reach a head that is not
    * η-shaped, and the check ends only when their common limit is spent. Its
    * purpose is to catch a check whose η contractions are not bounded.
    */
  test(
    "a criterion whose head contracts by η to itself shows no member and ends"
  ) {
    val successor = pureValue(
      facts.constructorDefine(
        NativeName.Constructor(BigIntegerFamily.identity, 1)
      )
    )
    def expanded(applied: gezi.frontend.Term, arity: Int): gezi.frontend.Term =
      if arity == 0 then applied
      else gezi.frontend.Term.λ(x => expanded(applied(x), arity - 1))
    val half = gezi.frontend.Term.λ(x => gezi.frontend.Term.λ(f => f(x(x)(f))))
    val shown = (1 to 3).toVector.map { arity =>
      val criterion = half(half)(gezi.frontend.Term.λ(t => expanded(t, arity)))
      val instruction = gezi.frontend.Defunctionalization
        .thunkInstruction[encoding.type](criterion.deBruijnTerm(Map.empty))
      premise.member(
        gezi.ir.Value.of(instruction),
        successor,
        Vector(JitTesting.criterionOf(encoding)(Representation.BigInteger))
      )
    }
    assertEquals(shown, Vector(false, false, false))
  }

  /** The library's fixed-width words (`TermTables.codecTerms`), whose family
    * takes a width of every size, checked once for every width: the width is a
    * fresh opaque constant W, a closed term of no layer that no head β reads,
    * so that what is shown of W holds of every width by substitution, by β
    * alone and with no reader's neutral value. The premise is shown for the
    * cell under `word_type (successor W)` (proofs, section 25, steps 2 to 6)
    * and for the end under `word_type zero`; the end is no member under a
    * positive width and the cell none under no width. Its purpose is to catch
    * word facts whose cell's field criteria are not the criterion's own at some
    * width, which no test of a width at a time could cover.
    */
  test(
    "the words' cell and end are shown members of their criterion for every width"
  ) {
    val terms = StandardLibrary
      .entryMembers(
        LibraryFiles.buildRoot,
        gezi.standardlibrary.TermTables.codecTerms,
        gezi.weakhead.Expansions.none
      )
      ._1
    def term(key: String): JitValue[encoding.type] =
      val read =
        terms.getOrElse(key, fail(s"the codec terms have no member $key"))
      gezi.ir.Value.of(encoding.crossedAllFromNoFacts(Vector(read))(read))
    val width: JitValue[encoding.type] =
      gezi.ir.Value.of(encoding.opaque("a fixed width word's width"))
    val positive = JitValue.Apply(
      term("word_type"),
      JitValue.Apply(term("successor"), width)
    )
    val empty = JitValue.Apply(term("word_type"), term("zero"))
    val cellFields =
      Vector(term("boolean_type"), JitValue.Apply(term("word_type"), width))
    assertEquals(
      (
        premise.member(positive, term("word_cell"), cellFields),
        premise.member(empty, term("word_end"), Vector.empty),
        premise.member(positive, term("word_end"), Vector.empty),
        premise.member(empty, term("word_cell"), cellFields)
      ),
      (true, true, false, false)
    )
  }
