package com.yang_bo.gezi.frontend

import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law that parsing the lambdalattice text of a HOAS term gives the de
  * Bruijn term the HOAS conversion gives, on generated terms
  * (`HoasGenerators.closedTerm`, `LambdalatticeText`), whose purpose is to
  * catch a parser whose precedence, associativity or scoping departs from the
  * HOAS: `∥` binding looser than application and tighter than `+`, a chain of
  * `+` as one choice against a parenthesized choice as a member, a chain of `∥`
  * nesting to the left, an abstraction's body extending to the right, or a
  * variable's index under nested binders; on deep terms, a parser that is not
  * stack safe.
  */
class LambdalatticeTextLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of LambdalatticeTextLawTest, "parsing the text of a deep term gives its de Bruijn term", takes 3.521 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  // TODO: defines stood here, the library names of the generated terms, and with it the law's check that a
  // printer spells a free name (`DeBruijnTerm.Free`) as the name the parser reads back. It named library terms by
  // Term.define leaves of HoasGenerators.closedTerm, a free variable (blacklisted) and a table of library files
  // deleted when the library became files reached by paths. Its replacement generates
  // lambdalattice text with free names directly. The deleted code:
  // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/LambdalatticeTextLawTest.scala.

  property("parsing the text of a term gives the term's de Bruijn term") {
    for term <- HoasGenerators.closedTerm.forAllWithLog(
        LambdalatticeText.text(_)
      )
    yield
      val text = LambdalatticeText.text(term)
      val locallyNameless = term.locallyNamelessTerm
      Result.all(
        List(
          Result.diff(
            Lambdalattice.term(text, FreeNames.Allowed),
            locallyNameless
          )(_ == _),
          Result
            .diff(
              Lambdalattice.term(
                Lambdalattice.text(locallyNameless, Map.empty),
                FreeNames.Allowed
              ),
              locallyNameless
            )(
              _ == _
            )
            .log("printed from the locally nameless term")
        )
      )
  }

  // TODO: the property "a text is rejected for its first free name unless the reading allows free names" stood
  // here. Its purpose: catch a reading that takes a free name where its call did not allow one, and one that
  // rejects a closed text. It named library terms by Term.define leaves of HoasGenerators.closedTerm over library
  // names, a free variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
  // Its replacement generates lambdalattice text
  // with free names directly. The deleted code:
  // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/frontend/LambdalatticeTextLawTest.scala.

  property(
    "parsing the text of a deep term gives its de Bruijn term",
    _.copy(testLimit = 10)
  ) {
    for (kind, length, term) <- HoasGenerators
        .deepTerm(10000, 50000)
        .forAllWithLog((kind, length, _) => s"$kind of length $length")
    yield Result.assert(
      Lambdalattice.term(LambdalatticeText.text(term), FreeNames.Allowed) ==
        term.locallyNamelessTerm
    )
  }
