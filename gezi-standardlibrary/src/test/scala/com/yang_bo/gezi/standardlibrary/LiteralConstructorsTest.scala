package com.yang_bo.gezi.standardlibrary

import java.nio.file.Files
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.Literals

/** The front end's top (`Literals.top`), the miss of a partial function of a
  * literal, is the member of the library's file of top, so that a partial
  * function's miss holds the instruction a program that imports top from its
  * file holds. The file returns a tuple of one field, `λexport. export top`
  * (the binder `export`), so its term hands top to the tuple's continuation.
  * Its purpose is to catch the front end's constant and the library's file
  * drifting apart. A literal's bits are no library values (a literal's value is
  * what a module's `from_cbor` reads of them; their laws are
  * `CborCodecLawTest`), so they are not pinned. The input is the file itself,
  * so nothing is generated.
  */
class LiteralConstructorsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  private def fileTerm(path: String): DeBruijnTerm =
    Lambdalattice.term(
      Files.readString(
        LibraryFiles.sourceTree.resolve(s"library/$path.lambdalattice")
      )
    )

  /** `λexport. export value`, the tuple of one field, the value closed. */
  private def oneTuple(value: DeBruijnTerm): DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), value))

  test("the library file top's field is the front end's top") {
    assertEquals(fileTerm("top"), oneTuple(Literals.top))
  }
