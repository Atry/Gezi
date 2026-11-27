package com.yang_bo.gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.contest.corpora.reductions.CsesFamilies
import com.yang_bo.gezi.frontend.ProgramPurity
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law that every CSES program the points writer meets is a pure λ term by
  * `ProgramPurity.pureInstruction`, the test the writer applies before it
  * offers a point traps (`PointsFile.written`): the repeated program of every
  * variant below the top rungs (`CsesFamilies.atConstraints`, whose sites are
  * CSES inputs), both twins, from a generated seed at one and two sites, one
  * property for each problem. Its purpose is to catch a CSES problem file or
  * encoding that brings a top, a choice, a parallel or a constant into a
  * program, and a respelling (`CsesSpelling`) that breaks a literal's
  * application spine so that `ProgramPurity` looks at its levels' tops, either
  * of which would silently give the program's points no trap, the computed
  * wrong answers of `CsesFamily.trapCandidates` included.
  *
  * One property for each problem and not one for every variant: the one
  * property over the first batch's five problems overran the 3 s deadline in a
  * reading on two cores (CPUs 2 and 3), before and after the alpha renaming of
  * the problem files,, and with the second batch's ten as well on four (CPUs 0
  * to 3 of contest.slice, nice 10, the 1-minute load about 9, 2026-11-21); each
  * problem's property builds its own problem's programs, its file read when
  * first built.
  */
class CsesPurityLawTest extends GeneratedProperties:

  /** The parts of the law families' group the draws read, built once
    * (`LawFamilies.sharedFixtures`).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  CsesFamilies.all.flatten
    .filterNot(CsesFamilies.atConstraints.contains)
    .groupBy(_.problem)
    .toVector
    .sortBy(_._1)
    .foreach((problem, variants) =>
      property(
        s"every $problem program below the top rung is a pure λ term",
        _.copy(testLimit = 3)
      ) {
        for
          seed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).forAll
          repetitions <- Gen.int(Range.constant(1, 2)).forAll
        yield Result.all(
          variants.toList.map(variant =>
            Result
              .assert(
                ProgramPurity.pureInstruction(
                  PointsFile.closedTerm(
                    variant.program(LawFamilies.group, seed, repetitions)
                  )
                )
              )
              .log(
                s"${variant.stem}/repetitions_$repetitions at the seed $seed is not pure"
              )
          )
        )
      }
    )
