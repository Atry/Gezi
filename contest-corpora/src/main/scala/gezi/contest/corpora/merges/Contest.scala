package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.frontend.Term
import gezi.frontend.Term.*

/** A circular proof of the contest corpus: `unfold p` checks the two outputs
  * and goes on with p, `cite k` closes the branch at the goal k unfolds above.
  */
enum CircularProof:
  case Unfold(proof: CircularProof)
  case Cite(index: Int)

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_clauses.pl`; its data are
  * `problems/clauses`), which `contest.pl` included: the contest corpus,
  * problems whose data is built by value recursion over the Scott encoding of
  * the prelude (linked lists with a cycle, streams and Brzozowski derivatives,
  * proof objects and circular proofs, equi-recursive types). The constructors
  * of regular expressions, the top and function types, the field labels and the
  * field orders of the self record are data of the family
  * `gezi/problems/clauses` and are read from it.
  */
final class Contest(problems: ProblemFamilies, prelude: Prelude):

  private val file = problems("clauses")

  import prelude.{
    cons,
    falseValue,
    first,
    fixpoint,
    identity,
    map,
    naturalDouble,
    naturalEqual,
    nil,
    pair,
    second,
    successor,
    trueValue,
    zero
  }

  // ---- shared pieces ----

  /** The Scott numeral `count` (`numeral/2`). */
  def numeral(count: Int): ProblemTerm =
    require(count >= 0, s"a numeral is not negative: $count")
    (1 to count).foldLeft(zero)((rest, _) => successor(rest))

  /** `and a b`: b when a is true, false otherwise (`conjunction/1`). */
  val conjunction: ProblemTerm = λ(a => λ(b => a(b)(falseValue)))

  /** The Scott list of the numerals, ending in the tail (`labels_list/3`). */
  def labelsList(labels: Seq[Int], tail: ProblemTerm): ProblemTerm =
    labels.foldRight(tail)((label, rest) => cons(numeral(label))(rest))

  /** The infinite list that repeats the labels,
    * `fix (\self. cons l1 (cons l2 (... self)))` (`cyclic_labels/2`).
    */
  def cyclicLabels(labels: Seq[Int]): ProblemTerm = fixpoint(
    λ(self => labelsList(labels, self))
  )

  // ---- 1. linked list cycle ----

  /** A list of `prefix` nodes followed by a cycle of `cycle` nodes, each node's
    * element the numeral of its position (`lasso/3`).
    */
  def lasso(prefix: Int, cycle: Int): ProblemTerm =
    labelsList(0 until prefix, cyclicLabels(prefix until prefix + cycle))

  /** `count` labelled nodes, then nil (`acyclic/2`). */
  def acyclic(count: Int): ProblemTerm = labelsList(0 until count, nil)

  /** The lasso's prefix, then `rounds` turns of its cycle, then nil
    * (`unrolled_lasso/4`).
    */
  def unrolledLasso(prefix: Int, cycle: Int, rounds: Int): ProblemTerm =
    labelsList(
      (0 until prefix) ++ Vector
        .fill(rounds)(prefix until prefix + cycle)
        .flatten,
      nil
    )

  /** `ends node = node true (\h. \t. ends t)` (`ends/1`). */
  val ends: ProblemTerm = fixpoint(
    λ(self => λ(node => node(trueValue)(λ(_ => λ(tail => self(tail))))))
  )

  /** `same a b`: both are cons nodes with equal labels (`same_node/1`). */
  val sameNode: ProblemTerm =
    λ(a =>
      λ(b =>
        a(falseValue)(
          λ(headLeft =>
            λ(_ =>
              b(falseValue)(
                λ(headRight => λ(_ => naturalEqual(headLeft)(headRight)))
              )
            )
          )
        )
      )
    )

  /** Floyd's race of the tortoise and the hare, 141 (`floyd_race/1`). */
  val floydRace: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(slow =>
          λ(fast =>
            fast(falseValue)(
              λ(_ =>
                λ(fastTail =>
                  fastTail(falseValue)(
                    λ(_ =>
                      λ(fastNext =>
                        slow(falseValue)(
                          λ(_ =>
                            λ(slowNext =>
                              sameNode(slowNext)(fastNext)(trueValue)(
                                self(slowNext)(fastNext)
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** `\list. race list list` (`floyd_has_cycle/1`). */
  val floydHasCycle: ProblemTerm = λ(list => floydRace(list)(list))

  /** The race that returns the node where the two meet (`floyd_meet/1`). */
  val floydMeet: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(slow =>
          λ(fast =>
            fast(nil)(
              λ(_ =>
                λ(fastTail =>
                  fastTail(nil)(
                    λ(_ =>
                      λ(fastNext =>
                        slow(nil)(
                          λ(_ =>
                            λ(slowNext =>
                              sameNode(slowNext)(fastNext)(slowNext)(
                                self(slowNext)(fastNext)
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** A node's label (`node_label/1`). */
  val nodeLabel: ProblemTerm = λ(node => node(zero)(λ(head => λ(_ => head))))

  /** A node's tail (`node_next/1`). */
  val nodeNext: ProblemTerm = λ(node => node(nil)(λ(_ => λ(tail => tail))))

  /** The second phase of Floyd's 142 (`floyd_walk/1`). */
  val floydWalk: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            sameNode(left)(right)(nodeLabel(left))(
              self(nodeNext(left))(nodeNext(right))
            )
          )
        )
      )
    )

  /** Floyd's 142, the label of the node where the cycle starts
    * (`floyd_cycle_start/1`).
    */
  val floydCycleStart: ProblemTerm =
    λ(list => floydWalk(list)(floydMeet(list)(list)))

  /** Whether a natural is in a list (`member_natural/1`). */
  val memberNatural: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(element =>
          λ(elements =>
            elements(falseValue)(
              λ(head =>
                λ(tail =>
                  naturalEqual(element)(head)(trueValue)(self(element)(tail))
                )
              )
            )
          )
        )
      )
    )

  /** The visited set, 142 (`visited_cycle_start/1`). */
  val visitedCycleStart: ProblemTerm =
    λ(list =>
      fixpoint(
        λ(self =>
          λ(seen =>
            λ(node =>
              node(zero)(
                λ(head =>
                  λ(tail =>
                    memberNatural(head)(seen)(head)(
                      self(cons(head)(seen))(tail)
                    )
                  )
                )
              )
            )
          )
        )
      )(nil)(list)
    )

  // ---- 2. symbolic computation by value recursion ----

  /** `ones = 1 : ones` (`stream_ones/1`). */
  def streamOnes: ProblemTerm = fixpoint(λ(stream => cons(numeral(1))(stream)))

  /** `ones = 1 : map id ones` (`stream_ones_by_map/1`). */
  def streamOnesByMap: ProblemTerm = fixpoint(
    λ(stream => cons(numeral(1))(map(identity)(stream)))
  )

  /** `nats = 0 : map succ nats` (`stream_naturals_by_map/1`). */
  def streamNaturalsByMap: ProblemTerm = fixpoint(
    λ(stream => cons(zero)(map(successor)(stream)))
  )

  /** `x = 1 : y, y = 1 : x`, read at x (`stream_mutual/1`). */
  def streamMutual: ProblemTerm =
    first(
      fixpoint(
        λ(streams =>
          pair(cons(numeral(1))(second(streams)))(
            cons(numeral(1))(first(streams))
          )
        )
      )
    )

  /** `nth n s` (`stream_nth/1`). */
  val streamNth: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(index =>
          λ(stream =>
            stream(zero)(
              λ(head =>
                λ(tail =>
                  index(head)(λ(predecessor => self(predecessor)(tail)))
                )
              )
            )
          )
        )
      )
    )

  /** `every c s` (`every_element_is/1`). */
  val everyElementIs: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(constant =>
          λ(stream =>
            stream(trueValue)(
              λ(head =>
                λ(tail =>
                  naturalEqual(head)(constant)(self(constant)(tail))(falseValue)
                )
              )
            )
          )
        )
      )
    )

  private def regexEmpty: ProblemTerm = file.program("regex_empty")

  /** The regular expression of the empty word (`regex_epsilon/1`). */
  def regexEpsilon: ProblemTerm = file.program("regex_epsilon")

  private def regexLetter: ProblemTerm = file.program("regex_letter")

  /** `alt l r` (`regex_alternation/1`). */
  def regexAlternation: ProblemTerm = file.program("regex_alternation")

  /** `seq l r` (`regex_concatenation/1`). */
  def regexConcatenation: ProblemTerm = file.program("regex_concatenation")

  /** The letter `a` is true, `b` false (`letter/2`). */
  def letter(name: Char): ProblemTerm = name match
    case 'a'   => trueValue
    case 'b'   => falseValue
    case other => throw IllegalArgumentException(s"$other is no letter")

  /** The regular expression of one letter (`letter_expression/2`). */
  def letterExpression(name: Char): ProblemTerm = regexLetter(letter(name))

  private val sameLetter: ProblemTerm =
    λ(left => λ(right => left(right)(right(falseValue)(trueValue))))

  /** `nullable r` (`regex_nullable/1`). */
  val regexNullable: ProblemTerm = regexRecursion(falseValue)

  /** `nonempty r` (`regex_nonempty/1`). */
  val regexNonempty: ProblemTerm = regexRecursion(trueValue)

  private def regexRecursion(atLetter: ProblemTerm): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(expression =>
          expression(falseValue)(trueValue)(λ(_ => atLetter))(
            λ(left => λ(right => prelude.or(self(left))(self(right))))
          )(
            λ(firstPart =>
              λ(secondPart => conjunction(self(firstPart))(self(secondPart)))
            )
          )
        )
      )
    )

  /** The derivative by a letter, over the `plain` or the `smart` constructors
    * (`regex_derivative/2`).
    */
  def regexDerivative(kind: String): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(letterValue =>
          λ(expression =>
            expression(regexEmpty)(regexEmpty)(
              λ(other =>
                sameLetter(letterValue)(other)(regexEpsilon)(regexEmpty)
              )
            )(
              λ(left =>
                λ(right =>
                  kindAlternation(kind)(self(letterValue)(left))(
                    self(letterValue)(right)
                  )
                )
              )
            )(
              λ(firstPart =>
                λ(secondPart =>
                  kindAlternation(kind)(
                    kindConcatenation(kind)(self(letterValue)(firstPart))(
                      secondPart
                    )
                  )(
                    regexNullable(firstPart)(self(letterValue)(secondPart))(
                      regexEmpty
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  private def kindAlternation(kind: String): ProblemTerm = kind match
    case "plain" => regexAlternation
    case "smart" =>
      λ(left =>
        λ(right =>
          regexIsEmpty(left)(right)(
            regexIsEmpty(right)(left)(regexAlternation(left)(right))
          )
        )
      )
    case other =>
      throw IllegalArgumentException(s"$other is no kind of constructors")

  private def kindConcatenation(kind: String): ProblemTerm = kind match
    case "plain" => regexConcatenation
    case "smart" =>
      λ(firstPart =>
        λ(secondPart =>
          regexIsEmpty(firstPart)(regexEmpty)(
            regexIsEpsilon(firstPart)(secondPart)(
              regexConcatenation(firstPart)(secondPart)
            )
          )
        )
      )
    case other =>
      throw IllegalArgumentException(s"$other is no kind of constructors")

  private def regexIsEmpty: ProblemTerm =
    λ(expression =>
      expression(trueValue)(falseValue)(λ(_ => falseValue))(
        λ(_ => λ(_ => falseValue))
      )(λ(_ => λ(_ => falseValue)))
    )

  private def regexIsEpsilon: ProblemTerm =
    λ(expression =>
      expression(falseValue)(trueValue)(λ(_ => falseValue))(
        λ(_ => λ(_ => falseValue))
      )(λ(_ => λ(_ => falseValue)))
    )

  /** `matches r w` (`regex_matches/1`). */
  def regexMatches: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(expression =>
          λ(word =>
            word(regexNullable(expression))(
              λ(letterValue =>
                λ(rest =>
                  self(regexDerivative("plain")(letterValue)(expression))(rest)
                )
              )
            )
          )
        )
      )
    )

  /** `all_prefixes r w` (`regex_all_prefixes/2`). */
  def regexAllPrefixes(kind: String): ProblemTerm =
    fixpoint(
      λ(self =>
        λ(expression =>
          λ(word =>
            regexNullable(expression)(
              word(trueValue)(
                λ(letterValue =>
                  λ(rest =>
                    self(regexDerivative(kind)(letterValue)(expression))(rest)
                  )
                )
              )
            )(falseValue)
          )
        )
      )
    )

  /** `S = epsilon | a (S b)` (`grammar_a_n_b_n/1`). */
  def grammarANBN: ProblemTerm =
    fixpoint(
      λ(grammar =>
        regexAlternation(regexEpsilon)(
          regexConcatenation(letterExpression('a'))(
            regexConcatenation(grammar)(letterExpression('b'))
          )
        )
      )
    )

  /** `S = epsilon | a S` (`grammar_a_star/1`). */
  def grammarAStar: ProblemTerm =
    fixpoint(
      λ(grammar =>
        regexAlternation(regexEpsilon)(
          regexConcatenation(letterExpression('a'))(grammar)
        )
      )
    )

  /** `S = epsilon | a (b S)` (`grammar_a_b_star/1`). */
  def grammarABStar: ProblemTerm =
    fixpoint(
      λ(grammar =>
        regexAlternation(regexEpsilon)(
          regexConcatenation(letterExpression('a'))(
            regexConcatenation(letterExpression('b'))(grammar)
          )
        )
      )
    )

  /** `S = a S` (`grammar_no_base/1`). */
  def grammarNoBase: ProblemTerm = fixpoint(
    λ(grammar => regexConcatenation(letterExpression('a'))(grammar))
  )

  /** `S = b | a S` (`grammar_with_base/1`). */
  def grammarWithBase: ProblemTerm =
    fixpoint(
      λ(grammar =>
        regexAlternation(letterExpression('b'))(
          regexConcatenation(letterExpression('a'))(grammar)
        )
      )
    )

  /** A finite word, a Scott list of letters (`word/2`). */
  def word(letters: Seq[Char]): ProblemTerm =
    letters.foldRight(nil)((name, rest) => cons(letter(name))(rest))

  /** a^count b^count, then the extra letters (`a_n_b_n_word/3`). */
  def aNBNWord(count: Int, extra: Seq[Char]): ProblemTerm =
    word(Vector.fill(count)('a') ++ Vector.fill(count)('b') ++ extra)

  /** The infinite word a a a ... (`word_a_omega/1`). */
  def wordAOmega: ProblemTerm = fixpoint(
    λ(wordVariable => cons(letter('a'))(wordVariable))
  )

  // ---- 3. theorem proving by value recursion ----

  /** The checker of "every element is even" (`check_evens/1`). */
  val checkEvens: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(proof =>
          λ(stream =>
            stream(trueValue)(
              λ(head =>
                λ(tail =>
                  proof(falseValue)(
                    λ(witness =>
                      λ(rest =>
                        naturalEqual(naturalDouble(witness))(head)(
                          self(rest)(tail)
                        )(falseValue)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The cyclic stream 0, 2, ..., 2(count - 1) and its cyclic proof
    * (`evens/3`).
    */
  def evens(count: Int): (ProblemTerm, ProblemTerm) =
    (cyclicLabels((0 until count).map(2 * _)), cyclicLabels(0 until count))

  /** The checker of "this list is infinite" (`check_infinite/1`). */
  val checkInfinite: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(proof =>
          λ(list =>
            list(falseValue)(
              λ(_ => λ(tail => proof(λ(rest => self(rest)(tail)))))
            )
          )
        )
      )
    )

  /** `p = \k. k p` (`infinite_proof/1`). */
  def infiniteProof: ProblemTerm = fixpoint(
    λ(proof => λ(continuation => continuation(proof)))
  )

  /** An automaton, a Scott list of pairs (output, next state) (`automaton/2`).
    */
  def automaton(transitions: Seq[(Int, Int)]): ProblemTerm =
    transitions.foldRight(nil)((transition, rest) =>
      cons(pair(numeral(transition._1))(numeral(transition._2)))(rest)
    )

  /** The term of a circular proof (`proof_term/2`). */
  def proofTerm(proof: CircularProof): ProblemTerm = proof match
    case CircularProof.Unfold(inner) =>
      λ(unfold => λ(_ => unfold(proofTerm(inner))))
    case CircularProof.Cite(index) => λ(_ => λ(cite => cite(numeral(index))))

  private def listElement: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(list =>
          λ(index =>
            list(nil)(
              λ(head =>
                λ(tail =>
                  index(head)(λ(predecessor => self(tail)(predecessor)))
                )
              )
            )
          )
        )
      )
    )

  private def automatonOutput: ProblemTerm =
    λ(automatonTerm => λ(state => first(listElement(automatonTerm)(state))))

  private def automatonNext: ProblemTerm =
    λ(automatonTerm => λ(state => second(listElement(automatonTerm)(state))))

  private def cited: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(goals =>
          λ(index =>
            λ(left =>
              λ(right =>
                goals(falseValue)(
                  λ(goal =>
                    λ(rest =>
                      index(
                        goal(
                          λ(goalLeft =>
                            λ(goalRight =>
                              conjunction(naturalEqual(goalLeft)(left))(
                                naturalEqual(goalRight)(right)
                              )
                            )
                          )
                        )
                      )(
                        λ(predecessor => self(rest)(predecessor)(left)(right))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The checker of a circular proof (`check_circular/1`). */
  def checkCircular: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(firstAutomaton =>
          λ(secondAutomaton =>
            λ(goals =>
              λ(left =>
                λ(right =>
                  λ(proof =>
                    proof(
                      λ(rest =>
                        naturalEqual(automatonOutput(firstAutomaton)(left))(
                          automatonOutput(secondAutomaton)(right)
                        )(
                          self(firstAutomaton)(secondAutomaton)(
                            cons(pair(left)(right))(goals)
                          )(automatonNext(firstAutomaton)(left))(
                            automatonNext(secondAutomaton)(right)
                          )(rest)
                        )(falseValue)
                      )
                    )(λ(index => cited(goals)(index)(left)(right)))
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The check of the proof for state 0 of the first automaton against state 0
    * of the second (`circular_claim/4`).
    */
  def circularClaim(
      firstTransitions: Seq[(Int, Int)],
      secondTransitions: Seq[(Int, Int)],
      proof: CircularProof
  ): ProblemTerm =
    checkCircular(automaton(firstTransitions))(automaton(secondTransitions))(
      nil
    )(zero)(zero)(proofTerm(proof))

  // ---- 4. greatest-fixed-point type systems ----

  private def typeTop: ProblemTerm = file.program("type_top")

  private def typeBase(name: Int): ProblemTerm =
    λ(_ => λ(base => λ(_ => λ(_ => base(numeral(name))))))

  private def typeFunction(
      argument: ProblemTerm,
      result: ProblemTerm
  ): ProblemTerm = file.program("type_function", argument, result)

  /** The record type of the labelled fields, in order (`type_record/2`). */
  def typeRecord(fields: Seq[(Int, ProblemTerm)]): ProblemTerm =
    λ(_ =>
      λ(_ =>
        λ(_ =>
          λ(record =>
            record(
              fields.foldRight(nil)((field, rest) =>
                cons(pair(numeral(field._1))(field._2))(rest)
              )
            )
          )
        )
      )
    )

  /** The base type of the naturals (`type_natural/1`). */
  def typeNatural: ProblemTerm = typeBase(0)

  /** The base type of the Booleans (`type_boolean/1`). */
  def typeBoolean: ProblemTerm = typeBase(1)

  /** The equi-recursive type `fixpoint (\self. Body)` (`recursive_type/2`). */
  def recursiveType(body: ProblemTerm => ProblemTerm): ProblemTerm = fixpoint(
    λ(self => body(self))
  )

  /** The label of each field name (`field/2`). */
  private val fields: Map[String, Int] =
    file
      .rows("field")
      .map(arguments =>
        ProblemData.text(arguments(0)) -> ProblemData.small(arguments(1))
      )
      .toMap

  /** The record type of the named fields, each name labelled by `field/2`
    * (`record_named/2`). Throws for a name that is no field.
    */
  def recordNamed(named: (String, ProblemTerm)*): ProblemTerm =
    typeRecord(
      named.map((name, fieldType) =>
        fields.getOrElse(
          name,
          throw IllegalArgumentException(s"$name is no field")
        ) -> fieldType
      )
    )

  /** Subtyping without an assumption set (`subtype/1`). */
  def subtype: ProblemTerm =
    fixpoint(
      λ(subtypeVariable =>
        λ(sub =>
          λ(superType =>
            val every = fixpoint(
              λ(everySelf =>
                λ(haveFields =>
                  λ(wantFields =>
                    wantFields(trueValue)(
                      λ(field =>
                        λ(rest =>
                          field(
                            λ(label =>
                              λ(fieldType =>
                                conjunction(
                                  find(subtypeVariable)(haveFields)(label)(
                                    fieldType
                                  )
                                )(everySelf(haveFields)(rest))
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
            superType(trueValue)(
              λ(name =>
                sub(falseValue)(λ(subName => naturalEqual(subName)(name)))(
                  λ(_ => λ(_ => falseValue))
                )(λ(_ => falseValue))
              )
            )(
              λ(superArgument =>
                λ(superResult =>
                  sub(falseValue)(λ(_ => falseValue))(
                    λ(subArgument =>
                      λ(subResult =>
                        conjunction(
                          subtypeVariable(superArgument)(subArgument)
                        )(subtypeVariable(subResult)(superResult))
                      )
                    )
                  )(λ(_ => falseValue))
                )
              )
            )(
              λ(superFields =>
                sub(falseValue)(λ(_ => falseValue))(λ(_ => λ(_ => falseValue)))(
                  λ(subFields => every(subFields)(superFields))
                )
              )
            )
          )
        )
      )
    )

  /** The search of a wanted field among the fields, checking its type by the
    * subtype variable (the `Find` of `subtype/1`).
    */
  private def find(subtypeVariable: ProblemTerm): ProblemTerm =
    fixpoint(
      λ(findSelf =>
        λ(fieldList =>
          λ(wantedLabel =>
            λ(wantedType =>
              fieldList(falseValue)(
                λ(have =>
                  λ(haveRest =>
                    have(
                      λ(haveLabel =>
                        λ(haveType =>
                          naturalEqual(haveLabel)(wantedLabel)(
                            subtypeVariable(haveType)(wantedType)
                          )(findSelf(haveRest)(wantedLabel)(wantedType))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The fields of `T = { next : T, value : Nat }` in the order, the self and
    * the natural standing for the parameters of the row
    * (`self_record_fields/4`): a row names its two parameters by the texts of
    * its second and third fields, and each field is the plain pair of its name
    * and one of them, `λtuple. tuple Name Parameter`.
    */
  private def selfRecordFields(
      order: String,
      self: ProblemTerm,
      natural: ProblemTerm
  ): Vector[(String, ProblemTerm)] =
    file.rowsWith("self_record_fields", Map(0 -> order)) match
      case Vector(arguments) =>
        val environment = Map(
          ProblemData.text(arguments(1)) -> self,
          ProblemData.text(arguments(2)) -> natural
        )
        ProblemData
          .list(arguments(3))
          .map(field =>
            ProblemData.alternative(field, 1) match
              case (0, Vector(name, value)) =>
                val parameter = ProblemData.text(value)
                ProblemData.text(name) -> environment.getOrElse(
                  parameter,
                  throw IllegalArgumentException(
                    s"$parameter is no parameter of self_record_fields"
                  )
                )
              case other =>
                throw IllegalArgumentException(s"$other is not a named field")
          )
      case found =>
        throw IllegalArgumentException(
          s"self_record_fields has ${found.length} facts for $order"
        )

  private def selfRecord(order: String): ProblemTerm =
    recursiveType(self =>
      recordNamed(selfRecordFields(order, self, typeNatural)*)
    )

  private def nextOnlyRecord: ProblemTerm =
    recursiveType(self => recordNamed("next" -> self))

  private def unrolledSelfRecord(depth: Int, order: String): ProblemTerm =
    (1 to depth).foldLeft(typeRecord(Vector.empty))((inner, _) =>
      recordNamed(selfRecordFields(order, inner, typeNatural)*)
    )

  private def unrolledNextOnlyRecord(depth: Int): ProblemTerm =
    (1 to depth).foldLeft(typeRecord(Vector.empty))((inner, _) =>
      recordNamed("next" -> inner)
    )

  private def cellType: ProblemTerm =
    recursiveType(self => recordNamed("get" -> typeNatural, "self" -> self))

  private def settableCellType: ProblemTerm =
    recursiveType(self =>
      recordNamed(
        "set" -> typeFunction(typeNatural, self),
        "get" -> typeNatural,
        "self" -> self
      )
    )

  private def comparableType: ProblemTerm =
    recursiveType(self =>
      recordNamed("compare" -> typeFunction(self, typeBoolean))
    )

  private def extendedComparableType: ProblemTerm =
    recursiveType(self =>
      recordNamed(
        "extra" -> typeNatural,
        "compare" -> typeFunction(self, typeBoolean)
      )
    )

  private def stackType: ProblemTerm =
    recursiveType(self =>
      recordNamed(
        "push" -> typeFunction(typeNatural, self),
        "pop" -> self,
        "top" -> typeNatural
      )
    )

  private def listStackType: ProblemTerm =
    recursiveType(self =>
      recordNamed(
        "size" -> typeNatural,
        "top" -> typeNatural,
        "push" -> typeFunction(typeNatural, self),
        "pop" -> self
      )
    )

  private def containerType(element: Int): ProblemTerm =
    recursiveType(self =>
      recordNamed(
        "get" -> typeBase(element),
        "map" -> typeFunction(typeBase(element), self)
      )
    )

  private def nestOperator: ProblemTerm =
    fixpoint(
      λ(self =>
        λ(element =>
          recordNamed("head" -> element, "tail" -> self(identity(element)))
        )
      )
    )

  // ---- the points ----

  private def pointTerms: Vector[(String, () => ProblemTerm)] = Vector(
    "lasso_ends_small" -> (() => ends(lasso(2, 3))),
    "lasso_ends_medium" -> (() => ends(lasso(8, 8))),
    "lasso_ends_large" -> (() => ends(lasso(30, 30))),
    "acyclic_ends_small" -> (() => ends(acyclic(5))),
    "acyclic_ends_medium" -> (() => ends(acyclic(16))),
    "lasso_ends_unrolled" -> (() => ends(unrolledLasso(2, 3, 3))),
    "lasso_floyd_has_cycle_small" -> (() => floydHasCycle(lasso(2, 3))),
    "lasso_floyd_has_cycle_medium" -> (() => floydHasCycle(lasso(8, 8))),
    "lasso_floyd_has_cycle_large" -> (() => floydHasCycle(lasso(30, 30))),
    "acyclic_floyd_has_cycle_small" -> (() => floydHasCycle(acyclic(5))),
    "acyclic_floyd_has_cycle_medium" -> (() => floydHasCycle(acyclic(16))),
    "lasso_floyd_cycle_start_small" -> (() => floydCycleStart(lasso(2, 3))),
    "lasso_floyd_cycle_start_medium" -> (() => floydCycleStart(lasso(8, 8))),
    "lasso_floyd_cycle_start_large" -> (() => floydCycleStart(lasso(30, 30))),
    "rho_floyd_cycle_start" -> (() => floydCycleStart(lasso(0, 4))),
    "lasso_floyd_cycle_start_unrolled" -> (() =>
      floydCycleStart(unrolledLasso(2, 3, 4))
    ),
    "lasso_visited_cycle_start_small" -> (() => visitedCycleStart(lasso(2, 3))),
    "lasso_visited_cycle_start_medium" -> (() =>
      visitedCycleStart(lasso(8, 8))
    ),
    "lasso_visited_cycle_start_large" -> (() =>
      visitedCycleStart(lasso(30, 30))
    ),
    "stream_nth_ones_by_map_small" -> (() =>
      streamNth(numeral(5))(streamOnesByMap)
    ),
    "stream_nth_ones_by_map_large" -> (() =>
      streamNth(numeral(40))(streamOnesByMap)
    ),
    "stream_nth_naturals_by_map_small" -> (() =>
      streamNth(numeral(6))(streamNaturalsByMap)
    ),
    "stream_nth_naturals_by_map_large" -> (() =>
      streamNth(numeral(25))(streamNaturalsByMap)
    ),
    "stream_ones_all_one" -> (() => everyElementIs(numeral(1))(streamOnes)),
    "stream_mutual_all_one" -> (() => everyElementIs(numeral(1))(streamMutual)),
    "stream_ones_by_map_all_one" -> (() =>
      everyElementIs(numeral(1))(streamOnesByMap)
    ),
    "stream_naturals_all_zero" -> (() =>
      everyElementIs(zero)(streamNaturalsByMap)
    ),
    "stream_all_one_unrolled" -> (() =>
      everyElementIs(numeral(1))(labelsList(Vector(1, 1, 1, 1, 1), nil))
    ),
    "regex_matches_small" -> (() =>
      regexMatches(grammarANBN)(aNBNWord(2, Vector.empty))
    ),
    "regex_matches_medium" -> (() =>
      regexMatches(grammarANBN)(aNBNWord(5, Vector.empty))
    ),
    "regex_matches_large" -> (() =>
      regexMatches(grammarANBN)(aNBNWord(7, Vector.empty))
    ),
    "regex_rejects_small" -> (() =>
      regexMatches(grammarANBN)(aNBNWord(2, Vector('b')))
    ),
    "regex_rejects_medium" -> (() =>
      regexMatches(grammarANBN)(aNBNWord(5, Vector('a')))
    ),
    "regex_no_base_nonempty" -> (() => regexNonempty(grammarNoBase)),
    "regex_with_base_nonempty" -> (() => regexNonempty(grammarWithBase)),
    "regex_derivative_nonempty" -> (() =>
      regexNonempty(regexDerivative("plain")(letter('b'))(grammarABStar))
    ),
    "regex_all_prefixes_plain" -> (() =>
      regexAllPrefixes("plain")(grammarAStar)(wordAOmega)
    ),
    "regex_all_prefixes_smart" -> (() =>
      regexAllPrefixes("smart")(grammarAStar)(wordAOmega)
    ),
    "regex_all_prefixes_unrolled" -> (() =>
      regexAllPrefixes("plain")(grammarAStar)(word("aaaaa"))
    ),
    "proof_evens_small" -> (() => evensCheck(3)),
    "proof_evens_medium" -> (() => evensCheck(8)),
    "proof_evens_large" -> (() => evensCheck(20)),
    "proof_evens_by_map_identity" -> (() =>
      checkEvens(
        fixpoint(
          λ(proof => cons(numeral(0))(cons(numeral(1))(map(identity)(proof))))
        )
      )(
        fixpoint(
          λ(stream => cons(numeral(0))(cons(numeral(2))(map(identity)(stream))))
        )
      )
    ),
    "proof_evens_by_map_successor" -> (() =>
      checkEvens(fixpoint(λ(proof => cons(zero)(map(successor)(proof)))))(
        fixpoint(
          λ(stream => cons(zero)(map(λ(n => successor(successor(n))))(stream)))
        )
      )
    ),
    "proof_evens_wrong_witness" -> (() =>
      checkEvens(cyclicLabels(Vector(0, 1, 3)))(cyclicLabels(Vector(0, 2, 4)))
    ),
    "proof_evens_odd_claim" -> (() =>
      checkEvens(cyclicLabels(Vector(0, 1, 2)))(cyclicLabels(Vector(0, 2, 5)))
    ),
    "proof_evens_unrolled" -> (() =>
      checkEvens(cyclicLabels(Vector(0, 1, 2)))(
        labelsList(Vector(0, 2, 4, 0, 2, 4), nil)
      )
    ),
    "proof_infinite_lasso" -> (() => checkInfinite(infiniteProof)(lasso(2, 3))),
    "proof_infinite_ones_by_map" -> (() =>
      checkInfinite(infiniteProof)(streamOnesByMap)
    ),
    "proof_infinite_finite_list" -> (() =>
      checkInfinite(infiniteProof)(acyclic(4))
    ),
    "circular_bisimulation_small" -> (() =>
      circularClaim(
        Vector(1 -> 0),
        Vector(1 -> 1, 1 -> 0),
        Contest.unfolded(2, CircularProof.Cite(1))
      )
    ),
    "circular_bisimulation_medium" -> (() =>
      circularClaim(
        Vector(1 -> 1, 2 -> 0),
        Vector(1 -> 1, 2 -> 2, 1 -> 3, 2 -> 0),
        Contest.unfolded(4, CircularProof.Cite(3))
      )
    ),
    "circular_bisimulation_false_claim" -> (() =>
      circularClaim(
        Vector(1 -> 0),
        Vector(1 -> 1, 2 -> 0),
        Contest.unfolded(2, CircularProof.Cite(1))
      )
    ),
    "circular_bisimulation_wrong_citation" -> (() =>
      circularClaim(
        Vector(1 -> 0),
        Vector(1 -> 1, 1 -> 0),
        Contest.unfolded(1, CircularProof.Cite(0))
      )
    ),
    "circular_bisimulation_unguarded" -> (() =>
      circularClaim(Vector(1 -> 0), Vector(2 -> 0), CircularProof.Cite(0))
    ),
    "type_basic_record" -> (() =>
      subtype(recordNamed("next" -> typeNatural, "value" -> typeNatural))(
        recordNamed("next" -> typeTop)
      )
    ),
    "type_self_record" -> (() =>
      subtype(selfRecord("next_first"))(nextOnlyRecord)
    ),
    "type_self_record_unrolled" -> (() =>
      subtype(unrolledSelfRecord(4, "next_first"))(unrolledNextOnlyRecord(4))
    ),
    "type_self_record_reversed" -> (() =>
      subtype(nextOnlyRecord)(selfRecord("value_first"))
    ),
    "type_self_record_reversed_unrolled" -> (() =>
      subtype(unrolledNextOnlyRecord(4))(unrolledSelfRecord(4, "value_first"))
    ),
    "type_this_subclass" -> (() => subtype(settableCellType)(cellType)),
    "type_this_superclass" -> (() => subtype(cellType)(settableCellType)),
    "type_binary_method" -> (() =>
      subtype(extendedComparableType)(comparableType)
    ),
    "type_binary_method_renamed" -> (() =>
      subtype(comparableType)(comparableType)
    ),
    "type_abstract_stack" -> (() => subtype(listStackType)(stackType)),
    "type_abstract_element_mismatch" -> (() =>
      subtype(containerType(7))(containerType(8))
    ),
    "type_operator_rebuilt_argument" -> (() =>
      subtype(nestOperator(typeNatural))(nestOperator(typeTop))
    )
  )

  private def evensCheck(count: Int): ProblemTerm =
    val (stream, proof) = evens(count)
    checkEvens(proof)(stream)

  /** The points, in the order `contest.pl` exports them. */
  def points: Vector[String] = pointTerms.map(_._1)

  /** The point's program. */
  def program(name: String): ProblemTerm =
    pointTerms
      .find(_._1 == name)
      .map(_._2())
      .getOrElse(
        throw IllegalArgumentException(s"$name is no point of contest.pl")
      )

/** The circular proofs' shapes. */
object Contest:

  /** The proof `unfold(... unfold(inner))`, `count` unfolds deep. */
  def unfolded(count: Int, inner: CircularProof): CircularProof =
    (1 to count).foldLeft(inner)((proof, _) => CircularProof.Unfold(proof))
