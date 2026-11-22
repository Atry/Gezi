package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** The substrings that are a concatenation of every word, the port of `problems/hidden_37_concatenation`.
  */
object Hidden37Concatenation:

  private val family = "hidden_37_concatenation"

  /** The kind of a point, the constructors of
    * problems/hidden_37_concatenation/kind in order: the subtask, whose
    * string is as drawn, and the trap, whose string no window matches.
    */
  enum Kind:
    case Subtask, Trap

  /** The kind a field writes, a constructor of
    * problems/hidden_37_concatenation/kind read by its position
    * (`ProblemData.alternative`).
    */
  def kind(field: ProblemField): Kind =
    ProblemData.alternative(field, Kind.values.size) match
      case (position, Vector()) => Kind.fromOrdinal(position)
      case (_, fields)          => throw IllegalArgumentException(s"the kind of $family has ${fields.size} fields")

  /** The program (`concatenation_term/3`):
    * `(\words. (\pick. \drop. (\fit. Body) Fit) Pick Drop) Words`.
    */
  def concatenationTerm(attractors: Attractors, string: Vector[Int], words: Vector[Vector[Int]]): Term =
    val length = attractors.functionSurface("length", Spelling.Direct)
    val concat = attractors.functionSurface("concat", Spelling.Direct)
    λ(wordsVariable =>
      λ(pick =>
        λ(drop =>
          λ(fit =>
            λ(total => startsFunction(attractors, fit, wordsVariable, total)(SetFree.booleanList(attractors, string))(unary(0)))(
              length(concat(wordsVariable))
            )
          )(fitFunction(attractors, pick, drop))
        )
      )(pickFunction(attractors))(dropFunction(attractors))
    )(SetFree.bitLists(attractors, words))

  /** Each word picked, the rest passed on (`pick_function/1`). */
  private def pickFunction(attractors: Attractors): Term =
    val cons = attractors.attractorSurface("cons", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(words =>
          λ(function =>
            words(top)(λ(word =>
              λ(rest =>
                members(
                  Vector(function(word)(rest), self(rest)(λ(other => λ(others => function(other)(cons(word)(others))))))
                )
              )
            ))
          )
        )
      )
    )

  /** The string with its first n elements dropped (`drop_function/1`). */
  def dropFunction(attractors: Attractors): Term =
    val nil = attractors.attractorSurface("nil", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(count => λ(string => count(string)(λ(predecessor => string(nil)(λ(_ => λ(tail => self(predecessor)(tail))))))))
      )
    )

  /** The words fitted onto the string in some order (`fit_function/3`). */
  private def fitFunction(attractors: Attractors, pick: Term, drop: Term): Term =
    val prefix = attractors.functionSurface("bits_prefix", Spelling.Direct)
    val length = attractors.functionSurface("length", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(words =>
          λ(string =>
            λ(index =>
              words(index)(λ(_ =>
                λ(_ =>
                  pick(words)(λ(word =>
                    λ(rest => prefix(word)(string)(self(rest)(drop(length(word))(string))(index))(top))
                  ))
                )
              ))
            )
          )
        )
      )
    )

  /** Every start whose window the words fit (`starts_function/4`). */
  private def startsFunction(attractors: Attractors, fit: Term, words: Term, total: Term): Term =
    val atLeast = attractors.functionSurface("natural_at_least", Spelling.Direct)
    val length = attractors.functionSurface("length", Spelling.Direct)
    val successor = attractors.functionSurface("successor", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(string =>
          λ(index =>
            members(
              Vector(
                atLeast(length(string))(total)(fit(words)(string)(index))(top),
                string(top)(λ(_ => λ(tail => self(tail)(successor(index)))))
              )
            )
          )
        )
      )
    )

  /** The starts of the windows of the string that are a concatenation of
    * the words in some order, by sorting the window's pieces
    * (`window_starts/3`).
    */
  def windowStarts(string: Vector[Int], words: Vector[Vector[Int]]): Vector[Int] =
    val width = words.head.size
    val span = width * words.size
    val sorted = words.sortWith(lexicographicallyBefore)
    (0 to string.size - span).toVector.filter(position =>
      string.slice(position, position + span).grouped(width).toVector.sortWith(lexicographicallyBefore) == sorted
    )

  private def lexicographicallyBefore(left: Vector[Int], right: Vector[Int]): Boolean =
    left.zip(right).find(_ != _).map(_ < _).getOrElse(left.size < right.size)

  private def next(state: Long): Long = DynamicReferences.nextRandom(state)

  /** The elements in a random order, each drawn by `(Next >> 16) mod Length`
    * (`shuffled/4`).
    */
  private def shuffled[Element](elements: Vector[Element], state: Long): (Vector[Element], Long) =
    elements.indices.foldLeft((Vector.empty[Element], elements, state)) { case ((order, rest, current), _) =>
      val following = next(current)
      val index = ((following >> 16) % rest.size).toInt
      (order :+ rest(index), rest.patch(index, Vector.empty, 1), following)
    } match
      case (order, _, finalState) => (order, finalState)

  /** The words of a point and the state after them (`point_words/6`). */
  private def pointWords(width: Int, count: Int, distinct: Int, seed: Long): (Vector[Vector[Int]], Long) =
    val (codes, afterShuffle) = shuffled((0 until (1 << width)).toVector, seed)
    val alphabet = codes.take(distinct).map(code => (width - 1 to 0 by -1).toVector.map(bit => (code >> bit) & 1))
    (1 to count).foldLeft((Vector.empty[Vector[Int]], afterShuffle)) { case ((words, state), _) =>
      val following = next(state)
      (words :+ alphabet(((following >> 16) % alphabet.size).toInt), following)
    }

  /** Noise of 1 to 5 random bits (`noise/3`). */
  private def noise(state: Long): (Vector[Int], Long) =
    val sized = next(state)
    val size = ((sized >> 16) % 5 + 1).toInt
    val bits = DynamicReferences.states(sized, size)
    (bits.map(bitState => ((bitState >> 20) & 1).toInt), bits.lastOption.getOrElse(sized))

  /** Three rounds, each noise, a hit, noise and a near order, the pieces of
    * each round before the rounds before it (`point_string/3`).
    */
  private def pointString(words: Vector[Vector[Int]], state: Long): Vector[Int] =
    (1 to 3)
      .foldLeft((state, List.empty[Vector[Int]])) { case ((current, pieces), _) =>
        val (noiseOne, stateOne) = noise(current)
        val (order, stateTwo) = shuffled(words, stateOne)
        val (noiseTwo, stateThree) = noise(stateTwo)
        val (orderTwo, stateFour) = shuffled(words, stateThree)
        val stateFive = next(stateFour)
        val other = words.find(_ != orderTwo.head).getOrElse(throw IllegalArgumentException("no other word"))
        (stateFive, noiseOne :: order.flatten :: noiseTwo :: (other +: orderTwo.tail).flatten :: pieces)
      }
      ._2
      .toVector
      .flatten

  /** The string with the middle bit of its first window flipped until no
    * window remains (`trap_string/4`).
    */
  @tailrec
  private def trapString(string: Vector[Int], words: Vector[Vector[Int]], span: Int): Vector[Int] =
    windowStarts(string, words).headOption match
      case None => string
      case Some(start) =>
        val middle = start + span / 2
        trapString(string.updated(middle, 1 - string(middle)), words, span)

  /** The string and words of a point (`point_problem/3`). */
  def pointProblem(group: ReductionGroup, point: String): (Vector[Int], Vector[Vector[Int]]) =
    group.problems(family).keyed("concatenation_point").get(point) match
      case Some(Vector(width, count, distinct, seed, kind)) =>
        val widthValue = ProblemData.small(width)
        val (words, state) =
          pointWords(widthValue, ProblemData.small(count), ProblemData.small(distinct), ProblemData.small(seed))
        val original = pointString(words, state)
        val string = this.kind(kind) match
          case Kind.Subtask => original
          case Kind.Trap    => trapString(original, words, widthValue * ProblemData.small(count))
        (string, words)
      case other => throw IllegalArgumentException(s"no concatenation point $point: $other")

  /** The problems (`concatenation_point/6`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("concatenation_point").map(arguments =>
      val point = ProblemData.text(arguments.head)
      val (string, words) = pointProblem(group, point)
      ReductionProblem(
        point,
        concatenationTerm(group.attractors, string, words),
        "unary",
        Reduction.expectedOf(windowStarts(string, words).map(Scott.unaryTree)),
        Reduction.hiddenLimits
      )
    )
