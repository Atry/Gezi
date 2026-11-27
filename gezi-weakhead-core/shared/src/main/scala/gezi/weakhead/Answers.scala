package gezi.weakhead

/** The answers of a nondeterministic computation over a state, one at a time,
  * in order: what a Prolog predicate gives on backtracking. Pulling the stream
  * runs the computation to its next answer and gives the answer with the stream
  * of the ones after it, or nothing when there are no more. Only what is pulled
  * is computed, so a caller that stops at the first answer that settles its
  * question never computes the rest, as a Prolog caller under `once/1` does
  * not.
  *
  * @param pull
  *   the computation of the next answer and the answers after it
  */
final case class Answers[State, Answer](
    pull: Computation[State, Option[(Answer, Answers[State, Answer])]]
):

  /** These answers, then the other's. */
  def appended(other: Answers[State, Answer]): Answers[State, Answer] =
    Answers(pull.flatMap {
      case None                 => other.pull
      case Some((answer, rest)) =>
        Computation.pure(Some((answer, rest.appended(other))))
    })

  /** For each answer in order, the answers the continuation gives of it. */
  def flatMap[Next](
      continuation: Answer => Answers[State, Next]
  ): Answers[State, Next] =
    Answers(pull.flatMap {
      case None                 => Computation.pure(None)
      case Some((answer, rest)) =>
        continuation(answer).appended(rest.flatMap(continuation)).pull
    })

  /** Each answer mapped. */
  def map[Next](mapping: Answer => Next): Answers[State, Next] =
    flatMap(answer => Answers.single(mapping(answer)))

  /** The answers that pass the test, which may compute. */
  def filtered(
      test: Answer => Computation[State, Boolean]
  ): Answers[State, Answer] =
    flatMap(answer =>
      Answers.computed(
        test(answer).map(passes =>
          if passes then Vector(answer) else Vector.empty
        )
      )
    )

  /** The answers, each once, in the order first given: an answer equal to one
    * already given is dropped as it is pulled. Only what is pulled is computed,
    * as for the stream itself, so a caller that stops early never computes the
    * rest.
    */
  def distinct: Answers[State, Answer] =
    Answers.distinctFrom(this, Set.empty)

  /** Every answer, in order: the computation runs to the end. */
  def collected: Computation[State, Vector[Answer]] =
    Answers.collectedFrom(this, Vector.empty)

  /** Every distinct answer, in the order first given: the computation runs to
    * the end, as for `collected`, but an answer equal to one already given is
    * dropped as it comes, so that what is held is the distinct answers and not
    * every answer. The same vector as `collected` followed by `distinct`.
    */
  def distinctCollected: Computation[State, Vector[Answer]] =
    Answers.distinctCollectedFrom(this, Vector.empty, Set.empty)

  /** Whether some answer passes the test, the answers pulled only until one
    * does (`once/1`).
    */
  def exists(
      test: Answer => Computation[State, Boolean]
  ): Computation[State, Boolean] =
    pull.flatMap {
      case None                 => Computation.pure(false)
      case Some((answer, rest)) =>
        test(answer).flatMap(passes =>
          if passes then Computation.pure(true) else rest.exists(test)
        )
    }

/** The constructions of answer streams. */
object Answers:

  /** No answer. */
  def empty[State, Answer]: Answers[State, Answer] = Answers(
    Computation.pure(None)
  )

  /** One answer. */
  def single[State, Answer](answer: Answer): Answers[State, Answer] =
    Answers(Computation.pure(Some((answer, empty))))

  /** The answers of the vector, in order. The stream is built from the last
    * answer to the first by `Vector.foldRight`, which walks the vector by a
    * loop, so no call stack grows with the vector's size.
    */
  def of[State, Answer](answers: Vector[Answer]): Answers[State, Answer] =
    answers.foldRight(empty[State, Answer])((answer, rest) =>
      Answers(Computation.pure(Some((answer, rest))))
    )

  /** The answers the computation gives all at once. */
  def computed[State, Answer](
      computation: Computation[State, Vector[Answer]]
  ): Answers[State, Answer] =
    Answers(computation.flatMap(answers => of(answers).pull))

  private def collectedFrom[State, Answer](
      answers: Answers[State, Answer],
      found: Vector[Answer]
  ): Computation[State, Vector[Answer]] =
    answers.pull.flatMap {
      case None                 => Computation.pure(found)
      case Some((answer, rest)) => collectedFrom(rest, found :+ answer)
    }

  private def distinctFrom[State, Answer](
      answers: Answers[State, Answer],
      seen: Set[Answer]
  ): Answers[State, Answer] =
    Answers(answers.pull.flatMap {
      case None => Computation.pure(None)
      case Some((answer, rest)) if seen.contains(answer) =>
        distinctFrom(rest, seen).pull
      case Some((answer, rest)) =>
        Computation.pure(Some((answer, distinctFrom(rest, seen + answer))))
    })

  private def distinctCollectedFrom[State, Answer](
      answers: Answers[State, Answer],
      found: Vector[Answer],
      seen: Set[Answer]
  ): Computation[State, Vector[Answer]] =
    answers.pull.flatMap {
      case None => Computation.pure(found)
      case Some((answer, rest)) if seen.contains(answer) =>
        distinctCollectedFrom(rest, found, seen)
      case Some((answer, rest)) =>
        distinctCollectedFrom(rest, found :+ answer, seen + answer)
    }
