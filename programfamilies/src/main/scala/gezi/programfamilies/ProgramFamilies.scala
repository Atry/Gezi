package gezi.programfamilies

import gezi.ir.{Configured, NoFacts}
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions

/** The configuration of the terms here: no facts. */
private given programFamiliesNoFacts: NoFacts.type = NoFacts

/** The programs of the two configurations ([[Configurations]]), written in the
  * HOAS over the library's terms, closed instructions read off
  * `TermTables.programFamilyLibraryTerms` by projection: the ports of the
  * Prolog generators `fixpoint_verdicts:family_value/3` and
  * `coverage_program/3` and of the size families of the Prolog cost
  * comparison's `program/3`, which the Prolog exporter of the fixtures copied
  * as `cost_comparison_program/3`. Each builds the same program as the Prolog
  * generator: the same applications, abstractions and names, in the same order.
  */
object ProgramFamilies:

  /** The members of the fixture `TermTables.programFamilyLibraryTerms`, the
    * library terms of native_types the program families are written with, each
    * a closed instruction read by projection (`StandardLibrary.entryMembers`),
    * so that a program names no library term.
    */
  private lazy val libraryTerms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        FixedPointLines.buildRoot,
        TermTables.programFamilyLibraryTerms,
        Expansions.none
      )
      ._1

  /** The library term of the name as a closed HOAS term (`Term.Closed`). */
  private def libraryTerm(name: String): ProgramTerm =
    Term.closed(
      libraryTerms.getOrElse(
        name,
        throw IllegalArgumentException(
          s"${TermTables.programFamilyLibraryTerms.file} has no member $name"
        )
      )
    )

  lazy val zero: ProgramTerm = libraryTerm("zero")
  lazy val successor: ProgramTerm = libraryTerm("successor")
  private lazy val nil = libraryTerm("nil")
  private lazy val cons = libraryTerm("cons")
  private lazy val trueValue = libraryTerm("true")
  private lazy val falseValue = libraryTerm("false")
  private lazy val booleanNot = libraryTerm("boolean_not")
  private lazy val identity = libraryTerm("identity")
  private lazy val konstant = libraryTerm("konstant")
  private lazy val compose = libraryTerm("compose")
  private lazy val naturalFold = libraryTerm("nat_fold")
  private lazy val listFold = libraryTerm("list_fold")
  lazy val fixpoint: ProgramTerm = libraryTerm("fixpoint")

  /** `successor (... (successor zero))` with `size` successors (`numeral/2`).
    */
  def numeral(size: Int): ProgramTerm =
    require(size >= 0, s"a numeral's size is not negative: $size")
    (1 to size).foldLeft(zero)((value, _) => successor(value))

  /** The list of `size` copies of the element, `cons element (... nil)`
    * (`list_of/3`); each copy is an occurrence of its own once through the
    * front end.
    */
  def listOf(element: ProgramTerm, size: Int): ProgramTerm =
    require(size >= 0, s"a list's size is not negative: $size")
    (1 to size).foldLeft(nil)((rest, _) => cons(element)(rest))

  /** A chain of `size` lambdas returning the first one's variable,
    * `λa1. ... λan. a1` (`family_value(chain, ...)`).
    */
  def chain(size: Int): ProgramTerm =
    require(size >= 1, s"a chain has at least one lambda: $size")
    λ(first => (1 until size).foldLeft(first)((body, _) => λ(_ => body)))

  /** `size` nested closures applied to zero,
    * `(λa. successor ((λb. successor (... b)) a)) zero` (`family_value(nested,
    * ...)` and `nested/3`).
    */
  def nested(size: Int): ProgramTerm =
    require(size >= 0, s"a nesting's size is not negative: $size")
    λ(parameter => nestedBody(size, parameter))(zero)

  /** `successor parameter` under `size` closures, each applied to the enclosing
    * parameter (`nested/3`).
    */
  private def nestedBody(size: Int, parameter: ProgramTerm): ProgramTerm =
    if size == 0 then successor(parameter)
    else successor(λ(inner => nestedBody(size - 1, inner))(parameter))

  /** The Scott tuple of `size` zeros,
    * `(λa1. ... λan. λk. k a1 ... an) zero ... zero` (`family_value(tuple,
    * ...)`).
    */
  def tuple(size: Int): ProgramTerm =
    require(size >= 1, s"a tuple has at least one component: $size")
    (1 to size).foldLeft(tupleClosure(size, Vector.empty))((function, _) =>
      function(zero)
    )

  /** The lambdas of the components not yet bound, then the continuation's
    * lambda, whose body applies it to every component in order (`tuple_body/3`
    * and `chain_built/3`).
    */
  private def tupleClosure(
      remaining: Int,
      components: Vector[ProgramTerm]
  ): ProgramTerm =
    if remaining == 0 then
      λ(continuation =>
        components.foldLeft[ProgramTerm](continuation)((function, component) =>
          function(component)
        )
      )
    else λ(component => tupleClosure(remaining - 1, components :+ component))

  /** `nat_fold zero (compose successor successor) numeral` with a numeral of
    * `size` successors (`program(folds, ...)` of the Prolog cost comparison).
    */
  def fold(size: Int): ProgramTerm =
    naturalFold(zero)(compose(successor)(successor))(numeral(size))

  /** The programs of `coverage_program/3`, by name, in the order of that file.
    */
  val coverage: Vector[(String, ProgramTerm)] = Vector(
    "successor_zero" -> successor(zero),
    "successor_successor_zero" -> successor(successor(zero)),
    "boolean_not_true" -> booleanNot(trueValue),
    "identity_lambda" -> λ(variable => variable),
    "konstant_lambda" -> λ(kept => λ(_ => kept)),
    "identity_zero" -> identity(zero),
    "successor_redex" -> λ(argument => successor(argument))(zero),
    "compose_redex" ->
      λ(outer => λ(inner => λ(argument => outer(inner(argument)))))(successor)(
        successor
      )(zero),
    "x5" -> cons(zero)(nil),
    "x3" -> cons(cons(successor(zero))(nil))(cons(nil)(nil)),
    "nil_first" -> cons(nil)(cons(cons(zero)(nil))(nil)),
    "applied_booleans" ->
      cons(identity(trueValue))(
        cons(naturalFold(trueValue)(konstant(falseValue))(identity(zero)))(nil)
      ),
    "x7" -> cons(successor(zero))(cons(falseValue)(nil)),
    "x2" -> naturalFold(zero)(compose(successor)(successor))(successor(zero)),
    "x1" -> listFold(zero)(konstant(successor))(cons(zero)(nil)),
    "x4" -> naturalFold(zero)(trueValue)(successor(zero)),
    "x9" -> naturalFold(zero)(compose(successor)(successor)),
    "double_successor" -> λ(argument => successor(successor(argument))),
    "cons_zero" -> cons(zero),
    "compose_cons" -> compose(cons(zero))(konstant(nil)),
    "twice" -> λ(function => λ(argument => function(function(argument))))(
      successor
    )(zero),
    "list_copy" ->
      listFold(nil)(λ(head => λ(accumulated => cons(head)(accumulated))))(
        cons(zero)(nil)
      ),
    "list_successors" ->
      listFold(nil)(
        λ(head => λ(accumulated => cons(successor(head))(accumulated)))
      )(cons(zero)(nil)),
    "self_application" -> λ(variable => variable(variable)),
    "closure_parameter_used_at_two_types" ->
      λ(closure =>
        naturalFold(closure(falseValue))(booleanNot)(closure(successor(zero)))
      )(λ(variable => variable)),
    "scott_successor_applied" ->
      λ(predecessor => λ(_ => λ(step => step(predecessor))))(zero)(trueValue)(
        identity
      ),
    "konstant_inline" -> λ(kept => λ(_ => kept))(successor)(zero),
    "scott_cons_applied" ->
      λ(head => λ(tail => λ(_ => λ(step => step(head)(tail)))))(zero)(nil)(
        trueValue
      )(konstant),
    "identity_lambda_applied_to_itself" -> λ(first => first)(
      λ(second => second)
    ),
    "identity_lambda_at_two_types" ->
      λ(first => first)(successor)(λ(second => second)(zero)),
    "identity_lambda_on_zero" -> successor(λ(variable => variable)(zero)),
    "fold_of_identity_lambdas" ->
      naturalFold(λ(first => first)(successor(zero)))(
        λ(second => second)(successor)
      )(zero),
    "konstant_applications_at_two_types" ->
      cons(konstant(successor(zero))(successor(zero)))(
        cons(konstant(successor(zero))(successor))(nil)
      ),
    "closures_nested_at_zero" ->
      λ(outer => λ(inner => konstant(inner)(outer))(zero))(zero),
    "zero_chosen_by_its_context" -> booleanNot(λ(variable => variable)(zero)),
    "fixpoint_of_a_successor_closure" -> fixpoint(
      λ(recursive => successor(recursive))
    ),
    "successor_of_a_fixpoint_of_identity" -> successor(
      fixpoint(λ(variable => variable))
    )
  )
