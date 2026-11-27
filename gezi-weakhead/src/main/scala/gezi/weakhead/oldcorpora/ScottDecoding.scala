package gezi.weakhead.oldcorpora

import gezi.weakhead.Answers
import gezi.weakhead.Computation
import gezi.weakhead.Computed
import gezi.weakhead.Head
import gezi.weakhead.Mode
import gezi.weakhead.NeutralValue
import gezi.weakhead.NeutralVariable
import gezi.weakhead.ParallelSet
import gezi.weakhead.ReadingState
import gezi.weakhead.Resource
import gezi.ir.Value
import gezi.weakhead.WeakHead
import gezi.frontend.Term
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer}

/** A Scott data type of the problem corpora, its constructors in the order the
  * encoding takes its cases.
  */
enum ScottDataType:

  /** The Church booleans of the prelude, true = \t. \f. t. */
  case Booleans

  /** The prelude's Scott naturals, zero = \z. \s. z and successor p = \z. \s. s
    * p; zero is the same term as true.
    */
  case Unary

  /** The label-free binary naturals of `problems/merge_dynamic`, zero = \z. \e.
    * \o. z, even h = \z. \e. \o. e h, odd h = \z. \e. \o. o h, of value 0, 2h
    * and 2h + 1.
    */
  case Binary

  /** The constructors, each with the types of its fields, in the encoding's
    * order.
    */
  def constructors: Vector[ScottConstructor] = this match
    case Booleans =>
      Vector(
        ScottConstructor("true", Vector.empty),
        ScottConstructor("false", Vector.empty)
      )
    case Unary =>
      Vector(
        ScottConstructor("zero", Vector.empty),
        ScottConstructor("successor", Vector(Unary))
      )
    case Binary =>
      Vector(
        ScottConstructor("zero", Vector.empty),
        ScottConstructor("even", Vector(Binary)),
        ScottConstructor("odd", Vector(Binary))
      )

/** A constructor of a Scott data type: its name and the types of its fields.
  */
final case class ScottConstructor(
    name: String,
    fieldTypes: Vector[ScottDataType]
)

/** A constructor tree, or a head that is no constructor of its level. */
enum ConstructorTree:

  /** The constructor of the name over the trees of its fields. */
  case Constructor(name: String, subtrees: Vector[ConstructorTree])

  /** A head that is no constructor of the type at its level; it claims no
    * normal form.
    */
  case IllFormed

/** The outcome of `ScottDecoding.meaningConfirmed`: an answer when the decoding
  * finished, or how it stopped, which answers nothing.
  */
enum Confirmation:

  /** The decoding finished and answers the tree and nothing else. */
  case Confirmed

  /** The decoding finished and answers something other than the tree alone.
    */
  case NotConfirmed

  /** The decoding ran past its budget of steps. */
  case LimitReached

  /** The decoding ran out of a resource first. */
  case Exhausted(resource: Resource)

/** The case of a constructor at a field's depth, the Prolog decoder's
  * `case(Level, Name)`: a value no closed program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here: it stands for a binder of the
  * value read (a Scott value's handler, a constructor's or a define's
  * parameter), opened to read the value's head, as the normal-form reader's
  * `BoundVariable` opens a lambda, whose Scaladoc has the argument. A closed
  * term in its place would not do: a term that is no such value could ignore it
  * and build the reading itself.
  */
final case class ScottCase(level: Int, name: String) extends NeutralVariable

/** Scott case analysis: a term read as data by applying it to its cases. The
  * port of `gezi/prolog/gezi/old_corpora/scott_decoding.pl`, the contest's
  * reading of an output, for the problem corpora only: it encodes their
  * numerals and reads their answers, and the pipeline (the library, the
  * strategies, the compilation) must not use it; its data types are tables of
  * the corpora, never a type of a term. It moves to the module `corpora` when
  * that module is written.
  *
  * THE DECODING, on the weak-head evaluator: `decoded(mode, term, dataType)`
  * applies the closed term to one neutral value per constructor,
  * `ScottCase(level, name)` with the level the field's depth, and takes the
  * heads of the application. A neutral value of the case of a constructor of
  * this level over as many arguments as the constructor has fields names the
  * constructor, and each argument is decoded at its field's type one level
  * deeper. Any other head reads `IllFormed`. Each level has its own cases, so a
  * field that answers an outer level's case reads `IllFormed`: with one set of
  * cases for every level, `\z. \e. \o. e (\z1. \e1. \o1. e zero)` would read as
  * even (even zero), which it is not beta equal to.
  *
  * Every tree of every head is an answer, never the first only: under a choice
  * every combination of the fields' trees is an answer.
  *
  * WHY A TREE IS AN ANSWER: T ⊑ c(t) for the canonical term c(t) of a decoded
  * tree with no `IllFormed`, by the derivation of the Prolog module comment, so
  * T ⊑_O c(t). THE PARALLEL'S READ-OUT: a parallel set of several heads answers
  * each tree its first head decodes to that every other head decodes to as
  * well, at the same level, each head decoded whole. `IllFormed` is no tree of
  * a head, so a set all of whose heads are ill-formed answers nothing, and when
  * a head has no tree the heads after it are not decoded, the set having none
  * whatever they do. With it top = Y (λz. λx. z ∥ x), the term that stands for
  * no answer, decodes to nothing at every data type: top applied to the cases
  * is a parallel set that holds the abstraction λx. top ∥ x, which is no
  * constructor.
  */
object ScottDecoding:

  /** The constructor trees of the closed term at the data type under the mode,
    * one at a time.
    */
  def decoded[C <: NativeSpecializer & Singleton](
      mode: Mode,
      term: Value[C],
      dataType: ScottDataType
  )(using C): Answers[ReadingState[C], ConstructorTree] =
    decodedAt(mode, 0, term, dataType)

  private def decodedAt[C <: NativeSpecializer & Singleton](
      mode: Mode,
      level: Int,
      term: Value[C],
      dataType: ScottDataType
  )(using C): Answers[ReadingState[C], ConstructorTree] =
    val constructors = dataType.constructors
    val applied = constructors.foldLeft(term)((function, constructor) =>
      Value.Apply(
        function,
        NeutralValue[C](ScottCase(level, constructor.name), Vector.empty)
      )
    )
    WeakHead.heads(mode, applied).flatMap(setTree(mode, level, constructors, _))

  /** The trees of a parallel set: of its head when it has one; when it has
    * several, the trees every one of them decodes to (THE PARALLEL'S READ-OUT);
    * none of the empty parallel set, of which every tree is an answer and this
    * decoding, which gives its trees one at a time, gives none (a known
    * incompleteness).
    */
  private def setTree[C <: NativeSpecializer & Singleton](
      mode: Mode,
      level: Int,
      constructors: Vector[ScottConstructor],
      set: ParallelSet[C]
  )(using C): Answers[ReadingState[C], ConstructorTree] =
    set.heads.toList match
      case Nil             => Answers.empty
      case single :: Nil   => headTree(mode, level, constructors, single)
      case first :: others =>
        Answers.computed(
          headTrees(mode, level, constructors, first).flatMap(firstTrees =>
            Computation.folded(others.toVector, firstTrees)((trees, head) =>
              if trees.isEmpty then Computation.pure(trees)
              else
                headTrees(mode, level, constructors, head).map(found =>
                  val foundSet = found.toSet
                  trees.filter(foundSet.contains)
                )
            )
          )
        )

  private def headTree[C <: NativeSpecializer & Singleton](
      mode: Mode,
      level: Int,
      constructors: Vector[ScottConstructor],
      head: Head[C]
  )(using C): Answers[ReadingState[C], ConstructorTree] = head match
    case gezi.weakhead.Neutral(ScottCase(`level`, name), fields) =>
      constructors.find(_.name == name) match
        case Some(constructor) if constructor.fieldTypes.size == fields.size =>
          fieldsDecoded(
            mode,
            level + 1,
            fields.zip(constructor.fieldTypes),
            0,
            Vector.empty
          )
            .map(ConstructorTree.Constructor(name, _))
        case _ => Answers.single(ConstructorTree.IllFormed)
    case gezi.weakhead.Neutral(_, _) | gezi.ir.Thunk(_, _, _) =>
      Answers.single(ConstructorTree.IllFormed)

  /** The trees of one head of a parallel set of several, decoded whole, each
    * once, without `IllFormed`: a head that is no constructor of the level
    * claims no normal form, so it is no tree the heads can share.
    */
  private def headTrees[C <: NativeSpecializer & Singleton](
      mode: Mode,
      level: Int,
      constructors: Vector[ScottConstructor],
      head: Head[C]
  )(using C): Computation[ReadingState[C], Vector[ConstructorTree]] =
    headTree(mode, level, constructors, head).collected
      .map(_.distinct.filter(_ != ConstructorTree.IllFormed))

  /** The trees of the fields from the index on, each later field decoded for
    * each tree of the earlier ones.
    */
  private def fieldsDecoded[C <: NativeSpecializer & Singleton](
      mode: Mode,
      level: Int,
      fields: Vector[(Value[C], ScottDataType)],
      index: Int,
      subtrees: Vector[ConstructorTree]
  )(using C): Answers[ReadingState[C], Vector[ConstructorTree]] =
    if index >= fields.size then Answers.single(subtrees)
    else
      val (field, fieldType) = fields(index)
      decodedAt(mode, level, field, fieldType).flatMap(subtree =>
        fieldsDecoded(mode, level, fields, index + 1, subtrees :+ subtree)
      )

  /** Whether the term's meaning at the data type is the tree: its decoding
    * under tabling(weak_head), one reading from an empty store within the limit
    * of steps, answers the tree and nothing else (`Confirmed`), or finishes
    * with other answers (`NotConfirmed`); a decoding that runs past the limit,
    * or out of the tables, answers neither (the Prolog predicate had no limit).
    */
  def meaningConfirmed(
      term: Value[gezi.ir.NoFacts.type],
      dataType: ScottDataType,
      tree: ConstructorTree,
      limit: Long
  )(using gezi.ir.NoFacts.type): Confirmation =
    decoded(Mode.TablingWeakHead, term, dataType).collected.result(
      ReadingState.fresh(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
    ) match
      case Computed.Done(trees, _) =>
        if trees.distinct == Vector(tree) then Confirmation.Confirmed
        else Confirmation.NotConfirmed
      case Computed.Stopped(after) =>
        after.exhausted match
          case Some(resource) => Confirmation.Exhausted(resource)
          case None           => Confirmation.LimitReached

  /** The canonical closed term of the tree at the data type,
    * `\c1. ... \cn. ci s1 ... sk` with each si the term of a subtree, in the
    * HOAS of the front end. Throws `IllegalArgumentException` for a tree that
    * is not one of the type's. Trampolined, so that the deep trees of the large
    * problems take no JVM stack: the recursion by `map` overflowed the forked
    * test JVM's stack on the snapshots of set_free_scope_large_direct,
    * _respelled and _near_miss in one full `sbt test` of 2026-10-31 and not in
    * another, as the JIT compilation of its frames happened to come before the
    * deep tree or after.
    */
  def treeSurface(dataType: ScottDataType, tree: ConstructorTree): Term =
    surfaceOf(dataType, tree).result

  private def surfaceOf(
      dataType: ScottDataType,
      tree: ConstructorTree
  ): TailRec[Term] = tree match
    case ConstructorTree.Constructor(name, subtrees) =>
      val constructors = dataType.constructors
      val index = constructors.indexWhere(_.name == name)
      require(index >= 0, s"$name is no constructor of $dataType")
      val constructor = constructors(index)
      require(
        constructor.fieldTypes.size == subtrees.size,
        s"$name has ${constructor.fieldTypes.size} fields"
      )
      TailRecFolds
        .folded(
          constructor.fieldTypes.zip(subtrees).toVector,
          Vector.empty[Term]
        ) { case (before, (fieldType, subtree)) =>
          surfaceOf(fieldType, subtree).map(before :+ _)
        }
        .map(fields =>
          casesBound(constructors.size, Vector.empty)(cases =>
            fields.foldLeft(cases(index))((function, field) => function(field))
          )
        )
    case ConstructorTree.IllFormed =>
      throw IllegalArgumentException("an ill-formed tree has no canonical term")

  private def casesBound(count: Int, cases: Vector[Term])(
      body: Vector[Term] => Term
  ): Term =
    if cases.size == count then body(cases)
    else Term.λ(next => casesBound(count, cases :+ next)(body))

  /** The canonical binary tree of the natural: no even over zero. */
  def binaryTree(natural: BigInt): ConstructorTree =
    require(natural >= 0, s"a natural is not negative: $natural")
    if natural == 0 then ConstructorTree.Constructor("zero", Vector.empty)
    else
      val half = binaryTree(natural / 2)
      if natural % 2 == 0 then ConstructorTree.Constructor("even", Vector(half))
      else ConstructorTree.Constructor("odd", Vector(half))
