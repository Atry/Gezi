package gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term
import gezi.frontend.Term.*

/** Generators of closed object terms in the HOAS of `gezi.frontend.Term`.
  *
  * A term under binders is generated as an OPEN term, a function from the
  * variables bound outside it (outermost first) to a term; an abstraction's
  * body is the open term applied to the outer variables and the abstraction's
  * own, so the HOAS function is built from generated data and Hedgehog
  * shrinks that data. A closed term is an open term applied to no variable.
  */
object HoasGenerators:

  /** A term as a function of the variables bound outside it. */
  type Open = Vector[Term] => Term

  /** Closed terms of every construct: abstraction, application, choice
    * (choices of two to four members, choices nested in choices), parallel and variables, each at
    * function and argument positions, under binders and nested; one node in
    * eight repeats a subterm it has just generated (`t t`, `t + t`,
    * `t ∥ t`), so that equal closed subterms occur, which interning and
    * defunctionalization share. No choice has one member: such a choice has
    * no lambdalattice spelling, so the text law cannot use it (a test that
    * needs one writes `choice(t)` itself). Hedgehog's size bounds the nodes
    * at half of it, so at most 50; deep terms are `deepTerm`'s.
    */
  def closedTerm: Gen[Term] = closedTermOver(Vector.empty)

  /** The closed terms of `closedTerm` that also hold the library terms as
    * leaves, at function and argument positions: closed terms
    * (`Term.Closed`) a test read off a fixture file by projection, never a
    * name.
    */
  def closedTermOver(libraryTerms: Vector[Term]): Gen[Term] =
    Gen.sized(size => openTermOver(0, size.value / 2, libraryTerms)).map(_(Vector.empty))

  /** The open terms of `closedTerm` under `depth` binders, of at most
    * `nodes` nodes.
    */
  def openTerm(depth: Int, nodes: Int): Gen[Open] = openTermOver(depth, nodes, Vector.empty)

  /** The open terms of `closedTermOver` under `depth` binders, of at most
    * `nodes` nodes.
    */
  def openTermOver(depth: Int, nodes: Int, libraryTerms: Vector[Term]): Gen[Open] =
    val variable =
      if depth == 0 then Nil
      else List(3 -> Gen.int(Range.constant(0, depth - 1)).map(level => (outer: Vector[Term]) => outer(level)))
    val library =
      libraryTerms match
        case first +: rest => List(2 -> Gen.element(first, rest.toList).map(term => (_: Vector[Term]) => term))
        case _             => Nil
    val leaves = variable ++ library
    // With no binder and no library term there is no leaf: the term is an
    // abstraction, whose body has its variable as a leaf.
    lazy val abstraction = openTermOver(depth + 1, nodes - 1, libraryTerms).map(body =>
      (outer: Vector[Term]) => λ(bound => body(outer :+ bound))
    )
    if leaves.isEmpty then abstraction
    else
      val leaf = Gen.frequency(leaves.head, leaves.tail)
      if nodes <= 1 then leaf
      else
        val half = (nodes - 1) / 2
        val smaller = openTermOver(depth, half, libraryTerms)
        Gen.frequency1(
          2 -> leaf,
          3 -> abstraction,
          3 -> (for function <- smaller; argument <- smaller
          yield (outer: Vector[Term]) => function(outer)(argument(outer))),
          1 -> (for
            count <- Gen.int(Range.linear(2, 4))
            members <- openTermOver(depth, (nodes - 1) / count, libraryTerms).list(Range.singleton(count))
          yield (outer: Vector[Term]) => choice(members.map(_(outer))*)),
          1 -> (for left <- smaller; right <- smaller
          yield (outer: Vector[Term]) => left(outer) ∥ right(outer)),
          1 -> (for
            shared <- smaller
            combine <- Gen.element1[(Term, Term) => Term](
              (first, second) => first(second),
              (first, second) => choice(first, second),
              (first, second) => first ∥ second
            )
          yield (outer: Vector[Term]) => combine(shared(outer), shared(outer)))
        )

  /** The IR of generated closed terms through the front end: the terms of
    * `closedTerm`, converted and defunctionalized
    * (`Defunctionalization.thunkInstruction`); every thunk is well formed. A
    * test that needs an ill-formed thunk takes `PlantedDefects.malformedThunk`.
    */
  def instruction: Gen[gezi.ir.Instruction] =
    closedTerm
      .map(term => gezi.frontend.Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty)))

  /** Closed instructions as the evaluator makes them: the front end's
    * (`instruction`) combined `size` levels deep by a thunk with its first
    * hole filled by an argument (the evaluator's partial application, which
    * keeps the code as it is, so that the thunk's term is no longer the front
    * end's spelling of it), an application, a choice and a parallel.
    */
  def evaluatorInstruction(size: Int): Gen[gezi.ir.Instruction] =
    if size <= 1 then instruction
    else
      val smaller = evaluatorInstruction(size / 2)
      Gen.frequency1(
        2 -> instruction,
        3 -> (for function <- smaller; argument <- smaller yield applied(function, argument)),
        1 -> (for left <- smaller; right <- smaller yield gezi.ir.Instruction.Choice(left, right)),
        1 -> (for left <- smaller; right <- smaller yield gezi.ir.Instruction.Parallel(left, right))
      )

  /** The thunk with its first hole filled by the argument, as the evaluator
    * applies a thunk of two or more holes; the application of the function
    * to the argument otherwise.
    */
  private def applied(function: gezi.ir.Instruction, argument: gezi.ir.Instruction): gezi.ir.Instruction =
    import gezi.ir.Hole
    import gezi.ir.Instruction
    function match
      case Instruction.Thunk(code, Hole.Ignored +: rest, fillings) if rest.nonEmpty =>
        Instruction.Thunk(code, rest, fillings)
      case Instruction.Thunk(code, Hole.Bound(slot) +: rest, fillings) if rest.nonEmpty =>
        Instruction.Thunk(
          code,
          rest,
          fillings.patch(gezi.frontend.Defunctionalization.fillingPosition(rest, slot), Vector(argument), 0)
        )
      case _ => Instruction.Apply(function, argument)

  /** `λx. x x ... x` with `copies` occurrences of x, two or more. */
  def selfApplication(copies: Int): Term =
    require(copies >= 2, s"a self-application applies x to itself at least once: $copies")
    λ(x => (2 to copies).foldLeft(x)((function, _) => function(x)))

  /** Terms with no head, whose weak-head evaluation re-enters itself: Ω =
    * (λx. x x)(λx. x x), its variants with more copies, (λx. x x x)(λx. x x x)
    * among them, mixed pairs such as (λx. x x)(λx. x x x), whose evaluation
    * grows, and each applied to zero to two closed arguments of `closedTerm`.
    * Untabled reading runs out of any budget on them; tabled reading of Ω
    * finds that it has no head.
    */
  def headlessTerm: Gen[Term] =
    for
      functionCopies <- Gen.int(Range.linear(2, 3))
      argumentCopies <- Gen.frequency1(3 -> Gen.constant(functionCopies), 1 -> Gen.int(Range.linear(2, 3)))
      arguments <- closedTerm.list(Range.linear(0, 2))
    yield arguments.foldLeft(selfApplication(functionCopies)(selfApplication(argumentCopies)))(
      (function, argument) => function(argument)
    )

  /** Closed pure terms in βη normal form: no application of an abstraction
    * and no η-redex λx. M x with x not free in M. A normal form is an
    * abstraction or a variable applied to normal forms; a closed one starts
    * with an abstraction. The named cases: the identity λx. x, the numerals
    * λf. λx. f (f x), λx. λy. y x, and K = λx. λy. x. Generated by
    * construction and filtered for η-redexes (`hasEtaRedex`).
    */
  val normalForm: Gen[Term] =
    Gen
      .sized(size => normalFormOpen(0, size.value / 2))
      .map(_(Vector.empty))
      .filter(term => !hasEtaRedex(term.deBruijnTerm(Map.empty)))

  private def normalFormOpen(depth: Int, nodes: Int): Gen[Open] =
    // Lazy: the test of `nodes` below must come before it is built, or the
    // recursion has no end.
    lazy val abstraction =
      normalFormOpen(depth + 1, nodes - 1).map(body => (outer: Vector[Term]) => λ(bound => body(outer :+ bound)))
    if depth == 0 then abstraction
    else
      val neutral = for
        head <- Gen.int(Range.constant(0, depth - 1))
        count <- Gen.int(Range.linear(0, math.min(3, math.max(0, nodes - 1))))
        arguments <- normalFormOpen(depth, (nodes - 1) / math.max(1, count)).list(Range.singleton(count))
      yield (outer: Vector[Term]) => arguments.foldLeft(outer(head))((function, argument) => function(argument(outer)))
      if nodes <= 1 then neutral else Gen.frequency1(1 -> abstraction, 2 -> neutral)

  /** Closed terms with an η-redex λx. M x, x not free in M, under zero to
    * two binders that M may use: λy. λx. y x, λx. (λz. z) x, M any open term
    * of `openTerm`.
    */
  def etaRedexTerm: Gen[Term] =
    for
      depth <- Gen.int(Range.linear(0, 2))
      function <- Gen.sized(size => openTerm(depth, size.value / 4))
    yield
      def under(outer: Vector[Term]): Term =
        if outer.size == depth then λ(bound => function(outer)(bound))
        else λ(next => under(outer :+ next))
      under(Vector.empty)

  /** Whether the de Bruijn term holds an η-redex `λ. M 0` with the variable
    * 0 not free in M. Recursive on the term's depth: for generated terms of
    * at most 50 nodes.
    */
  def hasEtaRedex(term: DeBruijnTerm): Boolean = term match
    case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(0)))
        if !occurs(function, 0) =>
      true
    case DeBruijnTerm.Lambda(body)              => hasEtaRedex(body)
    case DeBruijnTerm.Apply(function, argument) => hasEtaRedex(function) || hasEtaRedex(argument)
    case DeBruijnTerm.Choice(left, right)       => hasEtaRedex(left) || hasEtaRedex(right)
    case DeBruijnTerm.Parallel(left, right)     => hasEtaRedex(left) || hasEtaRedex(right)
    case DeBruijnTerm.Variable(_) | DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_) => false

  private def occurs(term: DeBruijnTerm, index: Int): Boolean = term match
    case DeBruijnTerm.Variable(found)           => found == index
    case DeBruijnTerm.Lambda(body)              => occurs(body, index + 1)
    case DeBruijnTerm.Apply(function, argument) => occurs(function, index) || occurs(argument, index)
    case DeBruijnTerm.Choice(left, right)       => occurs(left, index) || occurs(right, index)
    case DeBruijnTerm.Parallel(left, right)     => occurs(left, index) || occurs(right, index)
    case DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_) => false

  /** A Scott data type: for each constructor, in the order the encoding
    * takes its cases, the kinds of its fields.
    */
  final case class ScottDataType(constructors: Vector[Vector[ScottField]])

  /** A field of a constructor: a value of the type itself, or of another
    * type.
    */
  enum ScottField:
    case Recursive
    case Element(dataType: ScottDataType)

  /** A value of a Scott data type: the constructor's position and the
    * fields' values.
    */
  final case class ScottTree(constructor: Int, fields: Vector[ScottTree])

  /** The booleans, true = λt. λf. t. */
  val scottBooleans: ScottDataType = ScottDataType(Vector(Vector.empty, Vector.empty))

  /** The unary naturals, zero = λz. λs. z, successor p = λz. λs. s p. */
  val scottUnary: ScottDataType = ScottDataType(Vector(Vector.empty, Vector(ScottField.Recursive)))

  /** The binary naturals: zero, even h, odd h. */
  val scottBinary: ScottDataType =
    ScottDataType(Vector(Vector.empty, Vector(ScottField.Recursive), Vector(ScottField.Recursive)))

  /** The lists of the element type: nil, cons head tail. */
  def scottList(element: ScottDataType): ScottDataType =
    ScottDataType(Vector(Vector.empty, Vector(ScottField.Element(element), ScottField.Recursive)))

  /** Values of the data type, of at most a fifth of Hedgehog's size in
    * constructors along any path: the named cases are each constructor
    * with no recursion (true, false, zero, nil) and chains such as
    * successor (successor zero) and a list of two booleans.
    */
  def scottTree(dataType: ScottDataType): Gen[ScottTree] =
    Gen.sized(size => scottTreeOfDepth(dataType, size.value / 5))

  private def scottTreeOfDepth(dataType: ScottDataType, depth: Int): Gen[ScottTree] =
    val positions = dataType.constructors.indices.toList
    val allowed =
      if depth <= 0 then positions.filter(position => dataType.constructors(position).forall(_ != ScottField.Recursive))
      else positions
    for
      constructor <- Gen.element(allowed.head, allowed.tail)
      fields <- dataType.constructors(constructor).foldLeft(Gen.constant(Vector.empty[ScottTree])) {
        (gathered, field) =>
          val fieldType = field match
            case ScottField.Recursive            => dataType
            case ScottField.Element(elementType) => elementType
          for done <- gathered; next <- scottTreeOfDepth(fieldType, depth - 1) yield done :+ next
      }
    yield ScottTree(constructor, fields)

  /** The Scott encoding of the value: `λc1. ... λcn. ci f1 ... fk`, each fi
    * the encoding of a field.
    */
  def scottTerm(dataType: ScottDataType, tree: ScottTree): Term =
    val fieldTypes = dataType.constructors(tree.constructor).map {
      case ScottField.Recursive            => dataType
      case ScottField.Element(elementType) => elementType
    }
    val fields = fieldTypes.zip(tree.fields).map(scottTerm)
    def cases(bound: Vector[Term]): Term =
      if bound.size == dataType.constructors.size then
        fields.foldLeft(bound(tree.constructor))((function, field) => function(field))
      else λ(next => cases(bound :+ next))
    cases(Vector.empty)

  /** The kinds of deep term `deepTerm` builds. */
  enum DeepKind:
    case LambdaChain, ApplicationSpine, NestedChoice, ParallelChain, NestedRedex

  /** Terms as deep as `length`, built by a fold rather than a recursive
    * generator, for stack safety: a chain of abstractions λx1. ... λxn. x1,
    * and, under one abstraction λa whose variable is the leaf a, an
    * application spine `a a ... a`, choices nested to the right
    * `choice(a, choice(a, ...))`, a parallel chain nested to the left, and
    * redexes nested in their bodies `(λx. (λy. ... y) x) a`. A test that
    * checks a deep term prints no term when it fails.
    */
  def deepTerm(kind: DeepKind, length: Int): Term =
    require(length >= 1, s"a deep term has length at least 1: $length")
    kind match
      case DeepKind.LambdaChain =>
        λ(first => (1 until length).foldLeft(first)((body, _) => λ(_ => body)))
      case DeepKind.ApplicationSpine =>
        λ(leaf => (1 to length).foldLeft(leaf)((function, _) => function(leaf)))
      case DeepKind.NestedChoice =>
        λ(leaf => (1 to length).foldLeft(leaf)((inner, _) => choice(leaf, inner)))
      case DeepKind.ParallelChain =>
        λ(leaf => (1 to length).foldLeft(leaf)((left, _) => left ∥ leaf))
      case DeepKind.NestedRedex =>
        λ(leaf => (1 to length).foldLeft(λ(x => x))((inner, _) => λ(x => inner(x)))(leaf))

  /** A deep term of a drawn kind, of a length from `minimum` to `maximum`
    * growing with the size.
    */
  def deepTerm(minimum: Int, maximum: Int): Gen[(DeepKind, Int, Term)] =
    for
      kind <- Gen.element1(
        DeepKind.LambdaChain,
        DeepKind.ApplicationSpine,
        DeepKind.NestedChoice,
        DeepKind.ParallelChain,
        DeepKind.NestedRedex
      )
      length <- Gen.int(Range.linear(minimum, maximum))
    yield (kind, length, deepTerm(kind, length))
