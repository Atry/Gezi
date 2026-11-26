package gezi.proofs

import gezi.rewritetrace.Conversions
import gezi.frontend.Defunctionalization
import gezi.ir.BindingNormalForm
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

import ArticleProof.congruence
import ArticleProof.connection
import ArticleProof.symmetry
import ArticleProof.transitivity
import gezi.ir.{Apply, Thunk}

/** How a thunk node reads as an application: filled from the thunk node
  * `parent` with one hole more, the filling at `position` filling the
  * parent's first hole; or made from `parent` whose first hole is ignored,
  * which drops its argument.
  */
private enum Reading:
  case Filled(position: Int, parent: Instruction)
  case Dropped(parent: Instruction)

/** The proofs of the steps of a search: that a side's instance equals a node
  * of the forest, and that each union holds, using only the unions made
  * before it, so that every proof is finite. The port of the matching and
  * the steps of `gezi/prolog/gezi/opentheory_article.pl`, whose
  * module comment, THE DERIVATION, says what each step proves.
  *
  * The Prolog writer searched by backtracking and took the first proof
  * (`once/1`). Here an attempt is a trampoline (`TailCalls`) that gives a
  * proof or none, so that matching a pattern as deep as a program takes no
  * JVM stack per layer; a search with several answers is a lazy list of
  * attempts in the Prolog's order of answers, and the first attempt that
  * gives a proof is taken (`firstFound`), so that the article is the same.
  * An attempt is run only when the ones before it gave none: an alternative
  * the Prolog never reached is never computed, and some throw.
  */
private final class ProofMatching(store: ArticleStore, forest: ProofForest):

  private type Attempt = TailRec[Option[ArticleProof]]

  /** The proof of the first attempt that gives one, the attempts run in
    * order.
    */
  private def firstFound(attempts: LazyList[Attempt]): Attempt = attempts match
    case LazyList() => done(None)
    case attempt #:: rest =>
      attempt.flatMap {
        case found @ Some(_) => done(found)
        case None            => tailcall(firstFound(rest))
      }

  /** The proof that the pattern, its metavariable i the element i of the
    * leaves, equals the target, using only the unions below `time`, or none.
    */
  def matchedProof(pattern: MatchPattern, leaves: Vector[Option[Instruction]], target: Instruction, time: Int): Option[ArticleProof] =
    tailcall(matched(pattern, leaves, target, time)).result

  /** The attempt to prove that the pattern equals the target: a
    * metavariable whose leaf is in the target's class is the leaf; an instruction
    * is the target, or a node of its class, or else read as its layer; a
    * lambda pattern whose leaf is in the target's class is the leaf by the
    * defunctionalized η rule of its thunk constant (a search binds the
    * metavariable to the class of a closure the pattern stands at), and is
    * otherwise matched as a thunk layer.
    */
  private def matched(pattern: MatchPattern, leaves: Vector[Option[Instruction]], target: Instruction, time: Int): Attempt =
    pattern match
      case MatchPattern.Metavariable(index) =>
        val bound = ArticleStore.leafBound(leaves, index)
        done(Option.when(forest.connectedBefore(bound, target, time))(connection(bound, target)))
      case MatchPattern.Reference(instruction) =>
        if instruction == target then done(Some(ArticleProof.Reflexivity(ArticleTerm.Stored(instruction))))
        else if forest.isNode(instruction) && forest.connectedBefore(instruction, target, time) then
          done(Some(connection(instruction, target)))
        else tailcall(layerMatched(store.storedPattern(instruction), leaves, target, time))
      case MatchPattern.Lambda(index, thunk) =>
        val bound = ArticleStore.leafBound(leaves, index)
        if forest.connectedBefore(bound, target, time) then
          val LayerShape.Thunk(code, holes) = LayerShape.of(thunk): @unchecked
          done(
            Some(
              transitivity(
                ArticleProof.Instance(Axiom.Eta(code, holes), Vector("filling0" -> ArticleTerm.Stored(bound))),
                connection(bound, target)
              )
            )
          )
        else tailcall(layerMatched(thunk, leaves, target, time))
      case MatchPattern.Layered(layer) => tailcall(layerMatched(layer, leaves, target, time))

  /** A pattern that is one layer, matched by the first node of the target's
    * class whose layer reads as it, followed by the path to the target. A
    * target that is no node of the proof, a term inside a define that a
    * search kept as a leaf, has no class, and nothing matches it but itself.
    */
  private def layerMatched(
      layer: Layer[MatchPattern],
      leaves: Vector[Option[Instruction]],
      target: Instruction,
      time: Int
  ): Attempt =
    if !forest.isNode(target) then done(None)
    else
      val shape = LayerShape.of(layer)
      firstFound(
        LazyList
          .from(forest.candidatesBefore(target, time))
          .map(candidate =>
            tailcall(firstFound(candidateProofs(shape, layer.children, leaves, candidate, time)))
              .map(_.map(proof => transitivity(proof, connection(candidate, target))))
          )
      )

  /** The attempts to prove that the layer of the shape over the patterns
    * equals the candidate: the candidate's layer is of the same shape, each
    * child matching; or the layer is a thunk with holes that is not its own
    * spelling and the candidate's layer is of the shape of its spelling, the
    * respelling instance joining the two and the spelling's fillings, over
    * the patterns, matching the candidate's (a lemma's side stated in
    * another spelling than the graph's node it was matched at); or the
    * layer is an application and the candidate's layer is a thunk that a
    * filling of a hole made, the defunctionalized β rule instance of
    * that filling joining the two, the filled thunk the candidate's layer
    * itself or the thunk the candidate's layer is the respelling of
    * (`unspelledLayers`), the respelling instance joining it to the
    * candidate.
    */
  private def candidateProofs(
      shape: LayerShape,
      children: Vector[MatchPattern],
      leaves: Vector[Option[Instruction]],
      candidate: Instruction,
      time: Int
  ): LazyList[Attempt] =
    val candidateLayer = store.layer(candidate)
    val sameShape: Attempt =
      if LayerShape.of(candidateLayer) == shape && candidateLayer.children.size == children.size then
        tailcall(childrenMatched(children.zip(candidateLayer.children).toList, leaves, time, Vector.empty))
          .map(_.map(congruence(shape, _)))
      else done(None)
    sameShape #:: ((shape, children, candidateLayer) match
      case (LayerShape.Thunk(code, holes), _, Thunk(candidateCode, candidateHoles, candidateFillings))
          if holes.nonEmpty && (candidateCode, candidateHoles) != (code, holes) &&
            children.size == store.thunkArity(code, holes) =>
        LazyList.from(store.respelled(code, holes)).collect {
          case (spelledCode, spelledHoles, spelledFillings)
              if (spelledCode, spelledHoles) == (candidateCode, candidateHoles) &&
                spelledFillings.size == candidateFillings.size =>
            val spelledChildren =
              spelledFillings.map(BindingNormalForm.placeholdersMapped(_, children)(MatchPattern.Layered(_)))
            val substitution = children.zipWithIndex.map((child, position) =>
              (s"filling$position", store.patternTerm(child, leaves.map(_.map(ArticleTerm.Stored(_)))))
            )
            tailcall(childrenMatched(spelledChildren.zip(candidateFillings).toList, leaves, time, Vector.empty)).map(
              _.map(proofs =>
                transitivity(
                  ArticleProof.Instance(Axiom.Respell(code, holes), substitution),
                  congruence(LayerShape.Thunk(spelledCode, spelledHoles), proofs)
                )
              )
            )
        }
      case (LayerShape.Apply, Vector(functionPattern, argumentPattern), Thunk(code, holes, fillings)) =>
        filledReadings(code, holes, fillings, time).map(reading =>
          tailcall(readingProof(reading, code, holes, fillings, functionPattern, argumentPattern, leaves, time))
        ) #::: unspelledLayers(code, holes, fillings).flatMap((sourceCode, sourceHoles, sourceFillings) =>
          filledReadings(sourceCode, sourceHoles, sourceFillings, time).map(reading =>
            tailcall(
              readingProof(reading, sourceCode, sourceHoles, sourceFillings, functionPattern, argumentPattern, leaves, time)
            ).map(_.map(transitivity(_, respellInstance(sourceCode, sourceHoles, sourceFillings))))
          )
        )
      case _ => LazyList.empty
    )

  /** The respelling instance (`Axiom.Respell`) of the thunk of the code and
    * holes over the fillings.
    */
  private def respellInstance(code: Code, holes: Vector[Hole], fillings: Vector[Instruction]): ArticleProof =
    ArticleProof.Instance(
      Axiom.Respell(code, holes),
      fillings.zipWithIndex.map((filling, position) => (s"filling$position", ArticleTerm.Stored(filling)))
    )

  /** Each thunk layer the defunctionalized β rule makes of a thunk node of
    * the forest, its first hole filled or dropped, that is not its own
    * spelling, by the code and holes of its spelling: the layer's code and
    * holes and the spelling's fillings over the placeholders. In the order
    * the nodes were made. Computed once, when a reading first asks.
    */
  private lazy val respelledFrom: Map[(Code, Vector[Hole]), Vector[(Code, Vector[Hole], Vector[Instruction])]] =
    forest.nodes
      .filterNot(_.opaque)
      .flatMap(node =>
        store.layer(node) match
          case Thunk(code, _ +: holes, _) if holes.nonEmpty => Some((code, holes))
          case _                                            => None
      )
      .distinct
      .flatMap((code, holes) =>
        store.respelled(code, holes).map((spelledCode, spelledHoles, spelledFillings) =>
          ((spelledCode, spelledHoles), (code, holes, spelledFillings))
        )
      )
      .groupMap(_._1)(_._2)

  /** The thunk layers the thunk node's layer of the code, holes and fillings
    * is the respelling of (`respelledFrom`): each with the fillings the
    * node's fillings hold at the placeholders of its spelling, when every
    * placeholder is held, one node at all its places.
    */
  private def unspelledLayers(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Instruction]
  ): LazyList[(Code, Vector[Hole], Vector[Instruction])] =
    LazyList.from(respelledFrom.getOrElse((code, holes), Vector.empty)).flatMap {
      (sourceCode, sourceHoles, spelledFillings) =>
        val arity = store.thunkArity(sourceCode, sourceHoles)
        val placeholders = BindingNormalForm.placeholders(arity).zipWithIndex.toMap
        val held =
          if spelledFillings.size != fillings.size then None
          else
            spelledFillings.zip(fillings).foldLeft(Option(Map.empty[Int, Instruction])) {
              case (found, (spelled, node)) => found.flatMap(placeholdersHeld(spelled, node, placeholders, _))
            }
        held.filter(_.size == arity).map(found => (sourceCode, sourceHoles, Vector.tabulate(arity)(found)))
    }

  /** The nodes the node holds at the placeholders of the respelled filling,
    * added to those found, when the node's layers are the filling's down to
    * its placeholders and a placeholder found before is the same node. A
    * respelled filling's leaves are its placeholders
    * (`BindingNormalForm.placeholdersFolded`), so `layered` is read of
    * layers only.
    */
  private def placeholdersHeld(
      spelled: Instruction,
      node: Instruction,
      placeholders: Map[Instruction, Int],
      found: Map[Int, Instruction]
  ): Option[Map[Int, Instruction]] =
    placeholders.get(spelled) match
      case Some(position) =>
        found.get(position) match
          case Some(earlier) => Option.when(earlier == node)(found)
          case None          => Some(found.updated(position, node))
      case None =>
        if node.opaque then None
        else
          val spelledLayer = spelled.layered
          val nodeLayer = store.layer(node)
          if LayerShape.of(spelledLayer) != LayerShape.of(nodeLayer) || spelledLayer.children.size != nodeLayer.children.size
          then None
          else
            spelledLayer.children.zip(nodeLayer.children).foldLeft(Option(found)) { case (held, (spelledChild, nodeChild)) =>
              held.flatMap(placeholdersHeld(spelledChild, nodeChild, placeholders, _))
            }

  /** Each pattern matched against its node, in order, each the first proof
    * it has; none when one has none.
    */
  private def childrenMatched(
      pairs: List[(MatchPattern, Instruction)],
      leaves: Vector[Option[Instruction]],
      time: Int,
      proofs: Vector[ArticleProof]
  ): TailRec[Option[Vector[ArticleProof]]] = pairs match
    case Nil => done(Some(proofs))
    case (pattern, node) :: rest =>
      tailcall(matched(pattern, leaves, node, time)).flatMap {
        case Some(proof) => tailcall(childrenMatched(rest, leaves, time, proofs :+ proof))
        case None        => done(None)
      }

  /** The readings of a thunk node as an application, before `time`: each
    * filling, in slot order, as the filling of the first hole of a thunk
    * node of one hole more whose other fillings are in the classes of the
    * others; then a thunk node whose first hole is ignored and whose
    * fillings are in the classes of these. Stack-safe: the positions whose
    * filling has no such thunk node are skipped by a loop, not by one frame
    * of `LazyList.flatMap` each, which threw `StackOverflowError` on a thunk
    * of 2,468 fillings none of which had one (the entry `solo`'s
    * repeated_library_hotspots_calls_1000 direct point, seed 20261116,
    * 2026-11-17).
    */
  private def filledReadings(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Instruction],
      time: Int
  ): LazyList[Reading] =
    val slots = filledSlots(holes, fillings.size)
    def parentsAt(position: Int): LazyList[Instruction] =
      thunkParents(code, Hole.Bound(slots(position)) +: holes, fillings.patch(position, Vector.empty, 1), time)
    @scala.annotation.tailrec
    def nextFilled(position: Int): Option[(Int, LazyList[Instruction])] =
      if position == slots.size then None
      else
        val parents = parentsAt(position)
        if parents.isEmpty then nextFilled(position + 1) else Some((position, parents))
    def readingsFrom(position: Int): LazyList[Reading] = nextFilled(position) match
      case Some((found, parents)) => parents.map(Reading.Filled(found, _)) #::: readingsFrom(found + 1)
      case None                   => thunkParents(code, Hole.Ignored +: holes, fillings, time).map(Reading.Dropped(_))
    readingsFrom(0)

  /** The slots that are no hole, in increasing order, as many as the
    * fillings.
    */
  private def filledSlots(holes: Vector[Hole], fillingCount: Int): Vector[Int] =
    val holeSlots = holes.collect { case Hole.Bound(slot) => slot }
    (0 until holeSlots.size + fillingCount).filterNot(holeSlots.contains).toVector

  private def thunkParents(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Instruction],
      time: Int
  ): LazyList[Instruction] =
    LazyList.from(forest.thunks.getOrElse((code, holes), Vector.empty)).filter(parent =>
      store.layer(parent) match
        case Thunk(_, _, parentFillings) =>
          parentFillings.size == fillings.size &&
          parentFillings.zip(fillings).forall((parentFilling, filling) =>
            forest.connectedBefore(parentFilling, filling, time)
          )
        case _ => false
    )

  /** The application of the two patterns equals the parent applied to the
    * filling (congruence), which equals the thunk filled from the parent's
    * fillings (the defunctionalized β rule instance), which equals the
    * candidate's layer (congruence over the fillings, one class each).
    */
  private def readingProof(
      reading: Reading,
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[Instruction],
      functionPattern: MatchPattern,
      argumentPattern: MatchPattern,
      leaves: Vector[Option[Instruction]],
      time: Int
  ): Attempt = reading match
    case Reading.Filled(position, parent) =>
      val argument = fillings(position)
      tailcall(matched(functionPattern, leaves, parent, time)).flatMap {
        case None => done(None)
        case Some(functionProof) =>
          tailcall(matched(argumentPattern, leaves, argument, time)).map(_.flatMap { argumentProof =>
            val (parentHoles, parentFillings) = thunkParts(parent)
            val filled = parentFillings.patch(position, Vector(argument), 0)
            Option.when(filled.size == fillings.size) {
              val substitution =
                fillSubstitution(parentFillings.map(ArticleTerm.Stored(_)), ArticleTerm.Stored(argument))
              val applied = congruence(LayerShape.Apply, Vector(functionProof, argumentProof))
              val spelled = congruence(LayerShape.Thunk(code, holes), filled.zip(fillings).map(connection))
              transitivity(
                applied,
                transitivity(ArticleProof.Instance(Axiom.Fill(code, parentHoles), substitution), spelled)
              )
            }
          })
      }
    case Reading.Dropped(parent) =>
      tailcall(matched(functionPattern, leaves, parent, time)).map(_.flatMap { functionProof =>
        val argumentTerm = store.patternTerm(argumentPattern, leaves.map(_.map(ArticleTerm.Stored(_))))
        val (parentHoles, parentFillings) = thunkParts(parent)
        Option.when(parentFillings.size == fillings.size) {
          val substitution = fillSubstitution(parentFillings.map(ArticleTerm.Stored(_)), argumentTerm)
          val applied = congruence(LayerShape.Apply, Vector(functionProof, ArticleProof.Reflexivity(argumentTerm)))
          val spelled = congruence(LayerShape.Thunk(code, holes), parentFillings.zip(fillings).map(connection))
          transitivity(
            applied,
            transitivity(ArticleProof.Instance(Axiom.Fill(code, parentHoles), substitution), spelled)
          )
        }
      })

  private def thunkParts(node: Instruction): (Vector[Hole], Vector[Instruction]) = store.layer(node) match
    case Thunk(_, holes, fillings) => (holes, fillings)
    case other => throw IllegalStateException(s"the thunk node $node has the layer $other")

  /** The variables of a defunctionalized β rule equation bound to a parent's
    * fillings and the argument.
    */
  private def fillSubstitution(fillings: Vector[ArticleTerm], argument: ArticleTerm): Vector[(String, ArticleTerm)] =
    fillings.zipWithIndex.map((filling, position) => (s"filling$position", filling)) :+ ("argument" -> argument)

  /** The proof of the union numbered `number`: the encoding of its first
    * node equal to its second's.
    */
  def edgeProof(number: Int): ArticleProof =
    val union = forest.union(number)
    val first = union.first
    val second = union.second
    union.justification match
      case Justification.Congruence =>
        firstFound(congruenceProofs(number, first, second)).result.getOrElse(
          throw OpentheoryArticleError(ArticleErrorReason.CongruenceNotProved(number, first, second))
        )
      case Justification.Lemma(lemma, bindings) =>
        val (arity, leftPattern, rightPattern) = store.lemmaPatterns(lemma)
        if bindings.size != arity then
          throw OpentheoryArticleError(ArticleErrorReason.BindingsDiffer(number, lemma, bindings.size, arity))
        val leftProof = instanceSideProof(number, leftPattern, bindings, first)
        val rightProof = instanceSideProof(number, rightPattern, bindings, second)
        val axiom = Axiom.Lemma(lemma)
        val substitution = (leftPattern.mentions ++ rightPattern.mentions).distinct.sorted
          .map(index => (s"metavariable$index", ArticleTerm.Stored(ArticleStore.leafBound(bindings, index))))
        transitivity(
          symmetry(leftProof),
          transitivity(ArticleProof.Instance(axiom, substitution), rightProof)
        )
      case Justification.LemmaWithoutBindings(lemma) =>
        throw OpentheoryArticleError(ArticleErrorReason.LemmaBindingNotRecorded(number, lemma))
      case Justification.Beta =>
        firstFound(betaProofs(number, first, second)).result.getOrElse(
          throw OpentheoryArticleError(ArticleErrorReason.BetaNotProved(number, first, second))
        )
      case Justification.BetaConversion(reduct) => ArticleProof.Conversion(first, second, reduct)
      // The spelling the thunk was written back from is the thunk opened at
      // the eigenvariables (it is the front end's abstraction of it,
      // `HigherOrderMatching.abstraction`); the recorded spelling node is the
      // node of the body's class its layer names, whose term may be another
      // spelling of it, so the spelling is matched against the body's class.
      case Justification.Abstraction(eigenvariables, body, _) =>
        val spelling = Conversions.opened(second, eigenvariables)
        val proof = matchedProof(MatchPattern.Reference(spelling), Vector.empty, body, number).getOrElse(
          throw OpentheoryArticleError(ArticleErrorReason.SideNotMatched(body))
        )
        ArticleProof.Abstraction(first, second, eigenvariables, body, ArticleProof.symmetry(proof))
      case other @ Justification.Valuation(_) =>
        throw OpentheoryArticleError(ArticleErrorReason.NotAJustification(number, other))

  private def instanceSideProof(
      number: Int,
      pattern: MatchPattern,
      bindings: Vector[Option[Instruction]],
      node: Instruction
  ): ArticleProof =
    matchedProof(pattern, bindings, node, number).getOrElse(
      throw OpentheoryArticleError(ArticleErrorReason.InstanceNotMatched(number, pattern, node))
    )

  /** The attempts at a union justified `beta`: an application united with
    * the body of the closure its function's class holds once the
    * application fills the closure's last hole. The function is read as the
    * closure, the application fills the last hole by the defunctionalized β
    * rule instance of that thunk constant, the constant with no hole left
    * equals its code's body over its fillings (the body equation of the
    * import set), and that body, the code read as a pattern whose
    * metavariable i is the filling of slot i, is matched against the body
    * node.
    */
  private def betaProofs(time: Int, application: Instruction, body: Instruction): LazyList[Attempt] =
    store.layer(application) match
      case Apply(function, argument) =>
        closureReads(time, Nil, function, 1).map { (code, holes, fillings, functionProof) =>
          val hole = holes match
            case Vector(only) => only
            case _            => throw IllegalStateException(s"a closure of one hole read with $holes")
          val filled = holeFilled(hole, Vector.empty, fillings, argument)
          val applied =
            congruence(LayerShape.Apply, Vector(functionProof, ArticleProof.Reflexivity(ArticleTerm.Stored(argument))))
          val closed = transitivity(
            applied,
            ArticleProof.Instance(
              Axiom.Fill(code, Vector(hole)),
              fillSubstitution(fillings.map(ArticleTerm.Stored(_)), ArticleTerm.Stored(argument))
            )
          )
          val bodySubstitution =
            filled.zipWithIndex.map((filling, position) => (s"filling$position", ArticleTerm.Stored(filling)))
          val unfolded = transitivity(closed, ArticleProof.Instance(Axiom.Body(code), bodySubstitution))
          tailcall(matched(store.codeBodyPattern(code), filled.map(Some(_)), body, time))
            .map(_.map(transitivity(unfolded, _)))
        } #::: residualProofs(time, function, argument, body)
      case _ => LazyList.empty

  /** The attempts at a union justified `beta` whose second node is the
    * residual of an application that leaves a hole (`Saturation`'s residual
    * thunk): the function read as a closure of one hole more than the
    * residual has, the application filling its first hole by the
    * defunctionalized β rule instance, and the thunk that leaves matched
    * against the residual node, in the e-graph's spelling through the
    * respelling instance where the node is that thunk's respelling
    * (`candidateProofs`).
    */
  private def residualProofs(time: Int, function: Instruction, argument: Instruction, body: Instruction): LazyList[Attempt] =
    if body.opaque then LazyList.empty
    else
      store.layer(body) match
        case Thunk(_, residualHoles, _) if residualHoles.nonEmpty =>
          closureReads(time, Nil, function, residualHoles.size + 1).map { (code, holes, fillings, functionProof) =>
            val (hole, rest) = holes match
              case first +: others => (first, others)
              case _               => throw IllegalStateException(s"a closure of ${residualHoles.size + 1} holes read with $holes")
            val filled = holeFilled(hole, rest, fillings, argument)
            val applied =
              congruence(LayerShape.Apply, Vector(functionProof, ArticleProof.Reflexivity(ArticleTerm.Stored(argument))))
            val left = transitivity(
              applied,
              ArticleProof.Instance(
                Axiom.Fill(code, holes),
                fillSubstitution(fillings.map(ArticleTerm.Stored(_)), ArticleTerm.Stored(argument))
              )
            )
            tailcall(matched(MatchPattern.Layered(Thunk(code, rest, filled.map(MatchPattern.Reference(_)))), Vector.empty, body, time))
              .map(_.map(transitivity(left, _)))
          }
        case _ => LazyList.empty

  /** The readings of the node, before `time`, as the thunk constant of a
    * code with `holeCount` holes applied to fillings: a thunk node of the
    * node's class with that many holes, or an application in it whose
    * function reads so with one hole more, the application filling that
    * hole. `visited` holds the candidates read on the way down, so that a
    * class reached again through its own applications ends the descent. The
    * descent recurses once per application of a spine.
    */
  private def closureReads(
      time: Int,
      visited: List[Instruction],
      node: Instruction,
      holeCount: Int
  ): LazyList[(Code, Vector[Hole], Vector[Instruction], ArticleProof)] =
    LazyList.from(forest.candidatesBefore(node, time)).filterNot(visited.contains).flatMap { candidate =>
      val reads: LazyList[(Code, Vector[Hole], Vector[Instruction], ArticleProof)] =
        store.layer(candidate) match
          case Thunk(code, holes, fillings) if holes.nonEmpty && holes.size == holeCount =>
            LazyList((code, holes, fillings, ArticleProof.Reflexivity(ArticleTerm.Stored(candidate))))
          case Apply(function, argument) =>
            closureReads(time, candidate :: visited, function, holeCount + 1).map {
              (code, functionHoles, fillings, functionProof) =>
                val (hole, holes) = functionHoles match
                  case first +: rest => (first, rest)
                  case _             => throw IllegalStateException("a closure read with no hole")
                val filled = holeFilled(hole, holes, fillings, argument)
                val applied =
                  congruence(LayerShape.Apply, Vector(functionProof, ArticleProof.Reflexivity(ArticleTerm.Stored(argument))))
                val proof = transitivity(
                  applied,
                  ArticleProof.Instance(
                    Axiom.Fill(code, functionHoles),
                    fillSubstitution(fillings.map(ArticleTerm.Stored(_)), ArticleTerm.Stored(argument))
                  )
                )
                (code, holes, filled, proof)
            }
          case _ => LazyList.empty
      reads.map((code, holes, fillings, proof) => (code, holes, fillings, transitivity(connection(node, candidate), proof)))
    }

  /** The fillings of the thunk constant that the defunctionalized β rule
    * gives when the argument fills the hole, the holes left after it: the
    * argument at the place of the hole's slot, or dropped by an ignored
    * hole.
    */
  private def holeFilled(hole: Hole, holes: Vector[Hole], fillings: Vector[Instruction], argument: Instruction): Vector[Instruction] =
    hole match
      case Hole.Ignored => fillings
      case Hole.Bound(slot) =>
        fillings.patch(Defunctionalization.fillingPosition(holes, slot), Vector(argument), 0)

  /** The attempts at a congruence union. Either the two nodes are one layer
    * over classes united before it, the first node's layer matched against
    * the second (an application read as the filled thunk the e-graph spells
    * it as); or they are two spellings of one application through two
    * thunks of one class: one of the two nodes reads as the application of a
    * node to a node, and that application is matched against each of the
    * two, the first proof for the second node taken for each proof for the
    * first, in order.
    */
  private def congruenceProofs(time: Int, user: Instruction, twin: Instruction): LazyList[Attempt] =
    val userLayer = store.layer(user)
    candidateProofs(LayerShape.of(userLayer), userLayer.children.map(MatchPattern.Reference(_)), Vector.empty, twin, time) #:::
      (nodeApplications(user, time) #::: nodeApplications(twin, time)).flatMap { (function, argument) =>
        val children = Vector(MatchPattern.Reference(function), MatchPattern.Reference(argument))
        candidateProofs(LayerShape.Apply, children, Vector.empty, user, time).map(userAttempt =>
          userAttempt.flatMap {
            case None => done(None)
            case Some(userProof) =>
              tailcall(firstFound(candidateProofs(LayerShape.Apply, children, Vector.empty, twin, time)))
                .map(_.map(twinProof => transitivity(symmetry(userProof), twinProof)))
          }
        )
      }

  /** The readings of the node's layer, before `time`, as the application of
    * a node to a node: its own `apply` layer, or a thunk filled from a
    * parent, the filling being the argument; a thunk that a parent whose
    * first hole is ignored makes reads as that parent applied to any term,
    * here the parent itself; and so a thunk the node's layer is the
    * respelling of (`unspelledLayers`).
    */
  private def nodeApplications(node: Instruction, time: Int): LazyList[(Instruction, Instruction)] =
    def applications(code: Code, holes: Vector[Hole], fillings: Vector[Instruction]): LazyList[(Instruction, Instruction)] =
      filledReadings(code, holes, fillings, time).map {
        case Reading.Filled(position, parent) => (parent, fillings(position))
        case Reading.Dropped(parent)          => (parent, parent)
      }
    store.layer(node) match
      case Apply(function, argument) => LazyList((function, argument))
      case Thunk(code, holes, fillings) =>
        applications(code, holes, fillings) #::: unspelledLayers(code, holes, fillings).flatMap(applications)
      case _ => LazyList.empty
