package com.yang_bo.gezi.knowledgereading

import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Literal
import com.yang_bo.gezi.frontend.Literals
import com.yang_bo.gezi.frontend.Respelling
import com.yang_bo.gezi.ir.ChoiceSpine
import com.yang_bo.gezi.weakhead.Computation
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Head
import com.yang_bo.gezi.weakhead.KnownExtremes
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NeutralValue
import com.yang_bo.gezi.weakhead.NeutralVariable
import com.yang_bo.gezi.weakhead.ParallelSet
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.weakhead.TableRetention
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.weakhead.Values
import com.yang_bo.gezi.weakhead.WeakHead
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** A fresh neutral variable the reader applies knowledge data to: the handler
  * of one alternative of a Scott constructor (a tuple being the one alternative
  * of its arity).
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the
  * term"), kept as an exception argued here: it stands for a binder of the
  * value read (a Scott value's handler, a constructor's or a define's
  * parameter), opened to read the value's head, as the normal-form reader's
  * `BoundVariable` opens a lambda, whose Scaladoc has the argument. A closed
  * term in its place would not do: a term that is no such value could ignore it
  * and build the reading itself.
  */
enum KnowledgeVariable extends NeutralVariable:
  case Alternative(position: Int)

/** Knowledge data the reader cannot read: a head of another shape than the
  * encoding's, or a reading the budget stopped.
  */
final case class KnowledgeReadingError(reason: String)
    extends RuntimeException(reason)

/** A reading of knowledge data on the weak-head evaluator. */
type Reading[C <: NativeSpecializer & Singleton, Result] =
  Computation[ReadingState[C], Result]

/** The reader of data written in lambdalattice: the generic part, which knows
  * the encodings and no knowledge. It takes a field off a record of partial
  * functions of literals by its key, opens a Scott constructor with fresh
  * neutral variables, and decodes the sugar of lists, strings and integers,
  * always under `Mode.TablingWeakHead`, since a configuration file is read
  * tabled, which unfolds no library term and reads no index, so that reading
  * knowledge depends on no knowledge. The tables are those of the reading's
  * state: a look-up repeated within one `run` is answered from its table. A
  * field is opened, never evaluated: the arguments of a neutral head keep the
  * author's spelling. What each key means is the caller's.
  *
  * A RECORD is a choice of curried partial functions of literals,
  * `(λ"k1". M1) + (λ"k2". M2)`; its field of a key is the record applied to the
  * elements the key's literal spreads into, which by equation (8) is the choice
  * of each member applied to them: the value of the member of that key, and top
  * for every other member. The record stays in the function position while the
  * elements come one by one, so the tables of the record applied to a prefix
  * are shared by every key with that prefix. Records chosen together are one
  * record, so a field several of them write is the choice of what they write.
  *
  * THE MISS OF A KEY. The evaluator runs as its variant that knows top
  * (`com.yang_bo.gezi.weakhead.KnownExtremes`, `knownExtremes`): the top a member of
  * another key gives is a greatest term, which has no parallel set, so a miss
  * leaves nothing behind, and nothing of it is applied to the handlers or to a
  * later key (top + M = M, top M = top, top ∥ M = top).
  *
  * THE DATA HEADS of a value applied to its handlers are the neutral heads,
  * each the one head of its parallel set. Any other parallel set is an error of
  * the data: the reader has no rule of its own for one, since there is only the
  * one ordinary tabled weak-head interpreter.
  */
object KnowledgeReading:

  /** The terms the evaluator knows while it reads knowledge: top alone, which
    * every partial function of a literal has as its miss, and no least term
    * (`KnownExtremes.onlyTop`, the extremes every reading of the contest
    * knows).
    */
  val knownExtremes: KnownExtremes = KnownExtremes.onlyTop

  /** The tables a single read of knowledge from a fresh state may hold: a
    * round's lemmas (`StandardLibrary.lemmas` from `startingState`, as the
    * strategies' and the JIT's tests read them), an entry's or a problem's
    * data, a library file's members.
    *
    * MEASURED 2026-11-16 by a scratch munit probe in jit, not committed: a
    * round's lemmas read from this state with the table limit lifted, the
    * library the native route's
    * (`tests/library_fixtures/presets.lambdalattice`), with the knowledge's
    * texts decoded by the library's `text/cbor` (on cbor-literals, 5c6c2f83b)
    * and read by the host as tries (`trieText`, knowledge-literal-text,
    * f0c79a478):
    *
    * {{{
    * round                       lemmas   tables (decoded)   tables (tries)   steps (decoded)   steps (tries)
    * closure_application              1              3,573              979             8,015           2,496
    * prolog_backend_type_check       71             74,377           18,552           238,659          98,011
    * occurrence_erasure               2              4,898            1,264            11,796           3,853
    * }}}
    *
    * THE LIMIT: set to 100,000 when a round's lemmas read 74,377 tables with
    * the decoded texts, and not lowered with the tries' 18,552: the reads of a
    * problem's data that start from this state still decode their texts by the
    * library and were not measured again. A read of knowledge from a fresh
    * state that needs more is a finding, and the limit is set again from a
    * measurement.
    *
    * TODO: once no problem data decodes its texts by the library, measure the
    * single reads from this state again and lower the limit from that
    * measurement.
    */
  val startingTableLimit: Int = 100000

  /** The state a compilation's first read starts from: no table, no expansion,
    * the evaluator knowing `knownExtremes`. Each read takes the state the
    * previous one returned (`run` of three arguments), so that the reads over
    * one tree list each directory once and share the expansions and the
    * complete tables: a read does not start from a fresh state.
    *
    * The reads after the entry's term expand no URI node (113 expansions after
    * the entry's term and after the compilation's last read, measured
    * 2026-11-12): its read-back term holds no directory, so sharing saves only
    * the tables of terms the reads have in common. A compilation starts from
    * `compilationState`, whose table limit covers the sum of its reads' tables
    * (measured at `compilationTableLimit`); this state keeps the limit of a
    * single read of knowledge, `startingTableLimit`, defined above it since an
    * object's values are initialized in order.
    */
  val startingState: ReadingState[NoFacts.type] = ReadingState
    .knowing(0, knownExtremes, com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts)
    .copy(tableLimit = startingTableLimit)

  /** The tables one compilation's reads may hold together. A single read's
    * limit (`startingTableLimit`) is the space of one read's tables; a
    * compilation threads one state through the entry's term, the entry's data,
    * the knowledge and each round's lemmas and leaves, so its tables are the
    * sum of what those reads add, each read keeping the complete tables of the
    * reads before it (the tables the reads share are counted once).
    *
    * The reads after the projection of the root to the visible subtree: an
    * entry's read takes that projection first and adds its tables to the
    * state's limit (`com.yang_bo.gezi.standardlibrary.StandardLibrary.projected`,
    * 788b762e5), so that this limit counts only what follows it, the
    * projection's cost growing with the bytes of the subtree's absolute path.
    *
    * MEASURED 2026-11-23 on eee2e6de1 by one scratch munit probe in
    * contest-entries-plover, not committed: `EntryData.at` of each in-tree
    * entry and of the fixture
    * `tests/plover_fixtures/ordered_compositions_entry` (`compositions` below)
    * under `Defaults.entryDataState` with a table limit far above any entry's,
    * then `StandardLibrary.compiled` and each round's `lemmas` and `leaves`,
    * threaded as `GenericEntryProvider.initializedWithLibrary` threads them;
    * the complete tables after each read net of the projection's (3,050), in a
    * checkout 7 levels deep (`Path.getNameCount`) whose gezi directory has 78
    * members (76 tracked directories, `target` and one directory left from a
    * deleted module):
    *
    * {{{
    * after                          fixture   plover    solo     wren     compositions
    * the data                       37,461    68,040    46,383   45,020   67,450
    * the knowledge                  62,990    136,674   79,922   78,236   136,471
    * the rounds' lemmas and leaves  63,034    136,773   79,952   78,270   136,576
    * }}}
    *
    * The rounds read: fixture 3, plover 3, solo 2, wren 4, compositions 5. At
    * a9945efcb the last row read 60,041, 133,806, 76,991, 75,309 and 133,609:
    * every compilation grew by 2,961 to 2,993 tables between the two commits,
    * which split `hindley_milner_unions` into four files and added six files to
    * `corpora/compiler`. Six empty files of the same names added at a9945efcb
    * account for 218 to 282 of those tables.
    *
    * The data's tables grow with the options: an import's look-up passes every
    * member of the directory it reads, so n options imported from one directory
    * of n members cost tables in proportion to n squared times the bits of
    * their names, and each option added makes every other import of the
    * directory dearer.
    *
    * The mechanism: the data's tables are those of the look-ups that the entry
    * and its imports make, each key a variable arguments partial function's
    * literal taken bit by bit at each member of each directory on the path, so
    * a look-up costs tables in proportion to the bits of its keys times the
    * members it passes (the design's cost, `com.yang_bo.gezi.directorysugar.DirectoryTree`,
    * at `keys`). The knowledge's tables are mostly those of its texts, the
    * lemmas' names and proof citations and the names of natives and
    * representations: read as a trie, a text of n bytes takes 8 tables (one a
    * bit) and about 24 steps a byte, where the library's `text/cbor` took about
    * 47 tables and 108 steps a byte to decode it (one string of 8 to 128 bytes:
    * 82, 146, 282, 538 and 1,050 tables as a trie; 463, 837, 1,640, 3,116 and
    * 6,063 decoded), linear in n on both. The earlier readings of 2026-11-13
    * gave the data's depth term, 107.7 tables a level, and its member term,
    * 53.8 tables a member of the gezi directory; they are not measured again.
    *
    * THE LIMIT: the compilation of `plover`, the largest, at 78 members
    * (136,773), plus the depth term up to a greatest checkout depth of 32
    * levels (25 × 107.7 = 2,693, from the 7 levels measured), plus the member
    * term up to 110 members (32 × 53.8 = 1,722), plus a tenth of that
    * compilation for the knowledge's and the options' growth (13,677), is
    * 154,865, rounded up to the next thousand: the room above the compilation
    * is 18,227 tables, of which 13,677 are for more knowledge and options.
    * CHECKOUTS DEEPER THAN 32 LEVELS, AND A gezi DIRECTORY OF MORE THAN 110
    * MEMBERS, ARE NOT COVERED: each level beyond adds about 108 tables and each
    * member about 54. An entry whose knowledge reads past the limit is a
    * finding, and the limit is set again from a measurement. Set from the
    * measurement as a small limit is (`CONTRIBUTING.md`, "Tests fail fast": a
    * limit hit by the algorithm's expected cost is raised to what was measured)
    * on 2026-11-16, and set again on 2026-11-20, 2026-11-21, 2026-11-22 and
    * 2026-11-23.
    *
    * The cost is the design's: the variable arguments partial function is the
    * trie, the tables of a key's prefixes its nodes, shared by every look-up
    * with that prefix in one reading state; a first look-up tests the key's
    * bits at each member still alive, a constant factor of about 4.4 left
    * unoptimized, since optimizing it would be premature and would add to the
    * weak head (a hash table would be the faster way), and a first look-up
    * below linear in the members is out of reach, since merging two members
    * into one node is unsound by equation (10).
    */
  val compilationTableLimit: Int = 155000

  /** The state a compilation's first read starts from: `startingState` with the
    * table limit `compilationTableLimit`, since the compilation's reads all
    * keep their complete tables in the one state they thread.
    */
  val compilationState: ReadingState[NoFacts.type] =
    startingState.copy(tableLimit = compilationTableLimit)

  /** The value of the reading within the limit of evaluator steps, read under
    * the state, and the state after it: the state's store, complete tables and
    * expansions kept, a fresh budget of the limit (`ReadingState.next` under
    * `TableRetention.KeptAll`, the retention of a compilation's reads,
    * `startingState`). Throws `KnowledgeReadingError` when the budget stops it:
    * knowledge that does not read within its budget is an error of its file.
    */
  def run[C <: NativeSpecializer & Singleton, Result](
      reading: Reading[C, Result],
      limit: Long,
      state: ReadingState[C]
  )(using C): (Result, ReadingState[C]) =
    reading.result(state.next(TableRetention.KeptAll, limit)) match
      case Computed.Done(value, after) => (value, after)
      case Computed.Stopped(after)     =>
        throw KnowledgeReadingError(
          s"the knowledge was not read within $limit steps (${after.exhausted})"
        )

  /** The value of a reading that is the only read of its terms, from
    * `startingState`: a closed term read once, outside a compilation, such as a
    * problem's file or a resource. A compilation's reads use `run` of three
    * arguments.
    */
  def run[Result](reading: Reading[NoFacts.type, Result], limit: Long): Result =
    run(reading, limit, startingState)(using NoFacts)._1

  /** The members of a set, a choice of Scott tuples: the fields of each, in the
    * order the heads are enumerated. A set that nobody writes (the field of an
    * absent key) has no member. A member is never split: a library term whose
    * body is a choice is one field of one tuple.
    */
  def members[C <: NativeSpecializer & Singleton](
      set: Value[C]
  )(using C): Reading[C, Vector[Vector[Value[C]]]] =
    dataHeads(applied(set, 1)).map(_.map {
      case (KnowledgeVariable.Alternative(0), fields) => fields
      case other                                      =>
        throw KnowledgeReadingError(s"a member of a set is no tuple: $other")
    })

  /** The alternative a Scott constructor of `count` alternatives takes, from 0,
    * and its fields, none when the value has no data head (the field of a key
    * nobody writes): the value applied to `count` fresh handlers has one data
    * head, the handler of its alternative applied to the fields. Throws
    * `KnowledgeReadingError` for a value of several data heads, a field written
    * more than once.
    */
  def alternativeWritten[C <: NativeSpecializer & Singleton](
      value: Value[C],
      count: Int
  )(using C): Reading[C, Option[(Int, Vector[Value[C]])]] =
    dataHeads(applied(value, count)).map {
      case Vector() => None
      case Vector((KnowledgeVariable.Alternative(position), fields))
          if position < count =>
        Some((position, fields))
      case other =>
        throw KnowledgeReadingError(
          s"a Scott constructor of $count alternatives reads as ${other.size} values: $other"
        )
    }

  /** The alternatives a set of Scott constructors of `count` alternatives
    * takes, a choice of them, each with its fields, in the order the heads are
    * enumerated; none for a set nobody writes (the field of an absent key, or
    * top). Throws `KnowledgeReadingError` for a head that is no alternative of
    * `count`.
    */
  def alternatives[C <: NativeSpecializer & Singleton](
      set: Value[C],
      count: Int
  )(using C): Reading[C, Vector[(Int, Vector[Value[C]])]] =
    dataHeads(applied(set, count)).map(_.map {
      case (KnowledgeVariable.Alternative(position), fields)
          if position < count =>
        (position, fields)
      case other =>
        throw KnowledgeReadingError(
          s"a member of a set of Scott constructors of $count alternatives reads as $other"
        )
    })

  /** The bodies a mixin of the fixed-width encoding writes in each of its
    * `width` slots, slot by slot, each slot's in the order the heads are
    * enumerated. Several presets contribute to options through such a mixin,
    * never through string keys (`CONTRIBUTING.md`, "The Architecture"). A
    * contribution to the slot m is `λself. λc1 … cW. cm b`, a mixin a choice of
    * contributions, and the slot m read `o o c1 … cW`: the mixin applied to
    * itself as self and to `width` fresh handlers, each data head the handler
    * of its slot applied to one body. A mixin nobody writes (top) writes no
    * slot. Throws `KnowledgeReadingError` for a head that is no handler of the
    * width applied to one body.
    */
  def slots[C <: NativeSpecializer & Singleton](mixin: Value[C], width: Int)(
      using C
  ): Reading[C, Vector[Vector[Value[C]]]] =
    coproductSlots(Value.Apply(mixin, mixin), width)

  /** The bodies a mixin of the fixed-width encoding with no self writes in each
    * of its `width` slots, slot by slot, each slot's in the order the heads are
    * enumerated: with no self, a fixed-width mixin is a multi-valued Scott
    * coproduct. A contribution to the slot m is `λc1 … cW. cm b`, the coproduct
    * a choice of contributions, and one contribution may write several slots,
    * `λc1 … cW. cm b + cn d`. top writes no slot. Throws
    * `KnowledgeReadingError` for a head that is no handler of the width applied
    * to one body.
    */
  def coproductSlots[C <: NativeSpecializer & Singleton](
      coproduct: Value[C],
      width: Int
  )(using C): Reading[C, Vector[Vector[Value[C]]]] =
    alternatives(coproduct, width).map { found =>
      val bodies = found.map {
        case (slot, Vector(body)) => (slot, body)
        case (slot, other)        =>
          throw KnowledgeReadingError(
            s"a contribution to the slot $slot of a mixin of width $width has ${other.size} bodies, not one"
          )
      }
      Vector.tabulate(width)(slot =>
        bodies.collect { case (`slot`, body) => body }
      )
    }

  /** The bodies of the slots of a coproduct (`coproductSlots`) whose slots are
    * groups, the group `g` itself a coproduct of `groupWidths(g)` slots: each
    * group's bodies, the choice of every contribution to it, read as one
    * coproduct, so that contributions to one group from several places merge by
    * the choice alone. A group nobody writes writes no slot.
    */
  def coproductGroupSlots[C <: NativeSpecializer & Singleton](
      coproduct: Value[C],
      groupWidths: Vector[Int]
  )(using C): Reading[C, Vector[Vector[Vector[Value[C]]]]] =
    coproductSlots(coproduct, groupWidths.size).flatMap(found =>
      Computation.traversed(found.zip(groupWidths))((bodies, groupWidth) =>
        bodies.reduceOption(Value.Choice(_, _)) match
          case None =>
            Computation.pure(Vector.fill(groupWidth)(Vector.empty[Value[C]]))
          case Some(contributions) => coproductSlots(contributions, groupWidth)
      )
    )

  /** The bodies of the slots of a mixin whose slot `group`, of a mixin of width
    * `width`, is itself a mixin of width `groupWidth`: the group's bodies, the
    * choice of every contribution to the slot, read as one mixin (`slots`), so
    * that the contributions of several files deep-merge by the choice alone. A
    * group nobody writes writes no slot.
    */
  def groupSlots[C <: NativeSpecializer & Singleton](
      mixin: Value[C],
      width: Int,
      group: Int,
      groupWidth: Int
  )(using C): Reading[C, Vector[Vector[Value[C]]]] =
    slots(mixin, width).flatMap(found =>
      found(group).reduceOption(Value.Choice(_, _)) match
        case None => Computation.pure(Vector.fill(groupWidth)(Vector.empty))
        case Some(contributions) => slots(contributions, groupWidth)
    )

  /** `alternativeWritten` of a value that is written. Throws
    * `KnowledgeReadingError` for one that is not.
    */
  def alternative[C <: NativeSpecializer & Singleton](
      value: Value[C],
      count: Int
  )(using C): Reading[C, (Int, Vector[Value[C]])] =
    alternativeWritten(value, count).map(
      written(_, s"a Scott constructor of $count alternatives")
    )

  /** The fields of a Scott tuple `λs. s f1 … fn` of the arity. */
  def fields[C <: NativeSpecializer & Singleton](value: Value[C], arity: Int)(
      using C
  ): Reading[C, Vector[Value[C]]] =
    alternative(value, 1).map((_, found) =>
      if found.size == arity then found
      else
        throw KnowledgeReadingError(
          s"a tuple of arity $arity has ${found.size} fields"
        )
    )

  /** The items of a Scott list, `[]` the alternative 0 and a cell the
    * alternative 1 with the item and the tail; none when the value has no data
    * head.
    */
  def itemsWritten[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Reading[C, Option[Vector[Value[C]]]] =
    def from(
        rest: Value[C],
        found: Vector[Value[C]]
    ): Reading[C, Vector[Value[C]]] =
      alternative(rest, 2).flatMap(cell(_, found))
    def cell(
        read: (Int, Vector[Value[C]]),
        found: Vector[Value[C]]
    ): Reading[C, Vector[Value[C]]] = read match
      case (0, Vector())           => Computation.pure(found)
      case (1, Vector(item, tail)) => from(tail, found :+ item)
      case (position, other)       =>
        throw KnowledgeReadingError(
          s"a list's alternative $position has ${other.size} fields"
        )
    alternativeWritten(value, 2).flatMap {
      case None       => Computation.pure(None)
      case Some(read) => cell(read, Vector.empty).map(Some(_))
    }

  /** `itemsWritten` of a list that is written. */
  def items[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Vector[Value[C]]] =
    itemsWritten(value).map(written(_, "a list"))

  /** The text of the library's Scott list of bytes (`Literals.textTerm`, what
    * the library's `text/cbor` `from_cbor` of a string gives), each byte the
    * 8-tuple of its bits, high bit first; none when the value has no data head.
    */
  def textWritten[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Option[String]] =
    itemsWritten(value).flatMap {
      case None        => Computation.pure(None)
      case Some(bytes) =>
        Computation
          .traversed(bytes)(byte)
          .map(read =>
            Some(
              codePoints(read, Vector.empty).map(Character.toString(_)).mkString
            )
          )
    }

  /** `textWritten` of a string that is written. */
  def text[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Reading[C, String] = textWritten(value).map(written(_, "a string"))

  /** The literal a trie wraps (`λk. k e1 … ep`, a literal's variable arguments,
    * `CONTRIBUTING.md`, "Terms"), read by structure: the value applied to one
    * handler has one data head, the handler applied to the bits, each a Scott
    * boolean whose alternative 0 is 1, high bit first, eight to a byte. None
    * when the value has no data head. Throws `KnowledgeReadingError` for a
    * number of bits that is no multiple of eight, and as `alternative` and
    * `truth` do. No library function decodes the literal: the host reads its
    * bits, and nowhere in the compiler does the object language decode a text.
    */
  def trieLiteralWritten[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Option[Literal]] =
    alternativeWritten(value, 1).flatMap {
      case None            => Computation.pure(None)
      case Some((_, bits)) =>
        if bits.size % 8 != 0 then
          throw KnowledgeReadingError(
            s"a trie of ${bits.size} bits is no whole number of bytes"
          )
        Computation
          .traversed(bits)(truth)
          .map(read =>
            Some(
              Literal(
                IArray.from(
                  read.grouped(8).map(byteBits => byteValue(byteBits).toByte)
                )
              )
            )
          )
    }

  /** The text of a trie that wraps one CBOR text string (`Literal.textRead`);
    * none when the value has no data head. Throws `KnowledgeReadingError` for a
    * literal of anything else, and as `trieLiteralWritten` does.
    */
  def trieTextWritten[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Option[String]] =
    trieLiteralWritten(value).map(
      _.map(literal =>
        Literal
          .textRead(literal)
          .fold(
            reason =>
              throw KnowledgeReadingError(s"a trie wraps no text: $reason"),
            identity
          )
      )
    )

  /** `trieTextWritten` of a text that is written. */
  def trieText[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, String] =
    trieTextWritten(value).map(written(_, "a trie of a text"))

  /** The integer of a trie that wraps one CBOR integer (`Literal.integerRead`),
    * a scalar a text writes as a literal and the host decodes. Throws
    * `KnowledgeReadingError` for a value with no data head, for a literal of
    * anything else, and as `trieLiteralWritten` does.
    */
  def trieInteger[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, BigInt] =
    trieLiteralWritten(value).map(read =>
      Literal
        .integerRead(written(read, "a trie of an integer"))
        .fold(
          reason =>
            throw KnowledgeReadingError(s"a trie wraps no integer: $reason"),
          identity
        )
    )

  /** The value of the library's Scott integer (`Literals.integerTerm`, what
    * `integer/cbor`'s `from_cbor` gives): the alternative 0 a `binary` natural
    * n, the alternative 1 the natural n of −(n + 1); none when the value has no
    * data head.
    */
  def integerWritten[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Option[BigInt]] =
    alternativeWritten(value, 2).flatMap {
      case None                       => Computation.pure(None)
      case Some((0, Vector(natural))) =>
        naturalBits(natural, Vector.empty).map(bits => Some(naturalOf(bits)))
      case Some((1, Vector(natural))) =>
        naturalBits(natural, Vector.empty).map(bits =>
          Some(-naturalOf(bits) - 1)
        )
      case Some((position, other)) =>
        throw KnowledgeReadingError(
          s"an integer's alternative $position has ${other.size} fields"
        )
    }

  /** `integerWritten` of an integer that is written. */
  def integer[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Reading[C, BigInt] = integerWritten(value).map(written(_, "an integer"))

  /** A Scott boolean, the alternative 0 true (`λt. λf. t`). */
  def truth[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Boolean] =
    alternative(value, 2).map {
      case (position, Vector()) => position == 0
      case (_, other)           =>
        throw KnowledgeReadingError(s"a boolean has ${other.size} fields")
    }

  /** The instruction of a field as its author wrote it, spelled again as the
    * front end spells it, the instructions of the names kept as they are (one
    * more substitution, done by the reading of knowledge only, which changes
    * the language's semantics nowhere else), so that a field written under a
    * let and the same field written out are one instruction: the value's
    * instruction respelled on the IR (`Respelling.respelled`), each closed
    * instruction once, so that the work is linear in the value as a graph.
    */
  def term[C <: NativeSpecializer & Singleton](
      value: Value[C],
      names: Set[Configured[C]]
  )(using C): Configured[C] =
    Respelling.respelled(Values.instruction(value), names)

  /** The term of the value's weak heads: the choice of the one head of each of
    * its parallel sets, each an abstraction read back to the IR, in the order
    * the heads are enumerated; top (`Literals.top`) for a value of no parallel
    * set. Equal to the value as the choice of its parallel sets, the
    * evaluator's disjunctive normal form, for the answers the evaluator finds.
    * Throws `KnowledgeReadingError` for a parallel set of other than one
    * abstraction.
    */
  def headsTerm[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Reading[C, Configured[C]] =
    heads(value).map(sets =>
      val terms = sets
        .map(set =>
          set.heads match
            case Vector(head @ Head.Lambda(_, _, _)) =>
              Values.instruction[C](head.value)
            case other =>
              throw KnowledgeReadingError(
                s"a head of the value is no one abstraction: $other"
              )
        )
        .distinct
      if terms.isEmpty then Defunctionalization.thunkInstruction(Literals.top)
      else ChoiceSpine.nested(terms, (summon[C]: C).choice(_, _))
    )

  /** The term of the Scott tuples a value gives, its spine reduced: the value
    * applied to one handler (`alternatives`), each data head's fields read back
    * to the IR unevaluated, and the choice of the tuples `λt. t F1 … Fn` of
    * them, in the order the heads are enumerated; top (`Literals.top`) for a
    * value of no data head. A file's content is the tuple
    * `λexport. … export M1 … Mn`, its imports under `export`
    * (`CONTRIBUTING.md`, "lambdalattice files export through their first binder
    * `export`"), so its instance is an abstraction before any import is read;
    * applied to the handler, its imports are read, and the term holds what they
    * gave and never the tree, as `headsTerm` of a file whose imports stood in
    * head position did. Equal to the value on what it gives a continuation, by
    * the β rule.
    */
  def tuplesTerm[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Reading[C, Configured[C]] =
    alternatives(value, 1).map(found =>
      val tuples = found
        .map((_, fields) =>
          Defunctionalization.thunkInstruction(
            DeBruijnTerm.Lambda(
              fields.foldLeft(DeBruijnTerm.Variable(0))((tuple, field) =>
                DeBruijnTerm.Apply(
                  tuple,
                  DeBruijnTerm.Constant(Values.instruction(field))
                )
              )
            )
          )
        )
        .distinct
      if tuples.isEmpty then Defunctionalization.thunkInstruction(Literals.top)
      else ChoiceSpine.nested(tuples, (summon[C]: C).choice(_, _))
    )

  /** The one field M of a Scott tuple of one field, `λtuple. tuple M`: a member
    * in continuation passing style, `λk. k M`, or the instance of a file of a
    * tree, which returns a tuple, not a partial function (`CONTRIBUTING.md`,
    * "Terms", module system). The field of a file is its one member, a group of
    * keyed members read by `field`, or a problem's data. Throws
    * `KnowledgeReadingError` for a value that is no tuple of one field.
    */
  def soleField[C <: NativeSpecializer & Singleton](
      tuple: Value[C]
  )(using C): Reading[C, Value[C]] =
    fields(tuple, 1).map {
      case Vector(field) => field
      case other         =>
        throw KnowledgeReadingError(
          s"a tuple of one field has ${other.size} fields"
        )
    }

  /** The term of the one field of a Scott tuple of one field (`soleField`),
    * read back to the IR (`term`, no names).
    */
  def memberTerm[C <: NativeSpecializer & Singleton](tuple: Value[C])(using
      C
  ): Reading[C, Configured[C]] =
    soleField(tuple).map(term(_, Set.empty))

  private def written[Read](read: Option[Read], what: String): Read =
    read.getOrElse(
      throw KnowledgeReadingError(
        s"$what is not written: the value has no data head"
      )
    )

  private def applied[C <: NativeSpecializer & Singleton](
      value: Value[C],
      count: Int
  )(using C): Value[C] =
    (0 until count).foldLeft(value)((function, position) =>
      Value.Apply(
        function,
        NeutralValue(KnowledgeVariable.Alternative(position), Vector.empty)
      )
    )

  private def naturalOf(bits: Vector[Boolean]): BigInt =
    bits.foldRight(BigInt(0))((bit, above) =>
      above * 2 + (if bit then 1 else 0)
    )

  /** The bits of a binary natural (`Literals.naturalTerm`), the low bit first:
    * zero the alternative 0, twice a natural the alternative 1, twice a natural
    * and one the alternative 2.
    */
  private def naturalBits[C <: NativeSpecializer & Singleton](
      value: Value[C],
      found: Vector[Boolean]
  )(using C): Reading[C, Vector[Boolean]] =
    alternative(value, 3).flatMap {
      case (0, Vector())     => Computation.pure(found)
      case (1, Vector(half)) => naturalBits(half, found :+ false)
      case (2, Vector(half)) => naturalBits(half, found :+ true)
      case (position, other) =>
        throw KnowledgeReadingError(
          s"a natural's alternative $position has ${other.size} fields"
        )
    }

  /** The value of a byte, the 8-tuple of its bits, each a Scott boolean whose
    * alternative 0 is 1, high bit first.
    */
  private def byte[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Int] =
    fields(value, 8)
      .flatMap(bits => Computation.traversed(bits)(truth))
      .map(byteValue)

  /** The value of a byte's bits, high bit first. */
  private def byteValue(bits: Vector[Boolean]): Int =
    bits.foldLeft(0)((value, set) => value * 2 + (if set then 1 else 0))

  /** The code points of UTF-8 bytes (RFC 3629: a lead byte 0xxxxxxx, 110xxxxx,
    * 1110xxxx or 11110xxx followed by that many continuation bytes 10xxxxxx).
    * Throws `KnowledgeReadingError` on a malformed sequence.
    */
  @scala.annotation.tailrec
  private def codePoints(bytes: Vector[Int], found: Vector[Int]): Vector[Int] =
    bytes.headOption match
      case None       => found
      case Some(lead) =>
        val rest = bytes.drop(1)
        val (length, initial) =
          if lead < 0x80 then (0, lead)
          else if (lead & 0xe0) == 0xc0 then (1, lead & 0x1f)
          else if (lead & 0xf0) == 0xe0 then (2, lead & 0x0f)
          else if (lead & 0xf8) == 0xf0 then (3, lead & 0x07)
          else
            throw KnowledgeReadingError(
              s"a string's byte $lead starts no UTF-8 sequence"
            )
        val continuation = rest.take(length)
        if continuation.size < length || continuation.exists(byte =>
            (byte & 0xc0) != 0x80
          )
        then
          throw KnowledgeReadingError(
            s"a string's UTF-8 sequence from byte $lead is cut or malformed"
          )
        codePoints(
          rest.drop(length),
          found :+ continuation.foldLeft(initial)((value, byte) =>
            value * 64 + (byte & 0x3f)
          )
        )

  /** Every parallel set of the value under the tabled weak head. */
  private def heads[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Reading[C, Vector[ParallelSet[C]]] =
    WeakHead.heads(Mode.TablingWeakHead, value).collected

  /** The data heads of the value (THE DATA HEADS): of each parallel set, its
    * one head, a handler applied to fields. Throws `KnowledgeReadingError` for
    * a set whose one head is an abstraction, for the empty parallel set, which
    * a least term has and no data does, and for a set of several heads, which
    * no encoding of this reader writes.
    */
  private def dataHeads[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Reading[C, Vector[(NeutralVariable, Vector[Value[C]])]] =
    heads(value).map(
      _.map(set =>
        set.heads match
          case Vector(Head.Neutral(variable, arguments)) =>
            (variable, arguments)
          case Vector(other) =>
            throw KnowledgeReadingError(
              s"a head of the data is no handler applied to fields: $other"
            )
          case Vector() =>
            throw KnowledgeReadingError(
              "the data is a least term, which is no data value"
            )
          case several =>
            throw KnowledgeReadingError(
              s"the data is a parallel of several heads: $several"
            )
      )
    )
