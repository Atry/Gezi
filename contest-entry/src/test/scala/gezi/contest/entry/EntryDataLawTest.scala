package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Literals
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.BuiltInRule
import gezi.ir.Instruction
import gezi.knowledgereading.KnowledgeReading
import gezi.standardlibrary.KnowledgeSlot
import gezi.standardlibrary.KnowledgeText
import gezi.weakhead.Computation
import gezi.weakhead.Value

/** The laws of the entry's data form (`EntryData`). Their purpose is to
  * catch a reader that loses or changes a setting, takes a round's setting
  * from another round, or reads the options of one contribution only when
  * several write them, as presets and an entry do (the round trip), and one
  * that accepts a value that is no constructor of its list, a slot no
  * contribution writes, or a slot two contributions write with two values
  * (the refusals): there is no default, so a reader that supplied one would
  * pass an entry that says less than it must. The
  * knowledge is closed terms written out, since a text read outside the
  * source trees holds no relative path; how a relative path is linked is the
  * directory loader's and the selection elimination's, checked by their own
  * laws.
  */
class EntryDataLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of EntryDataLawTest, "anEntryWrittenInLambdalatticeReadsBackAsItself", takes 7.330 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  /** A part of a round's or the backend's knowledge: a contribution to one
    * slot of the knowledge mixin (`KnowledgeText.mixin`), its member the
    * unary tuple of a closed term `λa. λb. a b … b`.
    */
  private def knowledgeMember(slot: KnowledgeSlot): Gen[String] =
    Gen.int(Range.linear(0, 4)).map(count => contribution(slot, s"(λk. k (λa. λb. a${" b" * count}))"))

  /** The contribution of the member's text to the slot. */
  private def contribution(slot: KnowledgeSlot, member: String): String =
    KnowledgeText.mixin(Vector(slot -> Vector(KnowledgeText.Member(member)))).trim

  private def knowledgeMembers(slot: KnowledgeSlot): Gen[Vector[String]] =
    knowledgeMember(slot).list(Range.linear(0, 3)).map(_.toVector.distinct)

  private def term(text: String): Instruction =
    Defunctionalization.thunkInstruction(Lambdalattice.term(text))

  /** The knowledge of the parts as `EntryText` writes it: their choice, top
    * for none.
    */
  private def knowledgeText(parts: Vector[String]): String =
    if parts.isEmpty then Lambdalattice.text(Literals.top, Map.empty) else parts.mkString("(", " + ", ")")

  /** A round as generated: its knowledge's parts, its settings and the
    * contributions that write them.
    */
  private final case class Round(knowledge: Vector[String], settings: RoundSettings, options: Vector[String]):
    def text: String = EntryText.round(knowledge, options)

  /** Contributions that write the slots together, as several presets and an
    * entry would: the slots split among up to three contributions, each
    * writing its share in one term, and one of them, drawn or none, written
    * twice.
    */
  private def contributions(groupWidths: Vector[Int], slots: Vector[EntryText.OptionSlot]): Gen[Vector[String]] =
    for
      owners <- Gen.int(Range.constant(0, 2)).list(Range.singleton(slots.size))
      repeated <- Gen.int(Range.constant(0, 3))
    yield
      val written = slots.zip(owners).groupBy(_._2).toVector.sortBy(_._1).map((_, owned) => EntryText.contribution(groupWidths, owned.map(_._1)))
      written ++ written.lift(repeated)

  /** One of the published cases of an option's list. */
  private def published[Option](cases: Array[Option]): Gen[Option] = Gen.element1(cases.head, cases.tail*)

  /** A closed term `λa. λb. a b … b` of up to four arguments `b`, the text
    * of a module's selector or parameters: the reader keeps both as written.
    */
  private val closedTerm: Gen[String] = Gen.int(Range.linear(0, 4)).map(count => s"(λa. λb. a${" b" * count})")

  private val round: Gen[Round] =
    for
      knowledge <- knowledgeMembers(KnowledgeSlot.Leaves)
      opening <- Gen.boolean
      chosen <- Gen.boolean.list(Range.singleton(BuiltInRule.values.length))
      indexer <- published(IndexerImplementation.values)
      orientationCompiler <- published(OrientationCompilerImplementation.values)
      saturator <- published(SaturatorImplementation.values)
      enumerationBound <- Gen.long(Range.linear(1L, 1024L))
      wholeFoldBound <- Gen.long(Range.linear(0L, 1024L))
      extractorSelector <- closedTerm
      extractorParameters <- closedTerm
      extractor <- Gen.element1(
        ExtractorImplementation.NarrowBlock(enumerationBound, wholeFoldBound),
        ExtractorImplementation.NarrowListBlock(enumerationBound, wholeFoldBound),
        ExtractorImplementation.Module(term(extractorSelector), term(extractorParameters))
      )
      lemmaEncoding <- published(LemmaEncodingImplementation.values)
      ematching <- published(EmatchingImplementation.values)
      respellings <- published(MemoRetentionOption.values)
      writeBackSpellings <- published(MemoRetentionOption.values)
      openingCriterion <- published(OpeningCriterionOption.values)
      settings = RoundSettings(
        opening,
        BuiltInRule.values.toVector.zip(chosen).collect { case (rule, true) => rule }.toSet,
        indexer,
        orientationCompiler,
        saturator,
        extractor,
        lemmaEncoding,
        ematching,
        respellings,
        writeBackSpellings,
        openingCriterion
      )
      options <- contributions(EntryData.roundGroupWidths, EntryText.roundSlots(settings))
    yield Round(knowledge, settings, options)

  private val options: Gen[JitOptions] =
    for
      instanceTable <- Gen.boolean
      trial <- Gen.long(Range.linear(1L, 1L << 40))
      instanceRetention <- Gen.choice1(
        Gen.int(Range.linear(1, 1 << 22)).map(InstanceRetentionOption.Generations(_)),
        Gen.constant(InstanceRetentionOption.NeverDropped)
      )
      budget <- Gen.int(Range.linear(0, 1 << 20))
      checkpoints <- Gen.choice1(
        Gen.constant(CheckpointOption.Profitable),
        Gen.long(Range.linear(0L, 1L << 40)).map(CheckpointOption.EverySteps(_))
      )
      nativeBlocks <- published(NativeBlocksOption.values)
      lookahead <- Gen.choice1(
        Gen.constant(LookaheadOption.Lazily),
        Gen.long(Range.linear(1L, 1L << 40)).map(LookaheadOption.WithinSteps(_))
      )
    yield JitOptions(
      DispatchOption.Fallback,
      BackendOption.Closure,
      GranularityOption.PredicatePerCode,
      instanceTable,
      trial,
      instanceRetention,
      budget,
      checkpoints,
      nativeBlocks,
      lookahead
    )

  private val readingOptions: Gen[ReadingOptions] =
    for
      application <- published(ApplicationOption.values)
      tableSharing <- published(TableSharingOption.values)
      tableRetention <- Gen.choice1(
        Gen.constant(TableRetentionOption.KeptAll),
        Gen.constant(TableRetentionOption.NoneKept),
        Gen.int(Range.linear(1, 100)).map(TableRetentionOption.DroppedAtPercent(_))
      )
      continuation <- published(ContinuationOption.values)
      parallel <- published(ParallelOption.values)
    yield ReadingOptions(application, tableSharing, tableRetention, continuation, parallel)

  /** An executor as generated: the option and the text that writes it. */
  private final case class WrittenExecutor(option: ExecutorOption, text: String)

  /** The framework's JIT, or a module of a generated selector and
    * parameters.
    */
  private val executor: Gen[WrittenExecutor] =
    Gen.choice1(
      Gen.constant(WrittenExecutor(ExecutorOption.Jit, EntryText.jitExecutor)),
      for
        selector <- closedTerm
        parameters <- closedTerm
      yield WrittenExecutor(ExecutorOption.Module(term(selector), term(parameters)), EntryText.moduleExecutor(selector, parameters))
    )

  /** How many members the knowledge's slot `natives` holds, read as the
    * library reads a slot.
    */
  private def nativesCount(knowledge: Instruction): Int =
    val slot = KnowledgeSlot.Natives
    KnowledgeReading
      .run(
        KnowledgeReading
          .groupSlots(knowledge, KnowledgeSlot.width, slot.group, KnowledgeSlot.groupWidths(slot.group))
          .flatMap(slots => Computation.traversed(slots(slot.position))(KnowledgeReading.members)),
        1000000L
      )
      .flatten
      .size

  property("anEntryWrittenInLambdalatticeReadsBackAsItself") {
    for
      rounds <- round.list(Range.linear(0, 3)).forAll
      backend <- knowledgeMembers(KnowledgeSlot.Natives).forAll
      jit <- options.forAll
      reading <- readingOptions.forAll
      chosen <- executor.forAll
      place <- published(CompilationPlaceOption.values).forAll
      options <- contributions(EntryData.backendGroupWidths, EntryText.backendSlots(jit, reading, chosen.text, place)).forAll
    yield
      val text = EntryText.entry(rounds.toVector.map(_.text), backend, options)
      val data = EntryData.lambdalatticeRead(text)
      Result
        .diff(
          data.rounds,
          rounds.toVector.map(found => EntryRound(term(knowledgeText(found.knowledge)), found.settings))
        )(_ == _)
        .and(Result.diff(data.jit, jit)(_ == _))
        .and(Result.diff(data.reading, reading)(_ == _))
        .and(Result.diff(data.executor, chosen.option)(_ == _))
        .and(Result.diff(data.compilationPlace, place)(_ == _))
        .and(Result.diff(nativesCount(data.backend), backend.size)(_ == _))
        .log(text)
  }

  /** The trie of the text's string literal, `(λk. k "…")`, a value that is
    * no constructor of an option's list and no Scott boolean or integer.
    */
  private def trie(written: String): String = s"(λk. k \"$written\")"

  /** The text of the library's Scott integer of the value. */
  private def number(value: BigInt): String = s"(${Lambdalattice.text(Literals.integerTerm(value), Map.empty)})"

  /** The constructor of a list of one case, but with a field: no constructor
    * of no field, which every published case is.
    */
  private val withAField: String = "(λonly. only (λx. x))"

  private val roundFields: Vector[(String, String)] =
    Vector(
      "opening" -> "(λt. λf. f)",
      "rules" -> "(λbeta. beta)",
      "indexer" -> "(λstandard. standard)",
      "orientation_compiler" -> "(λstandard. standard)",
      "saturator" -> "(λhigher_order. higher_order)",
      "extractor" -> s"((λenumeration_bound whole_fold_bound narrow_block narrow_list_block module. narrow_block enumeration_bound whole_fold_bound) ${number(256)} ${number(1)})",
      "lemma_encoding" -> "(λbaseline. baseline)",
      "ematching" -> "(λclosures interpretation bytecode. closures)",
      "respellings" -> "(λkept not_kept. kept)",
      "write_back_spellings" -> "(λkept not_kept. kept)",
      "opening_criterion" -> "(λcalls_a_head calls_a_head_with_matching_arguments. calls_a_head)"
    )

  private val optionFields: Vector[(String, String)] = Vector(
    "dispatch" -> "(λfallback. fallback)",
    "implementation" -> "(λclosure. closure)",
    "granularity" -> "(λpredicate_per_code. predicate_per_code)",
    "instance_table" -> "(λt. λf. t)",
    "trial" -> number(1024),
    "instance_retention" -> s"((λsize generations never_dropped. generations size) ${number(524288)})",
    "budget" -> number(10000),
    "checkpoints" -> "(λprofitable every_steps. profitable)",
    "lookahead" -> "(λlazily within_steps. lazily)",
    "native_blocks" -> "(λnone. none)",
    "application" -> "(λby_layer by_spine by_shared_prefix. by_layer)",
    "table_sharing" -> "(λlocal strong soft_values weak_keys. local)",
    "table_retention" -> "(λkept_all none_kept dropped_at_percent. none_kept)",
    "continuation" -> "(λsubstituted packed. substituted)",
    "parallel" -> "(λboth_sides heads_met. both_sides)",
    "executor" -> "(λjit module. jit)",
    "compilation_place" -> "(λupfront by_executor. upfront)"
  )

  /** The slots' names of each group of a round's options,
    * `implementations` and `behaviour`, in order.
    */
  private val roundGroups: Vector[Vector[String]] = Vector(
    Vector("indexer", "orientation_compiler", "saturator", "extractor", "lemma_encoding", "ematching"),
    Vector("opening", "rules", "respellings", "write_back_spellings", "opening_criterion")
  )

  /** The slots' names of each group of the backend's options, `jit`,
    * `instances`, `reading` and `execution`, in order.
    */
  private val optionGroups: Vector[Vector[String]] = Vector(
    Vector("dispatch", "implementation", "granularity", "native_blocks", "budget", "trial"),
    Vector("instance_table", "instance_retention", "checkpoints", "lookahead"),
    Vector("application", "table_sharing", "table_retention", "continuation", "parallel"),
    Vector("executor", "compilation_place")
  )

  /** The knowledge of the round and of the backend, a contribution of one
    * leaf.
    */
  private val someKnowledge: String = contribution(KnowledgeSlot.Leaves, "(λk. k (λx. x))")

  /** The options coproduct of the fields, one contribution for each field,
    * to the slot of its name in the layout's groups, joined by the choice: a
    * name written by several fields is written by several contributions, and
    * a name no field gives is a slot no contribution writes.
    */
  private def coproduct(layout: Vector[Vector[String]], fields: Vector[(String, String)]): String =
    val slots = fields.map((name, value) =>
      val group = layout.indexWhere(_.contains(name))
      EntryText.OptionSlot(group, layout(group).indexOf(name), value)
    )
    slots.map(slot => EntryText.contribution(layout.map(_.size), Vector(slot))).mkString("(", " + ", ")")

  /** An entry's text: a tuple of one field, the compiler. */
  private def entryOf(compiler: String): String = s"λexport. export ($compiler)"

  private def roundText(round: Vector[(String, String)]): String = s"(λs. s $someKnowledge ${coproduct(roundGroups, round)})"

  private def backendText(options: Vector[(String, String)]): String = s"(λs. s $someKnowledge ${coproduct(optionGroups, options)})"

  private def entryText(round: Vector[(String, String)], options: Vector[(String, String)]): String =
    entryOf(s"λs. s ${EntryText.scottList(Vector(roundText(round)), " ")} ${backendText(options)}")

  /** The fields with the key's value replaced. */
  private def replaced(fields: Vector[(String, String)], key: String, value: String): Vector[(String, String)] =
    fields.map((found, written) => if found == key then (found, value) else (found, written))

  /** For each field, a value other than the one `roundFields` and
    * `optionFields` write.
    */
  private val otherValues: Map[String, String] = Map(
    "opening" -> "(λt. λf. t)",
    "rules" -> withAField,
    "indexer" -> withAField,
    "orientation_compiler" -> withAField,
    "saturator" -> withAField,
    "extractor" -> s"((λenumeration_bound whole_fold_bound narrow_block narrow_list_block module. narrow_list_block enumeration_bound whole_fold_bound) ${number(256)} ${number(1)})",
    "lemma_encoding" -> withAField,
    "ematching" -> "(λclosures interpretation bytecode. interpretation)",
    "respellings" -> "(λkept not_kept. not_kept)",
    "write_back_spellings" -> "(λkept not_kept. not_kept)",
    "opening_criterion" -> "(λcalls_a_head calls_a_head_with_matching_arguments. calls_a_head_with_matching_arguments)",
    "dispatch" -> withAField,
    "implementation" -> withAField,
    "granularity" -> withAField,
    "instance_table" -> "(λt. λf. f)",
    "trial" -> number(2048),
    "instance_retention" -> "(λgenerations never_dropped. never_dropped)",
    "budget" -> number(20000),
    "checkpoints" -> s"((λinterval profitable every_steps. every_steps interval) ${number(64)})",
    "lookahead" -> s"((λsteps lazily within_steps. within_steps steps) ${number(1000)})",
    "native_blocks" -> withAField,
    "application" -> "(λby_layer by_spine by_shared_prefix. by_spine)",
    "table_sharing" -> "(λlocal strong soft_values weak_keys. strong)",
    "table_retention" -> s"((λpercent kept_all none_kept dropped_at_percent. dropped_at_percent percent) ${number(50)})",
    "continuation" -> "(λsubstituted packed. packed)",
    "parallel" -> "(λboth_sides heads_met. heads_met)",
    "executor" -> "((λselector parameters jit module. module selector parameters) (λx. x) (λx. x))",
    "compilation_place" -> "(λupfront by_executor. by_executor)"
  )

  /** The fields with the key written once more, with another value, by
    * another contribution.
    */
  private def writtenWithAnother(fields: Vector[(String, String)], key: String): Vector[(String, String)] =
    fields :+ (key -> otherValues(key))

  /** Entries that differ from a well-formed one, which the first property's
    * generator also covers, in one slot: a value that is no constructor of
    * its list (a constructor with a field, or the trie of the name an entry
    * wrote before the options were Scott constructors), a value of another
    * shape, a slot no contribution writes, or a slot two contributions write
    * with two values, a conflict the reader reports and never settles. A
    * slot written twice with one value is not among them: equal readings
    * are one (`aFieldWrittenTwiceWithOneValueIsWrittenOnce`). Nor is `rules`
    * left out: it is a set, the join of its contributions, and no
    * contribution is the empty set, as top is.
    */
  private val wrong: Vector[String] =
    Vector(
      replaced(roundFields, "rules", withAField),
      replaced(roundFields, "rules", trie("beta")),
      replaced(roundFields, "indexer", withAField),
      replaced(roundFields, "indexer", trie("standard")),
      replaced(roundFields, "orientation_compiler", withAField),
      replaced(roundFields, "saturator", withAField),
      replaced(roundFields, "extractor", withAField),
      replaced(roundFields, "extractor", s"((λenumeration_bound whole_fold_bound narrow_block narrow_list_block module. narrow_block enumeration_bound whole_fold_bound) ${number(0)} ${number(1)})"),
      replaced(roundFields, "extractor", s"((λenumeration_bound whole_fold_bound narrow_block narrow_list_block module. narrow_list_block enumeration_bound whole_fold_bound) ${number(0)} ${number(1)})"),
      replaced(roundFields, "lemma_encoding", withAField),
      replaced(roundFields, "ematching", withAField),
      replaced(roundFields, "respellings", withAField),
      replaced(roundFields, "write_back_spellings", withAField),
      replaced(roundFields, "opening_criterion", withAField),
      replaced(roundFields, "extractor", trie("narrow_block")),
      replaced(roundFields, "extractor", "((λselector narrow_block narrow_list_block module. module selector) (λx. x))"),
      replaced(roundFields, "opening", trie("true"))
    ).map(entryText(_, optionFields)) ++
      Vector(
        replaced(optionFields, "dispatch", withAField),
        replaced(optionFields, "dispatch", trie("fallback")),
        replaced(optionFields, "implementation", withAField),
        replaced(optionFields, "granularity", withAField),
        replaced(optionFields, "trial", number(0)),
        replaced(optionFields, "instance_retention", s"((λsize generations never_dropped. generations size) ${number(0)})"),
        replaced(optionFields, "instance_retention", "(λgenerations never_dropped. generations)"),
        replaced(optionFields, "instance_retention", withAField),
        replaced(optionFields, "trial", trie("1024")),
        replaced(optionFields, "budget", number(-1)),
        replaced(optionFields, "checkpoints", withAField),
        replaced(optionFields, "lookahead", withAField),
        replaced(optionFields, "lookahead", s"((λsteps lazily within_steps. within_steps steps) ${number(0)})"),
        replaced(optionFields, "checkpoints", s"((λinterval profitable every_steps. every_steps interval) ${number(-1)})"),
        replaced(optionFields, "checkpoints", "((λinterval profitable every_steps. every_steps interval) (λt. λf. t))"),
        replaced(optionFields, "native_blocks", withAField),
        replaced(optionFields, "application", withAField),
        replaced(optionFields, "table_sharing", withAField),
        replaced(optionFields, "table_retention", withAField),
        replaced(optionFields, "table_retention", s"((λpercent kept_all none_kept dropped_at_percent. dropped_at_percent percent) ${number(0)})"),
        replaced(optionFields, "table_retention", s"((λpercent kept_all none_kept dropped_at_percent. dropped_at_percent percent) ${number(101)})"),
        replaced(optionFields, "executor", withAField),
        replaced(optionFields, "executor", trie("jit")),
        replaced(optionFields, "executor", "((λselector jit module. module selector) (λx. x))"),
        replaced(optionFields, "compilation_place", withAField),
        replaced(optionFields, "compilation_place", trie("upfront"))
      ).map(entryText(roundFields, _)) ++
      roundFields.collect { case (key, _) if key != "rules" => entryText(roundFields.filterNot(_._1 == key), optionFields) } ++
      optionFields.map((key, _) => entryText(roundFields, optionFields.filterNot(_._1 == key))) ++
      roundFields.map((key, _) => entryText(writtenWithAnother(roundFields, key), optionFields)) ++
      optionFields.map((key, _) => entryText(roundFields, writtenWithAnother(optionFields, key))) ++
      Vector(
        entryOf(s"λs. s ${backendText(optionFields)}"),
        entryOf(s"λs. s ${EntryText.scottList(Vector(roundText(roundFields)), " ")}")
      )

  /** Its purpose is to catch refusals that refuse for another reason than
    * the one field: the entry the wrong ones are made from reads.
    */
  test("theEntryTheWrongOnesAreMadeFromReads") {
    assert(EntryData.lambdalatticeRead(entryText(roundFields, optionFields)).rounds.nonEmpty)
  }

  /** Every wrong entry, each once: the texts are fixed, so a draw among
    * them could only leave some out.
    */
  test("anEntryWrongInOneFieldIsRefused") {
    val accepted = wrong.filterNot(text =>
      scala.util.Try(EntryData.lambdalatticeRead(text)).failed.toOption.exists {
        case _: EntryDataError => true
        case _                 => false
      }
    )
    assertEquals(accepted, Vector.empty[String])
  }

  /** Its purpose is to catch a reader that counts the writings of a field
    * and not its values: an entry one of whose fields is written twice with
    * one value reads as the entry. Every field, each once.
    */
  test("aFieldWrittenTwiceWithOneValueIsWrittenOnce") {
    val once = EntryData.lambdalatticeRead(entryText(roundFields, optionFields))
    val twice =
      roundFields.map(field => entryText(roundFields :+ field, optionFields)) ++
        optionFields.map(field => entryText(roundFields, optionFields :+ field))
    def settings(data: EntryData) =
      (data.rounds.map(_.settings), data.jit, data.reading, data.executor, data.compilationPlace)
    twice.foreach(text => assertEquals(settings(EntryData.lambdalatticeRead(text)), settings(once), text))
  }
