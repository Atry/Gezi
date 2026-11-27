package com.yang_bo.gezi.proofs

import com.yang_bo.gezi.standardlibrary.LibraryFiles

/** The port of the third unit of `gezi/tests/lean_statements.plt`, on the
  * native route's library, native_types, native_arithmetic,
  * hindley_milner_unions, native_arithmetic_unions, occurrence_erasure and
  * closure_application, with prolog_backend_shapes, whose lemmas the native
  * route's type check takes with the Prolog backend. Its export is a module of
  * the Lean package, `lean/LambdaJit/NativeRouteLibraryStatements.lean`, so
  * that the package can take the articles of the fixpoint runs through the
  * end-to-end theorem with these statements (module FixpointRunFixtures); the
  * Nix build of the package has only gezi/lean as its source. The unit checks
  * that the committed module is the export byte for byte, and then reads off
  * the package's declarations, in a temporary file that imports the module and
  * that Lean runs on against the package built first, the kind of every lemma's
  * soundness declaration (soundnessKind) and its `#print axioms`; it checks the
  * kinds against `expectedKinds` and the axioms against Lean's built-in ones:
  * every lemma is a theorem. The environment and the kernel's evaluation decide
  * which kind proves each, and the table is the baseline they are checked
  * against, the reading of 2026-10-29. Lean prints nothing but the kinds and
  * the axioms: anything else fails the test. The elaboration of
  * NativeRouteLibraryStatements, which declares the soundness of the 89 lemmas
  * it then held, took 83 seconds and a peak resident memory of about 2.6 GB
  * (measured 2026-10-30 for the Prolog test); it holds 111 since 2026-11-23.
  */
class LeanStatementsNativeRouteTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-21 on 4 CPUs (nice 10), cold (an empty Lake cache and build directory), under a machine load
  // of 8.3 to 13.3, after the kernel's decisions on the markers' literals were made cheaper and the markers' keys
  // took the prefix `$`: the test's `lake build` of the package takes 458 s, of
  // which module NativeRouteLibraryStatements 91 s, module FixpointRunSides 169 s and module FixpointRunFixtures,
  // which imports both, 216 s. The bound is 1.5 times the package's build and the test's 5 s, rounded up to 5 s.
  // Module FixpointRunFixtures is the kernel's evaluation of the reader over seven articles of 4304 to 12682 lines
  // (its documentation has the readings); no single check of the reader costs most of it (on
  // successor_zero_type_check, skipping the type check of appTerm saved 4 s of 33 s, of trans, axiom or thm less),
  // and checking the articles in parallel modules needs their memory at once (8.0 GB for the largest alone).
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(695, "s")

  // Exporting lemma statements to Lean to prove them is not a compiler configuration; the lemmas' soundness does
  // not depend on the backend. The knowledge
  // is the one field of tests/library_fixtures/native_route_lemmas.lambdalattice, the choice of the native route's
  // knowledge files without a backend's preset.
  private lazy val library =
    LibraryFiles.compiled(
      "tests/library_fixtures/native_route_lemmas.lambdalattice",
      Vector.empty
    )

  /** The native route's library, forced before the first test and not charged
    * to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library)

  /** What declares the soundness of each lemma of the native route's library,
    * in the order of the index: the decision of absorbed members for every
    * lemma but eight. unions_absorption is an instance of the numbered equation
    * (6) (measured 2026-10-29). The two lemmas of occurrence_erasure,
    * closure_applied and repelled_erased are declared by the decision of the
    * normal form within 1,000 contractions (measured 2026-11-21 and 2026-11-23,
    * the markers spelled as tags): their two sides differ only by the markers
    * `$name`, `$closure` and `$repelled`, identities by the β rule alone, and
    * in that spelling a marker's literal takes 344 to 516 contractions, more
    * than the normaliser's fuel of 100. The three repeller lemmas of
    * prolog_backend_shapes, `L = $repelled L`, are declared by the decision of
    * one side reached from the other by contraction: L holds fixpoints, so
    * neither side has a normal form, and the right side's contractions reach
    * the left after 565 (measured 2026-11-23). The decision of absorbed members
    * accepts the candidacies, the refutations, the other markers' lemmas, the
    * typed versions and the contracts of prolog_backend_shapes.
    */
  private val expectedKinds: Vector[(String, String)] =
    val modules = Vector(
      "native_types" -> Vector(
        "zero_scheme",
        "successor_scheme",
        "true_scheme",
        "false_scheme",
        "boolean_not_scheme",
        "nil_scheme",
        "cons_scheme",
        "identity_scheme",
        "konstant_scheme",
        "compose_scheme",
        "fixpoint_scheme",
        "nat_fold_scheme",
        "list_fold_scheme",
        "repelled_erased"
      ),
      "native_arithmetic" -> Vector("double_scheme", "even_scheme"),
      "hindley_milner_unions" -> Vector(
        "unions_absorption",
        "unions_parallel_idempotence",
        "unions_first_of_two_scheme",
        "unions_second_of_two_scheme",
        "unions_second_of_two_one_field_scheme",
        "unions_second_of_two_two_fields_scheme",
        "unions_boolean_not_scheme",
        "unions_identity_scheme",
        "unions_konstant_scheme",
        "unions_compose_scheme",
        "unions_fixpoint_scheme",
        "unions_nat_fold_scheme",
        "unions_list_fold_scheme",
        "unions_recursive_type_unfolding",
        "unions_occurrence_typed",
        "unions_occurrence_candidate",
        "unions_candidate_instance",
        "unions_structure_activation",
        "unions_function_activation",
        "unions_application_typed",
        "unions_type_choice",
        "unions_closure_typed",
        "unions_closure_type",
        "unions_closure_body",
        "unions_closure_curried",
        "unions_parameter_typed",
        "unions_unify_type_of_left",
        "unions_unify_type_of_right",
        "unions_unify_structure_left",
        "unions_unify_structure_right",
        "unions_unify_alternative_left",
        "unions_unify_alternative_right",
        "unions_unify_no_alternative_left",
        "unions_unify_no_alternative_right",
        "unions_unify_field_left",
        "unions_unify_field_right",
        "unions_unify_no_field_left",
        "unions_unify_no_field_right",
        "unions_unify_function_left",
        "unions_unify_function_right",
        "unions_unify_variable_left",
        "unions_unify_variable_right",
        "unions_function_decomposition",
        "unions_structure_decomposition",
        "unions_alternative_decomposition",
        "unions_field_decomposition"
      ),
      "native_arithmetic_unions" -> Vector(
        "unions_double_scheme",
        "unions_even_scheme"
      ),
      "occurrence_erasure" -> Vector(
        "occurrence_name_erased",
        "occurrence_closure_erased"
      ),
      "closure_application" -> Vector("closure_applied"),
      "prolog_backend_shapes" -> Vector(
        "shapes_natural_candidate",
        "shapes_natural_item_candidate",
        "shapes_boolean_candidate",
        "shapes_boolean_item_candidate",
        "shapes_natural_field_candidate",
        "shapes_list_candidate",
        "shapes_list_cell_candidate",
        "shapes_list_item_candidate",
        "shapes_list_tail_item_candidate",
        "shapes_nested_list_candidate",
        "shapes_list_fields_candidate",
        "shapes_list_head_refuted",
        "shapes_list_tail_refuted",
        "shapes_natural_field_refuted",
        "shapes_function_refuted",
        "shapes_list_refuted_first_field",
        "shapes_list_refuted_alternatives",
        "shapes_list_refuted_fields",
        "shapes_list_refuted_one_field",
        "shapes_list_refuted_no_field",
        "shapes_boolean_refuted_first_field",
        "shapes_boolean_refuted_alternatives",
        "shapes_boolean_refuted_field",
        "shapes_natural_refuted_first_field",
        "shapes_natural_refuted_alternatives",
        "shapes_natural_refuted_fields",
        "shapes_natural_refuted_no_field",
        "shapes_unify_refuted_left",
        "shapes_unify_refuted_right",
        "shapes_unify_candidate_left",
        "shapes_unify_candidate_right",
        "shapes_unify_item_candidate_left",
        "shapes_unify_item_candidate_right",
        "shapes_domain_candidate",
        "shapes_function_candidate",
        "shapes_typed_version_domain",
        "shapes_typed_version_function",
        "shapes_list_tail_domain_repelled",
        "shapes_range_repelled",
        "shapes_filter_repelled",
        "shapes_contract",
        "shapes_curried_contract",
        "shapes_contract_at_range",
        "shapes_contract_at_curried"
      )
    )
    val normalisedLong = Set(
      "occurrence_name_erased",
      "occurrence_closure_erased",
      "closure_applied",
      "repelled_erased"
    )
    val reached = Set(
      "shapes_list_tail_domain_repelled",
      "shapes_range_repelled",
      "shapes_filter_repelled"
    )
    for
      (_, names) <- modules
      name <- names
    yield (
      name,
      if name == "unions_absorption" then "numbered_instance"
      else if normalisedLong(name) then "long_normal_form"
      else if reached(name) then "reached_by_contraction"
      else "absorbed_members"
    )

  private def written(file: java.nio.file.Path, text: String): Unit =
    java.nio.file.Files
      .writeString(file, text, java.nio.charset.StandardCharsets.UTF_8)

  // With the environment variable `GEZI_WRITE_NATIVE_ROUTE_STATEMENTS` set, the test first writes the export to
  // the module, as OpentheoryArticleFixpointRunsTest's `GEZI_WRITE_FIXPOINT_RUNS` writes the runs' modules, then
  // checks it as always; a change of the module is reviewed in its diff.
  test("theLeanModuleOfTheNativeRouteStatementsIsTheirExport") {
    val module =
      ProofTestFiles.leanModules.resolve("NativeRouteLibraryStatements.lean")
    val exported = LeanStatementsChecks.exportedText(library)
    if sys.env.contains("GEZI_WRITE_NATIVE_ROUTE_STATEMENTS") then
      written(module, exported)
    assertEquals(ProofTestFiles.textRead(module), exported)
  }

  stoppableTest("theNativeRouteLemmasAreTheoremsAsRecorded") { stopped =>
    val names = LeanStatements.names(library)
    val text = Vector(
      "import LambdaJit.NativeRouteLibraryStatements",
      "",
      "namespace LambdaJit.LeanStatementsCheck",
      "",
      LeanStatementsChecks.kindDefinitions,
      "end LambdaJit.LeanStatementsCheck",
      "",
      LeanStatementsChecks.lemmaLines(names),
      ""
    ).mkString("\n")
    val normalised =
      ProofTestFiles.normalisedOutput(
        ProofTestFiles.leanRun(
          text,
          "lean_statements_native_route",
          Seq.empty,
          stopped
        )
      )
    val printed = names.map(name =>
      (name, LeanStatementsChecks.kindMessage(normalised, name)._3)
    )
    assertEquals(printed, expectedKinds)
    val theorems = names.map(LeanStatementsChecks.lemmaAxiom)
    theorems.foreach(theorem =>
      assertEquals(
        (theorem, ProofTestFiles.printedAxioms(normalised, theorem)),
        (theorem, ProofTestFiles.builtInAxioms)
      )
    )
    assertEquals(
      ProofTestFiles.otherOutput(
        LeanStatementsChecks.kindsRemoved(normalised, names),
        theorems
      ),
      ""
    )
  }
