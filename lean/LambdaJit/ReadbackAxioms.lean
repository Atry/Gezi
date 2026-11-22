import LambdaJit.Readback

/-!
# The axioms of the readback theorems

`#print axioms` for the soundness theorem of module `Readback`, the theorem it is proved from,
its three statements per rule, the agreement of the readback with D3's reading, and the
equality in λ-lattice-η on defunctionalized terms of the witness against that reading on
thunks whose fills clamp, printed on every build of this module. Recorded 2026-10-04:

    'LambdaJit.Readback.readbackSound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.Readback.interpretationSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Readback.readbackBetaFill' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Readback.readbackBetaInstance' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Readback.readbackEta' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.Readback.finalSlotsStatic' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Readback.Witness.applicationsEqual' depends on axioms: [propext]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof.
-/

#print axioms LambdaJit.Readback.readbackSound
#print axioms LambdaJit.Readback.interpretationSound
#print axioms LambdaJit.Readback.readbackBetaFill
#print axioms LambdaJit.Readback.readbackBetaInstance
#print axioms LambdaJit.Readback.readbackEta
#print axioms LambdaJit.Readback.finalSlotsStatic
#print axioms LambdaJit.Readback.Witness.applicationsEqual
