import LambdaJit.Encoding

/-!
# The axioms of the encoding theorems

`#print axioms` for the theorems of module `Encoding`, link (ii) of D6, printed on every build of this module. Recorded
2026-11-16, after thunk constants took their names from a signature (D7.1), and again the same day
after the operator of the empty choice left `fixedName`:

    'LambdaJit.Encoding.operatorOfNameOf' depends on axioms: [propext, Quot.sound]
    'LambdaJit.Encoding.readEncode' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.Encoding.endToEndEncoded' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Encoding.endToEndEncodedOfChecked' depends on axioms:
      [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof.
-/

#print axioms LambdaJit.Encoding.operatorOfNameOf
#print axioms LambdaJit.Encoding.readEncode
#print axioms LambdaJit.Encoding.endToEndEncoded
#print axioms LambdaJit.Encoding.endToEndEncodedOfChecked
