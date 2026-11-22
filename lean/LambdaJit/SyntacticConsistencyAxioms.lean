import LambdaJit.SyntacticConsistency

/-!
# The axioms of the syntactic consistency proof

`#print axioms` for the main theorems of modules `BetaEtaConfluence` and `SyntacticConsistency`,
printed on every build of this module. Recorded 2026-11-07:

    'LambdaJit.BetaEtaConfluence.ReducesMany.confluent' depends on axioms: [propext, Quot.sound]
    'LambdaJit.BetaEtaConfluence.firstNotConvertibleSecond' depends on axioms: [propext, Quot.sound]
    'LambdaJit.SyntacticConsistency.ReducesMany.confluent' depends on axioms: [propext, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof.
-/

#print axioms LambdaJit.BetaEtaConfluence.ReducesMany.confluent
#print axioms LambdaJit.BetaEtaConfluence.firstNotConvertibleSecond
#print axioms LambdaJit.SyntacticConsistency.ReducesMany.confluent
