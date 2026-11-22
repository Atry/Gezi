import LambdaJit.Article

/-!
# The axioms of the article reader's soundness

`#print axioms` for the soundness theorem of module `Article`, printed on every build of this
module. Recorded 2026-10-04:

    'LambdaJit.Article.readArticle_sound' depends on axioms: [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: there is no named axiom, and no placeholder of an
unfinished proof. The lemmas it rests on need fewer (`step_sound` and `runCommands_sound` only
`propext`, `Derivable.instantiate` none); the other two enter through the case analysis of the
final proof.
-/

#print axioms LambdaJit.Article.readArticle_sound
