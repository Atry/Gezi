import LambdaJit.LemmaSoundness
import LambdaJit.EndToEndFixtures

/-!
# The axioms of the soundness of statements by the normaliser

`#print axioms` for the general theorem of module `StatementNormalisation`, its form at the fixed
fuel, the theorem of joint contraction at its fixed fuel, the theorem of the instances of the
numbered equations, the theorem of absorbed members at its fixed bound, the form at the larger
fuel, and the fixture that proves `identity_applied` by the normaliser (module `EndToEndFixtures`),
printed on every build of this module. Recorded 2026-10-07, the absorbed members 2026-10-28, the
larger fuel 2026-11-21:

    'LambdaJit.StatementNormalisation.equationSoundOfNormalisedEqual' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.StatementNormalisation.statementSoundOfNormalised' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.StatementNormalisation.statementSoundOfContracted' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.StatementNormalisation.numberedInstanceSound' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.StatementNormalisation.statementSoundOfAbsorbed' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.StatementNormalisation.statementSoundOfNormalisedLong' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.EndToEndFixtures.identityAppliedNormalised' depends on axioms:
      [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed: the kernel evaluates the decisions (`decide +kernel` in the
fixture, `Eq.refl true` checked by the kernel in the command `lemma_soundness` of module
`LemmaSoundness`), so there is no `Lean.ofReduceBool`. A lemma that the command declares as a
theorem by a decision depends on these axioms and no other.
-/

#print axioms LambdaJit.StatementNormalisation.equationSoundOfNormalisedEqual
#print axioms LambdaJit.StatementNormalisation.statementSoundOfNormalised
#print axioms LambdaJit.StatementNormalisation.statementSoundOfContracted
#print axioms LambdaJit.StatementNormalisation.numberedInstanceSound
#print axioms LambdaJit.StatementNormalisation.statementSoundOfAbsorbed
#print axioms LambdaJit.StatementNormalisation.statementSoundOfNormalisedLong
#print axioms LambdaJit.EndToEndFixtures.identityAppliedNormalised
