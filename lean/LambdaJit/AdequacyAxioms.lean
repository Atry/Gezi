import LambdaJit.Adequacy

/-!
# The axioms of module `Adequacy`

`#print axioms` for `defunctionalizationFacts`, what is proved of D3's items in module `Adequacy`,
and the theorems of module `Defunctionalization` it is proved from: D3's item 3, the injectivity of
the defunctionalization (the converse of item 2, which holds by construction) and item 5, with
`defunctionalizeDefined`; for link (i) of D6 for the front end of that module
(`readbackThunkInstruction`, `thunkInstructionDefined`, `readbackOfThunkInstruction`); for the five
theorems of the agreement of the defunctionalization with `thunk_instruction/2`
(`Defunctionalization.Agreement`); for the witnesses that link (i) is stated on readbacks, a library
name (`Defunctionalization.Agreement.libraryNameReadback`, `libraryNameFrontEnd`,
`libraryNameOneReadback`) and a right-nested chain of choices
(`Defunctionalization.Agreement.choiceFrontEnd`); for the refutation of the
converse of D3's item 4 and its witnesses; and for the joinability of the IR theory and its
separation theorems in module `Confluence`, printed on every build of this module. Recorded
2026-10-10 (`Quot.sound` enters through `Program.equality_of_equal`, the soundness of the
comparison of programs that the canonical numbering uses: the slot of a source is found by the
decidable equality of sources, which that theorem gives, so the definition `thunkInstruction`
itself depends on `Quot.sound`, and so does every theorem below that is about it):

    'LambdaJit.Adequacy.defunctionalizationFacts' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Adequacy.consistentNormalFormsDefunctionalize' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Adequacy.converseFails' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.Adequacy.converseFailsUnderBinder' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Adequacy.converseFailsForBeta' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Adequacy.converseFailsWithoutNumberedEquations' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Adequacy.converseFailsOnOneReadback' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Adequacy.libraryNameOneReadback' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Defunctionalization.readbackThunkInstruction' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.thunkInstructionDefined' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.readbackOfThunkInstruction' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.readbackDefunctionalize' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.defunctionalizeInjective' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.defunctionalizeDefined' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Witness.addressesFinerThanAlpha' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.chainOfTwo' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.unreadBinder' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.binderReadTwice' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.innerChain' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.sharedClosedSubterm' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.libraryNameReadback' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.libraryNameFrontEnd' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Defunctionalization.Agreement.choiceFrontEnd' depends on axioms:
      [propext, Quot.sound]
    'LambdaJit.Confluence.confluent' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.Confluence.equalJoinable' depends on axioms: [propext, Classical.choice, Quot.sound]
    'LambdaJit.Confluence.reducesManyThunkKeeps' depends on axioms: [propext]
    'LambdaJit.Confluence.notEqualThunks' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'LambdaJit.Confluence.notEqualChoices' depends on axioms:
      [propext, Classical.choice, Quot.sound]

Only Lean's built-in axioms are listed.
-/

#print axioms LambdaJit.Adequacy.defunctionalizationFacts
#print axioms LambdaJit.Adequacy.consistentNormalFormsDefunctionalize
#print axioms LambdaJit.Adequacy.converseFails
#print axioms LambdaJit.Adequacy.converseFailsUnderBinder
#print axioms LambdaJit.Adequacy.converseFailsForBeta
#print axioms LambdaJit.Adequacy.converseFailsWithoutNumberedEquations
#print axioms LambdaJit.Adequacy.converseFailsOnOneReadback
#print axioms LambdaJit.Adequacy.libraryNameOneReadback
#print axioms LambdaJit.Defunctionalization.readbackThunkInstruction
#print axioms LambdaJit.Defunctionalization.thunkInstructionDefined
#print axioms LambdaJit.Defunctionalization.readbackOfThunkInstruction
#print axioms LambdaJit.Defunctionalization.readbackDefunctionalize
#print axioms LambdaJit.Defunctionalization.defunctionalizeInjective
#print axioms LambdaJit.Defunctionalization.defunctionalizeDefined
#print axioms LambdaJit.Defunctionalization.Witness.addressesFinerThanAlpha
#print axioms LambdaJit.Defunctionalization.Agreement.chainOfTwo
#print axioms LambdaJit.Defunctionalization.Agreement.unreadBinder
#print axioms LambdaJit.Defunctionalization.Agreement.binderReadTwice
#print axioms LambdaJit.Defunctionalization.Agreement.innerChain
#print axioms LambdaJit.Defunctionalization.Agreement.sharedClosedSubterm
#print axioms LambdaJit.Defunctionalization.Agreement.libraryNameReadback
#print axioms LambdaJit.Defunctionalization.Agreement.libraryNameFrontEnd
#print axioms LambdaJit.Defunctionalization.Agreement.choiceFrontEnd
#print axioms LambdaJit.Confluence.confluent
#print axioms LambdaJit.Confluence.equalJoinable
#print axioms LambdaJit.Confluence.reducesManyThunkKeeps
#print axioms LambdaJit.Confluence.notEqualThunks
#print axioms LambdaJit.Confluence.notEqualChoices
