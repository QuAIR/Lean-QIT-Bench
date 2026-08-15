/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.ChannelsAndChoiRepresentations.ChoiPositivityCharacterizationCompletePositivity.Definitions
@[expose] public section

namespace QITBench.ChoiPositivityCharacterizationCompletePositivity

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {A Ap B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype Ap] [DecidableEq Ap]
    [Fintype B] [DecidableEq B]
    (e : A ≃ Ap)
    (Phi : MatrixMap Ap B) :
    IsCompletelyPositiveOnAllReferences Phi ↔
      (relabeledChoiMatrix e Phi).PosSemidef := by
  sorry

end

end QITBench.ChoiPositivityCharacterizationCompletePositivity
