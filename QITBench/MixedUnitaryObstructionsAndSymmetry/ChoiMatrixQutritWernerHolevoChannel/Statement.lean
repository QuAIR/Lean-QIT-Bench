/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.ChoiMatrixQutritWernerHolevoChannel.Definitions
@[expose] public section

namespace QITBench.ChoiMatrixQutritWernerHolevoChannel

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main :
    MatrixMap.choi Phi = antisymmetricProjectorQutrit ∧
      MatrixMap.choi Phi =
        ((1 / 2 : ℂ) •
          ((1 : CMatrix (Fin 3 × Fin 3)) - swapOperator)) ∧
        MatrixMap.IsCompletelyPositive Phi := by
  sorry

end

end QITBench.ChoiMatrixQutritWernerHolevoChannel
