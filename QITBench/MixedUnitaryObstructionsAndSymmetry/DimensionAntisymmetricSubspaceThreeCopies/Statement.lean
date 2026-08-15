/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.DimensionAntisymmetricSubspaceThreeCopies.Definitions
@[expose] public section

namespace QITBench.DimensionAntisymmetricSubspaceThreeCopies

noncomputable section

theorem main
    (H : Type*) [Fintype H]
    (d : ℕ)
    (hd : Fintype.card H = d) :
    antisymmetricSubspaceDimensionThreeCopies H = Nat.choose d 3 ∧
      (antisymmetricSubspaceDimensionThreeCopies H : ℚ) =
        ((d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2)) / 6 := by
  sorry

end

end QITBench.DimensionAntisymmetricSubspaceThreeCopies
