module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.DimensionSymmetricSubspaceThreeCopies.Definitions
@[expose] public section

namespace QITBench.DimensionSymmetricSubspaceThreeCopies

noncomputable section

theorem main
    (H : Type*) [Fintype H]
    (d : ℕ)
    (hd : Fintype.card H = d) :
    symmetricSubspaceDimensionThreeCopies H = Nat.choose (d + 2) 3 ∧
      (symmetricSubspaceDimensionThreeCopies H : ℚ) =
        ((d : ℚ) * ((d : ℚ) + 1) * ((d : ℚ) + 2)) / 6 := by
  sorry

end

end QITBench.DimensionSymmetricSubspaceThreeCopies
