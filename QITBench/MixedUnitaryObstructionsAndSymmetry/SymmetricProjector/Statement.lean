module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.SymmetricProjector.Definitions
@[expose] public section

namespace QITBench.SymmetricProjector

open scoped BigOperators

noncomputable section

theorem main
    {d n : ℕ}
    {H V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (_hdim : Module.finrank ℂ H = d)
    (_simpleTensor : (Fin n → H) → V)
    (W : Equiv.Perm (Fin n) → V →ₗ[ℂ] V)
    (_hW_action : IsPermutationRepresentation _simpleTensor W)
    (hW_representation : IsGroupRepresentation W)
    (hW_unitary : IsUnitaryRepresentation W) :
    IsOrthogonalProjector (symmetricProjector n V W) := by
  sorry

end

end QITBench.SymmetricProjector
