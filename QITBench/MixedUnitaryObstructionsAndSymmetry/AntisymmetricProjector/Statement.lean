module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.AntisymmetricProjector.Definitions
@[expose] public section

namespace QITBench.AntisymmetricProjector

open scoped BigOperators

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (n : ℕ)
    (W : Equiv.Perm (Fin n) → CMatrix d)
    (sgn : Equiv.Perm (Fin n) → ℂ)
    (hrep : IsSignedPermutationRepresentation n W sgn) :
    IsOrthogonalProjector (antisymmetricProjector n W sgn) := by
  sorry

end

end QITBench.AntisymmetricProjector
