module

public import QITBench.NormFidelityAndContinuityTools.FuchsVanDeGraafInequalities.Definitions

@[expose] public section

namespace QITBench.FuchsVanDeGraafInequalities

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n : ℕ}
    (rho sigma : State (Fin n)) :
    let D := traceDistance rho.matrix sigma.matrix
    let F := unsquaredFidelity rho.matrix sigma.matrix
    1 - F ≤ D ∧ D ≤ Real.sqrt (1 - F ^ 2) := by
  sorry

end

end QITBench.FuchsVanDeGraafInequalities
