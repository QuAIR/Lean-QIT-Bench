module

public import QITBench.NormFidelityAndContinuityTools.VariationalCharacterizationTraceNorm.Definitions

@[expose] public section

namespace QITBench.VariationalCharacterizationTraceNorm

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n : ℕ}
    (rho sigma : State (Fin n)) :
    IsGreatest (unitaryTraceValues (rho.matrix - sigma.matrix))
      (traceNorm (rho.matrix - sigma.matrix)) := by
  sorry

end

end QITBench.VariationalCharacterizationTraceNorm
