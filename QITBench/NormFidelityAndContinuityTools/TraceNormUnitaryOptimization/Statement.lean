module

public import QITBench.NormFidelityAndContinuityTools.TraceNormUnitaryOptimization.Definitions

@[expose] public section

namespace QITBench.TraceNormUnitaryOptimization

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n : ℕ}
    (A U : CMatrix (Fin n))
    (hU : IsUnitaryMatrix U) :
    ‖Matrix.trace (A * U)‖ ≤ traceNorm A := by
  sorry

end

end QITBench.TraceNormUnitaryOptimization
