module

public import QITBench.NormFidelityAndContinuityTools.GentleMeasurementLemmaNormalizedPostMeasurementState.Definitions

@[expose] public section

namespace QITBench.GentleMeasurementLemmaNormalizedPostMeasurementState

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n : ℕ}
    (rho : State (Fin n))
    (M : CMatrix (Fin n))
    (epsilon : ℝ)
    (hM_pos : IsPositiveOperator M)
    (hM_le_one : OperatorLe M 1)
    (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hprob : 1 - epsilon ≤ Complex.re (Matrix.trace (M * rho.matrix))) :
    traceNorm (normalizedPostMeasurementState rho M - rho.matrix) ≤
      2 * Real.sqrt epsilon + epsilon := by
  sorry

end

end QITBench.GentleMeasurementLemmaNormalizedPostMeasurementState
