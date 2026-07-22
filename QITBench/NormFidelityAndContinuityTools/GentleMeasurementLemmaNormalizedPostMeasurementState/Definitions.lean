module

public import QITBench.Base

/-!
# Gentle Measurement Lemma for the Normalized Post-Measurement State

The input density operator is a `State`; the measurement effect is represented
as a positive matrix bounded above by the identity. The square root and trace
norm are concrete finite-dimensional matrix-CFC constructions.
-/

@[expose] public section

namespace QITBench.GentleMeasurementLemmaNormalizedPostMeasurementState

open scoped ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  CFC.sqrt A

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (A.conjTranspose * A)))

def IsPositiveOperator
    {n : ℕ}
    (A : CMatrix (Fin n)) : Prop :=
  A.PosSemidef

def OperatorLe
    {n : ℕ}
    (A B : CMatrix (Fin n)) : Prop :=
  A ≤ B

noncomputable def normalizedPostMeasurementState
    {n : ℕ}
    (rho : State (Fin n))
    (M : CMatrix (Fin n)) : CMatrix (Fin n) :=
  (Matrix.trace (M * rho.matrix))⁻¹ • (matrixSqrt M * rho.matrix * matrixSqrt M)

end

end QITBench.GentleMeasurementLemmaNormalizedPostMeasurementState
