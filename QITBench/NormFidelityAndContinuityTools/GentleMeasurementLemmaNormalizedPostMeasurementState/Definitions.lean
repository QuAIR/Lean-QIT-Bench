/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity

@[expose] public section

namespace QITBench.GentleMeasurementLemmaNormalizedPostMeasurementState

open scoped ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  Fidelity.matrixSqrt A

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Fidelity.traceNorm A

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
