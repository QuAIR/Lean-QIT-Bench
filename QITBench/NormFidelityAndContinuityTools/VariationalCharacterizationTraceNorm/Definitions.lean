/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.VariationalCharacterizationTraceNorm

open scoped ComplexOrder MatrixOrder

noncomputable section

def IsUnitaryMatrix
    {n : ℕ}
    (U : CMatrix (Fin n)) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  CFC.sqrt A

noncomputable def matrixAbs
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  matrixSqrt (A.conjTranspose * A)

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixAbs A))

noncomputable def unitaryTraceValues
    {n : ℕ}
    (A : CMatrix (Fin n)) : Set ℝ :=
  {x | ∃ U : CMatrix (Fin n),
    IsUnitaryMatrix U ∧ x = ‖Matrix.trace (A * U)‖}

end

end QITBench.VariationalCharacterizationTraceNorm
