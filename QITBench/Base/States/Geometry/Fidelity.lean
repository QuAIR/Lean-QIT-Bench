/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.States.TraceNorm.Distance

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

def State.fidelity (ρ σ : State a) : ℝ :=
  traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix)

@[simp]
theorem State.fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix (ρ σ : State a) :
    ρ.fidelity σ = traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) :=
  rfl

theorem State.fidelity_nonneg (ρ σ : State a) : 0 ≤ ρ.fidelity σ :=
  traceNorm_nonneg (ρ.sqrtMatrix * σ.sqrtMatrix)

def State.squaredFidelity (ρ σ : State a) : ℝ :=
  (ρ.fidelity σ) ^ 2

@[simp]
theorem State.squaredFidelity_eq_fidelity_sq (ρ σ : State a) :
    ρ.squaredFidelity σ = (ρ.fidelity σ) ^ 2 :=
  rfl

theorem State.squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq (ρ σ : State a) :
    ρ.squaredFidelity σ = (traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix)) ^ 2 :=
  rfl

theorem State.squaredFidelity_nonneg (ρ σ : State a) : 0 ≤ ρ.squaredFidelity σ :=
  sq_nonneg (ρ.fidelity σ)

@[simp]
theorem State.fidelity_self_eq_traceNorm_matrix (ρ : State a) :
    ρ.fidelity ρ = traceNorm ρ.matrix := by
  simp [State.fidelity]

@[simp]
theorem State.squaredFidelity_self_eq_traceNorm_matrix_sq (ρ : State a) :
    ρ.squaredFidelity ρ = (traceNorm ρ.matrix) ^ 2 := by
  simp [State.squaredFidelity]

end

end QITBench
