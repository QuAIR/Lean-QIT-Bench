/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.States.PosSqrt
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

noncomputable local instance cMatrixCStarAlgebraForDistanceContinuity {ι : Type u}
    [Fintype ι] [DecidableEq ι] :
    CStarAlgebra (Matrix ι ι ℂ) where

def traceNorm (M : CMatrix a) : ℝ :=
  (psdSqrt (Mᴴ * M)).trace.re

@[simp]
theorem psdSqrt_zero : psdSqrt (0 : CMatrix a) = 0 := by
  simp [psdSqrt]

theorem traceNorm_nonneg (M : CMatrix a) : 0 ≤ traceNorm M := by
  rw [traceNorm]
  have h : 0 ≤ (psdSqrt (Matrix.conjTranspose M * M)).trace :=
    Matrix.PosSemidef.trace_nonneg (psdSqrt_pos (Matrix.conjTranspose M * M))
  have hre := (Complex.nonneg_iff.mp h).1
  simpa using hre

theorem traceNorm_posSemidef_eq_trace_re
    (A : CMatrix a) (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  rw [traceNorm]
  have hherm : Matrix.conjTranspose A = A := hA.isHermitian.eq
  have hsqrt : psdSqrt (Matrix.conjTranspose A * A) = A := by
    rw [hherm]
    simpa [psdSqrt, sq] using (CFC.sqrt_sq A hA.nonneg)
  rw [hsqrt]

@[simp]
theorem traceNorm_zero : traceNorm (0 : CMatrix a) = 0 := by
  simp [traceNorm]

@[simp]
theorem traceNorm_neg (M : CMatrix a) : traceNorm (-M) = traceNorm M := by
  simp [traceNorm]

def traceNormDistance (M N : CMatrix a) : ℝ :=
  traceNorm (M - N)

def normalizedTraceDistance (M N : CMatrix a) : ℝ :=
  (1 / 2 : ℝ) * traceNormDistance M N

@[simp]
theorem traceNormDistance_eq_traceNorm_sub (M N : CMatrix a) :
    traceNormDistance M N = traceNorm (M - N) :=
  rfl

theorem traceNormDistance_nonneg (M N : CMatrix a) : 0 ≤ traceNormDistance M N :=
  traceNorm_nonneg (M - N)

@[simp]
theorem traceNormDistance_self (M : CMatrix a) : traceNormDistance M M = 0 := by
  simp [traceNormDistance]

theorem traceNormDistance_comm (M N : CMatrix a) :
    traceNormDistance M N = traceNormDistance N M := by
  calc
    traceNormDistance M N = traceNorm (M - N) := rfl
    _ = traceNorm (-(M - N)) := by rw [traceNorm_neg]
    _ = traceNormDistance N M := by simp [traceNormDistance, sub_eq_add_neg]

@[simp]
theorem normalizedTraceDistance_eq (M N : CMatrix a) :
    normalizedTraceDistance M N = (1 / 2 : ℝ) * traceNormDistance M N :=
  rfl

theorem normalizedTraceDistance_nonneg (M N : CMatrix a) :
    0 ≤ normalizedTraceDistance M N :=
  mul_nonneg (by norm_num) (traceNormDistance_nonneg M N)

@[simp]
theorem normalizedTraceDistance_self (M : CMatrix a) :
    normalizedTraceDistance M M = 0 := by
  simp [normalizedTraceDistance]

theorem normalizedTraceDistance_comm (M N : CMatrix a) :
    normalizedTraceDistance M N = normalizedTraceDistance N M := by
  rw [normalizedTraceDistance, normalizedTraceDistance, traceNormDistance_comm]

omit [Fintype a] [DecidableEq a] in
private theorem decouplingTraceNorm_continuous [Fintype a] [DecidableEq a] :
    Continuous (traceNorm : CMatrix a → ℝ) := by
  have hgram : Continuous (fun M : CMatrix a => star M * M) := by
    exact (Continuous.star continuous_id).matrix_mul continuous_id
  have hnonneg : ∀ M : CMatrix a, (star M * M) ∈ {A : CMatrix a | 0 ≤ A} := by
    intro M
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.posSemidef_conjTranspose_mul_self M)
  have hsqrtOn :
      ContinuousOn (CFC.sqrt : CMatrix a → CMatrix a) {A : CMatrix a | 0 ≤ A} := by
    exact CFC.continuousOn_sqrt
  have hsqrt : Continuous (fun M : CMatrix a => CFC.sqrt (star M * M)) := by
    exact hsqrtOn.comp_continuous hgram hnonneg
  have htrace : Continuous (fun M : CMatrix a => (CFC.sqrt (star M * M)).trace) :=
    Continuous.matrix_trace hsqrt
  simpa [traceNorm, psdSqrt] using Complex.continuous_re.comp htrace

omit [Fintype a] [DecidableEq a] in

theorem traceNorm_continuous [Fintype a] [DecidableEq a] :
    Continuous (traceNorm : CMatrix a → ℝ) :=
  decouplingTraceNorm_continuous

namespace State

def traceNormDistance (rho sigma : State a) : ℝ :=
  QITBench.traceNormDistance rho.matrix sigma.matrix

def normalizedTraceDistance (rho sigma : State a) : ℝ :=
  QITBench.normalizedTraceDistance rho.matrix sigma.matrix

@[simp]
theorem traceNormDistance_eq_matrix (rho sigma : State a) :
    rho.traceNormDistance sigma = QITBench.traceNormDistance rho.matrix sigma.matrix :=
  rfl

theorem traceNormDistance_nonneg (rho sigma : State a) :
    0 ≤ rho.traceNormDistance sigma :=
  QITBench.traceNormDistance_nonneg rho.matrix sigma.matrix

@[simp]
theorem traceNormDistance_self (rho : State a) : rho.traceNormDistance rho = 0 := by
  simp [State.traceNormDistance]

theorem traceNormDistance_comm (rho sigma : State a) :
    rho.traceNormDistance sigma = sigma.traceNormDistance rho :=
  QITBench.traceNormDistance_comm rho.matrix sigma.matrix

@[simp]
theorem normalizedTraceDistance_eq_matrix (rho sigma : State a) :
    rho.normalizedTraceDistance sigma =
      QITBench.normalizedTraceDistance rho.matrix sigma.matrix :=
  rfl

theorem normalizedTraceDistance_nonneg (rho sigma : State a) :
    0 ≤ rho.normalizedTraceDistance sigma :=
  QITBench.normalizedTraceDistance_nonneg rho.matrix sigma.matrix

@[simp]
theorem normalizedTraceDistance_self (rho : State a) :
    rho.normalizedTraceDistance rho = 0 := by
  simp [State.normalizedTraceDistance]

theorem normalizedTraceDistance_comm (rho sigma : State a) :
    rho.normalizedTraceDistance sigma = sigma.normalizedTraceDistance rho :=
  QITBench.normalizedTraceDistance_comm rho.matrix sigma.matrix

end State

end

end QITBench
