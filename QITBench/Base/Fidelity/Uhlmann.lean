/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity.Purification
public import QITBench.Base.Fidelity.Pure
public import QITBench.Base.Fidelity.TraceNormVariational
public import QITBench.Base.Fidelity.TraceDistance

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace QITBench.Fidelity

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

def amplitudeMatrix (psi : a × a → ℂ) : CMatrix a :=
  fun i j => psi (i, j)

def applyReferenceUnitaryAmp (U : Matrix.unitaryGroup a ℂ)
    (psi : a × a → ℂ) : a × a → ℂ :=
  fun ij => ∑ k, psi (ij.1, k) * (U : CMatrix a) k ij.2

private theorem partialTraceB_rankOne_eq_amplitudeMatrix_mul_conjTranspose
    (psi : a × a → ℂ) :
    partialTraceB (rankOneMatrix psi) =
      amplitudeMatrix psi * (amplitudeMatrix psi)ᴴ := by
  ext i i'
  simp [partialTraceB, amplitudeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem partialTraceB_rankOne_applyReferenceUnitaryAmp
    (U : Matrix.unitaryGroup a ℂ) (psi : a × a → ℂ) :
    partialTraceB (rankOneMatrix (applyReferenceUnitaryAmp U psi)) =
      partialTraceB (rankOneMatrix psi) := by
  let A : CMatrix a := amplitudeMatrix psi
  have hamp : amplitudeMatrix (applyReferenceUnitaryAmp U psi) = A * (U : CMatrix a) := by
    ext i j
    rfl
  have hUU : (U : CMatrix a) * (U : CMatrix a)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.prop
  rw [partialTraceB_rankOne_eq_amplitudeMatrix_mul_conjTranspose,
    partialTraceB_rankOne_eq_amplitudeMatrix_mul_conjTranspose, hamp,
    Matrix.conjTranspose_mul]
  calc
    (A * (U : CMatrix a)) * ((U : CMatrix a)ᴴ * Aᴴ) =
        A * ((U : CMatrix a) * (U : CMatrix a)ᴴ) * Aᴴ := by
          simp only [Matrix.mul_assoc]
    _ = A * Aᴴ := by rw [hUU, Matrix.mul_one]

def applyReferenceUnitary (U : Matrix.unitaryGroup a ℂ)
    (psi : PureVector (a × a)) : PureVector (a × a) where
  amp := applyReferenceUnitaryAmp U psi.amp
  trace_rankOne_eq_one := by
    calc
      (rankOneMatrix (applyReferenceUnitaryAmp U psi.amp)).trace =
          (partialTraceB (rankOneMatrix (applyReferenceUnitaryAmp U psi.amp))).trace :=
        (partialTraceB_trace _).symm
      _ = (partialTraceB (rankOneMatrix psi.amp)).trace := by
        rw [partialTraceB_rankOne_applyReferenceUnitaryAmp]
      _ = (rankOneMatrix psi.amp).trace := partialTraceB_trace _
      _ = 1 := psi.trace_rankOne_eq_one

theorem applyReferenceUnitary_marginalA
    (U : Matrix.unitaryGroup a ℂ) (psi : PureVector (a × a)) :
    (applyReferenceUnitary U psi).state.marginalA = psi.state.marginalA := by
  apply State.ext
  exact partialTraceB_rankOne_applyReferenceUnitaryAmp U psi.amp

theorem canonicalPurification_overlap_applyReferenceUnitary_eq_trace
    (rho sigma : State a) (U : Matrix.unitaryGroup a ℂ) :
    (∑ x, star ((canonicalPurification rho).amp x) *
        (applyReferenceUnitary U (canonicalPurification sigma)).amp x) =
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix * (U : CMatrix a)).trace := by
  classical
  change (∑ x : a × a, star (matrixSqrt rho.matrix x.1 x.2) *
      (∑ k, matrixSqrt sigma.matrix x.1 k * (U : CMatrix a) k x.2)) = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp only [Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  simp only [map_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  congr 1
  funext k
  rw [Finset.mul_sum]
  congr 1
  funext j
  have h := congrFun (congrFun (CFC.sqrt_nonneg rho.matrix).star_eq i) k
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun z => z * matrixSqrt sigma.matrix k j * (U : CMatrix a) j i) h

theorem exists_canonicalPurification_overlapSq_eq_fidelitySq
    (rho sigma : State a) :
    ∃ phi : PureVector (a × a),
      phi.state.marginalA = sigma ∧
      pureOverlapSq (canonicalPurification rho) phi =
        traceNorm (matrixSqrt rho.matrix * matrixSqrt sigma.matrix) ^ 2 := by
  classical
  obtain ⟨U, hU⟩ :=
    exists_unitary_abs_trace_eq_traceNorm
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix)
  refine ⟨applyReferenceUnitary U (canonicalPurification sigma), ?_, ?_⟩
  · rw [applyReferenceUnitary_marginalA, canonicalPurification_marginalA]
  · rw [pureOverlapSq, canonicalPurification_overlap_applyReferenceUnitary_eq_trace]
    rw [Complex.normSq_eq_norm_sq, hU]

end

end QITBench.Fidelity
