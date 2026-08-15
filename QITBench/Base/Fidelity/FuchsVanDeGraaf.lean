/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity.Uhlmann

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace QITBench.Fidelity

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem traceNorm_sqrt_mul_sqrt_eq_unsquaredFidelity
    (rho sigma : State a) :
    traceNorm (matrixSqrt sigma.matrix * matrixSqrt rho.matrix) =
      (Matrix.trace (matrixSqrt
        (matrixSqrt rho.matrix * sigma.matrix * matrixSqrt rho.matrix))).re := by
  unfold traceNorm
  have hrho : (matrixSqrt rho.matrix).conjTranspose = matrixSqrt rho.matrix := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg rho.matrix).star_eq
  have hsigma : (matrixSqrt sigma.matrix).conjTranspose = matrixSqrt sigma.matrix := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg sigma.matrix).star_eq
  have hsigma_sq : matrixSqrt sigma.matrix * matrixSqrt sigma.matrix = sigma.matrix :=
    CFC.sqrt_mul_sqrt_self sigma.matrix sigma.pos.nonneg
  rw [Matrix.conjTranspose_mul, hrho, hsigma]
  congr 3
  rw [show matrixSqrt rho.matrix * matrixSqrt sigma.matrix *
      (matrixSqrt sigma.matrix * matrixSqrt rho.matrix) =
      matrixSqrt rho.matrix * (matrixSqrt sigma.matrix * matrixSqrt sigma.matrix) *
        matrixSqrt rho.matrix by noncomm_ring, hsigma_sq]

private theorem trace_product_posSemidef_re_nonneg
    (A B : CMatrix a) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let S : CMatrix a := matrixSqrt A
  have hSstar : S.conjTranspose = S := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg A).star_eq
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hconj : (S * B * S.conjTranspose).PosSemidef := hB.mul_mul_conjTranspose_same S
  have htrace : 0 ≤ (S * B * S.conjTranspose).trace := hconj.trace_nonneg
  have hre : 0 ≤ (S * B * S.conjTranspose).trace.re :=
    (Complex.nonneg_iff.mp htrace).1
  rw [hSstar, Matrix.trace_mul_cycle, hSS] at hre
  exact hre

private theorem trace_sqrtEffect_mul_sqrtState_sq
    (E : CMatrix a) (hE : E.PosSemidef) (tau : State a) :
    (((matrixSqrt E * matrixSqrt tau.matrix) *
        (matrixSqrt E * matrixSqrt tau.matrix).conjTranspose).trace).re =
      (E * tau.matrix).trace.re := by
  have hEherm : (matrixSqrt E).conjTranspose = matrixSqrt E := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg E).star_eq
  have htauherm : (matrixSqrt tau.matrix).conjTranspose = matrixSqrt tau.matrix := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg tau.matrix).star_eq
  have hEsq : matrixSqrt E * matrixSqrt E = E :=
    CFC.sqrt_mul_sqrt_self E hE.nonneg
  have htausq : matrixSqrt tau.matrix * matrixSqrt tau.matrix = tau.matrix :=
    CFC.sqrt_mul_sqrt_self tau.matrix tau.pos.nonneg
  rw [Matrix.conjTranspose_mul, hEherm, htauherm]
  congr 1
  calc
    ((matrixSqrt E * matrixSqrt tau.matrix) *
        (matrixSqrt tau.matrix * matrixSqrt E)).trace =
        (matrixSqrt E * tau.matrix * matrixSqrt E).trace := by
          congr 1
          rw [show (matrixSqrt E * matrixSqrt tau.matrix) *
              (matrixSqrt tau.matrix * matrixSqrt E) =
              matrixSqrt E * (matrixSqrt tau.matrix * matrixSqrt tau.matrix) *
                matrixSqrt E by noncomm_ring, htausq]
    _ = (E * tau.matrix).trace := by
      rw [Matrix.trace_mul_cycle, hEsq]

private theorem abs_trace_sqrtProduct_effect_le
    (rho sigma : State a) (E : CMatrix a) (hE : E.PosSemidef)
    (U : Matrix.unitaryGroup a ℂ) :
    ‖(matrixSqrt rho.matrix * E * matrixSqrt sigma.matrix * (U : CMatrix a)).trace‖ ≤
      Real.sqrt ((E * rho.matrix).trace.re) *
        Real.sqrt ((E * sigma.matrix).trace.re) := by
  letI iSemi : SeminormedAddCommGroup (CMatrix a) :=
    (1 : CMatrix a).toMatrixSeminormedAddCommGroup Matrix.PosSemidef.one
  letI iInner : InnerProductSpace ℂ (CMatrix a) :=
    (1 : CMatrix a).toMatrixInnerProductSpace Matrix.PosSemidef.one
  let A : CMatrix a := matrixSqrt E * matrixSqrt rho.matrix
  let B : CMatrix a := matrixSqrt E * matrixSqrt sigma.matrix * (U : CMatrix a)
  have hinner : inner ℂ A B =
      (matrixSqrt rho.matrix * E * matrixSqrt sigma.matrix * (U : CMatrix a)).trace := by
    show (B * (1 : CMatrix a) * A.conjTranspose).trace = _
    have hEherm : (matrixSqrt E).conjTranspose = matrixSqrt E := by
      rw [← Matrix.star_eq_conjTranspose]
      exact (CFC.sqrt_nonneg E).star_eq
    have hrhoherm : (matrixSqrt rho.matrix).conjTranspose = matrixSqrt rho.matrix := by
      rw [← Matrix.star_eq_conjTranspose]
      exact (CFC.sqrt_nonneg rho.matrix).star_eq
    have hEsq : matrixSqrt E * matrixSqrt E = E :=
      CFC.sqrt_mul_sqrt_self E hE.nonneg
    rw [Matrix.mul_one, Matrix.conjTranspose_mul, hEherm, hrhoherm]
    calc
      (matrixSqrt E * matrixSqrt sigma.matrix * (U : CMatrix a) *
          (matrixSqrt rho.matrix * matrixSqrt E)).trace =
          (matrixSqrt rho.matrix * (matrixSqrt E * matrixSqrt E) *
            matrixSqrt sigma.matrix * (U : CMatrix a)).trace := by
            rw [Matrix.trace_mul_cycle]
            congr 1
            noncomm_ring
      _ = _ := by rw [hEsq]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) A B
  rw [hinner] at hcs
  have hnormA : @norm (CMatrix a) iSemi.toNorm A =
      Real.sqrt ((E * rho.matrix).trace.re) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt (trace_product_posSemidef_re_nonneg E rho.matrix hE rho.pos)]
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (CMatrix a)
      Complex.instRCLike iSemi iInner A]
    change ((A * (1 : CMatrix a) * A.conjTranspose).trace).re = _
    simpa [A] using trace_sqrtEffect_mul_sqrtState_sq E hE rho
  have hnormB : @norm (CMatrix a) iSemi.toNorm B =
      Real.sqrt ((E * sigma.matrix).trace.re) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt (trace_product_posSemidef_re_nonneg E sigma.matrix hE sigma.pos)]
    rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ (CMatrix a)
      Complex.instRCLike iSemi iInner B]
    change ((B * (1 : CMatrix a) * B.conjTranspose).trace).re = _
    have hUU : (U : CMatrix a) * (U : CMatrix a).conjTranspose = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp U.prop
    have hBprod : B * (1 : CMatrix a) * B.conjTranspose =
        (matrixSqrt E * matrixSqrt sigma.matrix) *
          (matrixSqrt E * matrixSqrt sigma.matrix).conjTranspose := by
      simp only [Matrix.mul_one, B]
      rw [Matrix.conjTranspose_mul]
      rw [show matrixSqrt E * matrixSqrt sigma.matrix * (U : CMatrix a) *
          ((U : CMatrix a).conjTranspose *
            (matrixSqrt E * matrixSqrt sigma.matrix).conjTranspose) =
          matrixSqrt E * matrixSqrt sigma.matrix *
            ((U : CMatrix a) * (U : CMatrix a).conjTranspose) *
              (matrixSqrt E * matrixSqrt sigma.matrix).conjTranspose by noncomm_ring,
        hUU, Matrix.mul_one]
    rw [hBprod]
    exact trace_sqrtEffect_mul_sqrtState_sq E hE sigma
  rw [hnormA, hnormB] at hcs
  simpa [mul_comm] using hcs

private theorem traceNorm_sqrtProduct_le_binaryClassicalFidelity
    (rho sigma : State a) (E : CMatrix a)
    (hE : E.PosSemidef) (hEle : E ≤ 1) :
    traceNorm (matrixSqrt rho.matrix * matrixSqrt sigma.matrix) ≤
      Real.sqrt ((E * rho.matrix).trace.re * (E * sigma.matrix).trace.re) +
      Real.sqrt (((1 - E) * rho.matrix).trace.re *
        ((1 - E) * sigma.matrix).trace.re) := by
  classical
  obtain ⟨U, hU⟩ :=
    exists_unitary_abs_trace_eq_traceNorm
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix)
  let W : CMatrix a := (U : CMatrix a)
  let Ec : CMatrix a := 1 - E
  have hEc : Ec.PosSemidef := by simpa [Ec, Matrix.le_iff] using hEle
  have hsplit :
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix * W).trace =
        (matrixSqrt rho.matrix * E * matrixSqrt sigma.matrix * W).trace +
        (matrixSqrt rho.matrix * Ec * matrixSqrt sigma.matrix * W).trace := by
    rw [← Matrix.trace_add]
    congr 1
    simp [Ec, Matrix.mul_sub]
    noncomm_ring
  rw [← hU]
  rw [hsplit]
  calc
    ‖(matrixSqrt rho.matrix * E * matrixSqrt sigma.matrix * W).trace +
        (matrixSqrt rho.matrix * Ec * matrixSqrt sigma.matrix * W).trace‖ ≤
      ‖(matrixSqrt rho.matrix * E * matrixSqrt sigma.matrix * W).trace‖ +
        ‖(matrixSqrt rho.matrix * Ec * matrixSqrt sigma.matrix * W).trace‖ :=
          norm_add_le _ _
    _ ≤ Real.sqrt ((E * rho.matrix).trace.re) *
          Real.sqrt ((E * sigma.matrix).trace.re) +
        (Real.sqrt ((Ec * rho.matrix).trace.re) *
          Real.sqrt ((Ec * sigma.matrix).trace.re)) := by
            exact add_le_add
              (abs_trace_sqrtProduct_effect_le rho sigma E hE U)
              (abs_trace_sqrtProduct_effect_le rho sigma Ec hEc U)
    _ = _ := by
      rw [← Real.sqrt_mul (trace_product_posSemidef_re_nonneg E rho.matrix hE rho.pos),
        ← Real.sqrt_mul (trace_product_posSemidef_re_nonneg Ec rho.matrix hEc rho.pos)]

private theorem powersStoermer_trace_sqrt_product_lower
    (rho sigma : State a) :
    1 - traceDistance rho.matrix sigma.matrix ≤
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix).trace.re := by
  let R := matrixSqrt rho.matrix
  let S := matrixSqrt sigma.matrix
  let H := R - S
  have hH : H.IsHermitian :=
    (CFC.sqrt_nonneg rho.matrix).isSelfAdjoint.sub
      (CFC.sqrt_nonneg sigma.matrix).isSelfAdjoint
  obtain ⟨T, hTminus, hTplus, hscore, hcomm, hpos, hneg⟩ :=
    exists_hermitian_sign_dual hH
  have hRpos : R.PosSemidef := (CFC.sqrt_nonneg rho.matrix).posSemidef
  have hSpos : S.PosSemidef := (CFC.sqrt_nonneg sigma.matrix).posSemidef
  have htrace1 : (((1 + T) * H) * S).trace.re ≥ 0 :=
    trace_product_posSemidef_re_nonneg ((1 + T) * H) S hpos hSpos
  have htrace2 : (((1 - T) * (-H)) * R).trace.re ≥ 0 :=
    trace_product_posSemidef_re_nonneg ((1 - T) * (-H)) R hneg hRpos
  have hcross : (T * (R * S - S * R)).trace = 0 := by
    have hc : T * R - R * T = T * S - S * T := by
      rw [show T * R - R * T = T * (R - S) - (R - S) * T +
          (T * S - S * T) by noncomm_ring, hcomm, sub_self, zero_add]
    calc
      (T * (R * S - S * R)).trace = ((T * R - R * T) * S).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.sub_mul, Matrix.trace_sub]
        rw [Matrix.mul_assoc]
        congr 1
        rw [show (T * (S * R)).trace = (R * T * S).trace by
          rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]]
      _ = ((T * S - S * T) * S).trace := by rw [hc]
      _ = 0 := by
        rw [Matrix.sub_mul, Matrix.trace_sub]
        rw [Matrix.trace_mul_cycle T S S]
        simp
  have hsum :
      ((((1 + T) * H) * S).trace + (((1 - T) * (-H)) * R).trace).re =
        (R * S + S * R - rho.matrix - sigma.matrix +
          T * (rho.matrix - sigma.matrix)).trace.re := by
    have hRR : R * R = rho.matrix := CFC.sqrt_mul_sqrt_self rho.matrix rho.pos.nonneg
    have hSS : S * S = sigma.matrix := CFC.sqrt_mul_sqrt_self sigma.matrix sigma.pos.nonneg
    let A : CMatrix a := ((1 + T) * H) * S
    let B : CMatrix a := ((1 - T) * (-H)) * R
    let C : CMatrix a := R * S + S * R - R * R - S * S + T * (R * R - S * S)
    let K : CMatrix a := T * (R * S - S * R)
    have hmat : A + B = C + K := by
      simp only [A, B, C, K, H]
      noncomm_ring
    calc
      (A.trace + B.trace).re = (A + B).trace.re := by rw [Matrix.trace_add]
      _ = (C + K).trace.re := by rw [hmat]
      _ = (C.trace + K.trace).re := by rw [Matrix.trace_add]
      _ = C.trace.re := by rw [show K.trace = 0 by simpa [K] using hcross]; simp
      _ = (R * S + S * R - rho.matrix - sigma.matrix +
          T * (rho.matrix - sigma.matrix)).trace.re := by
        congr 2
        simp only [C]
        rw [hRR, hSS]
  have hkey : 2 - 2 * (R * S).trace.re ≤
      (T * (rho.matrix - sigma.matrix)).trace.re := by
    have hnon : 0 ≤ ((((1 + T) * H) * S).trace +
        (((1 - T) * (-H)) * R).trace).re := by
      rw [Complex.add_re]
      linarith
    rw [hsum] at hnon
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
      rho.trace_eq_one, sigma.trace_eq_one, Complex.one_re] at hnon
    have hrs : (S * R).trace.re = (R * S).trace.re := by
      rw [Matrix.trace_mul_comm]
    rw [hrs] at hnon
    linarith
  have hdual : (T * (rho.matrix - sigma.matrix)).trace.re ≤
      traceNorm (rho.matrix - sigma.matrix) :=
    re_trace_mul_le_traceNorm (rho.pos.isHermitian.sub sigma.pos.isHermitian)
      hTminus hTplus
  unfold traceDistance
  nlinarith

theorem one_sub_unsquaredFidelity_le_traceDistance
    (rho sigma : State a) :
    1 - (Matrix.trace (matrixSqrt
      (matrixSqrt rho.matrix * sigma.matrix * matrixSqrt rho.matrix))).re ≤
      traceDistance rho.matrix sigma.matrix := by
  have hPS := powersStoermer_trace_sqrt_product_lower rho sigma
  have htrace_le :
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix).trace.re ≤
        traceNorm (matrixSqrt sigma.matrix * matrixSqrt rho.matrix) := by
    calc
      (matrixSqrt rho.matrix * matrixSqrt sigma.matrix).trace.re =
          (matrixSqrt sigma.matrix * matrixSqrt rho.matrix).trace.re := by
        rw [Matrix.trace_mul_comm]
      _ ≤ ‖(matrixSqrt sigma.matrix * matrixSqrt rho.matrix).trace‖ :=
        Complex.re_le_norm _
      _ = ‖((matrixSqrt sigma.matrix * matrixSqrt rho.matrix) *
          (1 : CMatrix a)).trace‖ := by simp
      _ ≤ traceNorm (matrixSqrt sigma.matrix * matrixSqrt rho.matrix) :=
        abs_trace_mul_unitary_le_traceNorm _ (1 : Matrix.unitaryGroup a ℂ)
  have hnorm : traceNorm (matrixSqrt sigma.matrix * matrixSqrt rho.matrix) =
      (Matrix.trace (matrixSqrt
        (matrixSqrt rho.matrix * sigma.matrix * matrixSqrt rho.matrix))).re := by
    exact traceNorm_sqrt_mul_sqrt_eq_unsquaredFidelity rho sigma
  rw [hnorm] at htrace_le
  linarith

theorem traceDistance_le_sqrt_one_sub_unsquaredFidelity_sq
    (rho sigma : State a) :
    traceDistance rho.matrix sigma.matrix ≤
      Real.sqrt (1 -
        (Matrix.trace (matrixSqrt
          (matrixSqrt rho.matrix * sigma.matrix * matrixSqrt rho.matrix))).re ^ 2) := by
  classical
  obtain ⟨phi, hphi, hoverlap⟩ :=
    exists_canonicalPurification_overlapSq_eq_fidelitySq sigma rho
  let psi : PureVector (a × a) := canonicalPurification sigma
  have hpsi : psi.state.marginalA = sigma := by
    simpa [psi] using canonicalPurification_marginalA sigma
  calc
    traceDistance rho.matrix sigma.matrix = traceDistance sigma.matrix rho.matrix := by
      have hneg (M : CMatrix a) : traceNorm (-M) = traceNorm M := by
        simp [traceNorm]
      unfold traceDistance
      rw [show sigma.matrix - rho.matrix = -(rho.matrix - sigma.matrix) by abel,
        hneg]
    _ = traceDistance psi.state.marginalA.matrix phi.state.marginalA.matrix := by
      rw [hpsi, hphi]
    _ ≤ traceDistance psi.state.matrix phi.state.matrix :=
      traceDistance_partialTraceB_mono psi.state phi.state
    _ ≤ Real.sqrt (1 - pureOverlapSq psi phi) :=
      pureState_traceDistance_le_sqrt_one_sub_overlapSq psi phi
    _ = Real.sqrt (1 -
        (Matrix.trace (matrixSqrt
          (matrixSqrt rho.matrix * sigma.matrix * matrixSqrt rho.matrix))).re ^ 2) := by
      rw [show pureOverlapSq psi phi =
          traceNorm (matrixSqrt sigma.matrix * matrixSqrt rho.matrix) ^ 2 from hoverlap]
      rw [traceNorm_sqrt_mul_sqrt_eq_unsquaredFidelity]

end

end QITBench.Fidelity
