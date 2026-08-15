/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity.TraceNormSpectral
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace QITBench.Fidelity

noncomputable section

variable {a : Type*} [Fintype a] [DecidableEq a]

private theorem trace_diagonal_mul_eq_sum (d : a → ℂ) (U : CMatrix a) :
    (Matrix.diagonal d * U).trace = ∑ i, d i * U i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

private theorem posSemidef_trace_mul_unitary_abs_le_trace_re
    (P : CMatrix a) (hP : P.PosSemidef) (U : Matrix.unitaryGroup a ℂ) :
    ‖(P * (U : CMatrix a)).trace‖ ≤ P.trace.re := by
  classical
  let E : Matrix.unitaryGroup a ℂ := hP.isHermitian.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal
    (fun i => ((hP.isHermitian.eigenvalues i : ℝ) : ℂ))
  let U' : Matrix.unitaryGroup a ℂ := E⁻¹ * U * E
  have hPdiag : P = (E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [E, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using hP.isHermitian.spectral_theorem
  have htrace : (P * (U : CMatrix a)).trace = (D * (U' : CMatrix a)).trace := by
    calc
      (P * (U : CMatrix a)).trace =
          (((E : CMatrix a) * D * (E⁻¹ : Matrix.unitaryGroup a ℂ)) * U).trace := by
            rw [hPdiag]
      _ = ((E : CMatrix a) * D * ((E⁻¹ : Matrix.unitaryGroup a ℂ) * U)).trace := by
            simp [Matrix.mul_assoc]
      _ = (((E⁻¹ : Matrix.unitaryGroup a ℂ) * U) * (E : CMatrix a) * D).trace := by
            rw [Matrix.trace_mul_cycle]
      _ = (D * (U' : CMatrix a)).trace := by
            rw [Matrix.trace_mul_comm]
            simp [U', Matrix.mul_assoc]
  have hdiag : (D * (U' : CMatrix a)).trace =
      ∑ i, ((hP.isHermitian.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i := by
    simpa [D] using trace_diagonal_mul_eq_sum
      (fun i => ((hP.isHermitian.eigenvalues i : ℝ) : ℂ)) (U' : CMatrix a)
  rw [htrace, hdiag]
  calc
    ‖∑ i, ((hP.isHermitian.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ ≤
        ∑ i, ‖((hP.isHermitian.eigenvalues i : ℝ) : ℂ) * (U' : CMatrix a) i i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, hP.isHermitian.eigenvalues i := by
      exact Finset.sum_le_sum fun i _ => by
        have hi : ‖(U' : CMatrix a) i i‖ ≤ (1 : ℝ) :=
          entry_norm_bound_of_unitary U'.prop i i
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hP.eigenvalues_nonneg i)]
        simpa using mul_le_mul_of_nonneg_left hi (hP.eigenvalues_nonneg i)
    _ = P.trace.re := by
      have ht := hP.isHermitian.trace_eq_sum_eigenvalues
      exact ((congrArg Complex.re ht).trans (by simp)).symm

private theorem adjoint_inner_adjoint_of_comp_adjoint_eq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {T₁ T₂ : E →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) (y z : F) :
    inner ℂ (T₁.adjoint y) (T₁.adjoint z) =
      inner ℂ (T₂.adjoint y) (T₂.adjoint z) := by
  calc
    inner ℂ (T₁.adjoint y) (T₁.adjoint z) = inner ℂ y (T₁ (T₁.adjoint z)) := by
      rw [LinearMap.adjoint_inner_left]
    _ = inner ℂ y ((T₁.comp T₁.adjoint) z) := rfl
    _ = inner ℂ y ((T₂.comp T₂.adjoint) z) := by rw [hGram]
    _ = inner ℂ y (T₂ (T₂.adjoint z)) := rfl
    _ = inner ℂ (T₂.adjoint y) (T₂.adjoint z) := by
      rw [LinearMap.adjoint_inner_left]

private theorem ker_adjoint_eq_of_comp_adjoint_eq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {T₁ T₂ : E →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.ker T₁.adjoint = LinearMap.ker T₂.adjoint := by
  calc
    LinearMap.ker T₁.adjoint = LinearMap.ker (T₁.comp T₁.adjoint) := by
      rw [LinearMap.ker_self_comp_adjoint]
    _ = LinearMap.ker (T₂.comp T₂.adjoint) := by rw [hGram]
    _ = LinearMap.ker T₂.adjoint := by
      rw [LinearMap.ker_self_comp_adjoint]

private def adjointRangeMap
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {T₁ T₂ : E →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.range T₁.adjoint →ₗ[ℂ] LinearMap.range T₂.adjoint where
  toFun x := ⟨T₂.adjoint (Classical.choose x.property),
    LinearMap.mem_range_self T₂.adjoint (Classical.choose x.property)⟩
  map_add' x y := by
    apply Subtype.ext
    let sx : F := Classical.choose x.property
    let sy : F := Classical.choose y.property
    let sxy : F := Classical.choose (x + y).property
    have hsx : T₁.adjoint sx = x := Classical.choose_spec x.property
    have hsy : T₁.adjoint sy = y := Classical.choose_spec y.property
    have hsxy : T₁.adjoint sxy = x + y := Classical.choose_spec (x + y).property
    have hker : sxy - (sx + sy) ∈ LinearMap.ker T₁.adjoint := by
      rw [LinearMap.mem_ker]
      simp [hsx, hsy, hsxy]
    have hker₂ : sxy - (sx + sy) ∈ LinearMap.ker T₂.adjoint := by
      rwa [ker_adjoint_eq_of_comp_adjoint_eq hGram] at hker
    have hzero := LinearMap.mem_ker.mp hker₂
    change T₂.adjoint sxy = T₂.adjoint sx + T₂.adjoint sy
    simpa using sub_eq_zero.mp (by simpa using hzero)
  map_smul' c x := by
    apply Subtype.ext
    let sx : F := Classical.choose x.property
    let scx : F := Classical.choose (c • x).property
    have hsx : T₁.adjoint sx = x := Classical.choose_spec x.property
    have hscx : T₁.adjoint scx = c • x := Classical.choose_spec (c • x).property
    have hker : scx - c • sx ∈ LinearMap.ker T₁.adjoint := by
      rw [LinearMap.mem_ker]
      simp [hsx, hscx]
    have hker₂ : scx - c • sx ∈ LinearMap.ker T₂.adjoint := by
      rwa [ker_adjoint_eq_of_comp_adjoint_eq hGram] at hker
    have hzero := LinearMap.mem_ker.mp hker₂
    change T₂.adjoint scx = c • T₂.adjoint sx
    simpa using sub_eq_zero.mp (by simpa using hzero)

private def adjointRangeIsometry
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {T₁ T₂ : E →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.range T₁.adjoint →ₗᵢ[ℂ] LinearMap.range T₂.adjoint :=
  (adjointRangeMap hGram).isometryOfInner <| by
    intro x y
    let sx : F := Classical.choose x.property
    let sy : F := Classical.choose y.property
    have hsx : T₁.adjoint sx = x := Classical.choose_spec x.property
    have hsy : T₁.adjoint sy = y := Classical.choose_spec y.property
    calc
      inner ℂ (adjointRangeMap hGram x) (adjointRangeMap hGram y) =
          inner ℂ (T₂.adjoint sx) (T₂.adjoint sy) := rfl
      _ = inner ℂ (T₁.adjoint sx) (T₁.adjoint sy) :=
        (adjoint_inner_adjoint_of_comp_adjoint_eq hGram sx sy).symm
      _ = inner ℂ x y := by rw [hsx, hsy, Submodule.coe_inner]

private theorem adjointRangeIsometry_apply_adjoint
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {T₁ T₂ : E →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) (y : F) :
    adjointRangeIsometry hGram
        ⟨T₁.adjoint y, LinearMap.mem_range_self T₁.adjoint y⟩ =
      ⟨T₂.adjoint y, LinearMap.mem_range_self T₂.adjoint y⟩ := by
  apply Subtype.ext
  let sy : F := Classical.choose (LinearMap.mem_range_self T₁.adjoint y)
  have hsy : T₁.adjoint sy = T₁.adjoint y :=
    Classical.choose_spec (LinearMap.mem_range_self T₁.adjoint y)
  have hker : sy - y ∈ LinearMap.ker T₁.adjoint := by
    rw [LinearMap.mem_ker]
    simp [hsy]
  have hker₂ : sy - y ∈ LinearMap.ker T₂.adjoint := by
    rwa [ker_adjoint_eq_of_comp_adjoint_eq hGram] at hker
  have hzero := LinearMap.mem_ker.mp hker₂
  change T₂.adjoint sy = T₂.adjoint y
  exact sub_eq_zero.mp (by simpa using hzero)

private theorem exists_unitary_right_factor (A B : CMatrix a)
    (hGram : A * Aᴴ = B * Bᴴ) :
    ∃ W : Matrix.unitaryGroup a ℂ, B = A * (W : CMatrix a) := by
  classical
  let T₁ : EuclideanSpace ℂ a →ₗ[ℂ] EuclideanSpace ℂ a := A.toEuclideanLin
  let T₂ : EuclideanSpace ℂ a →ₗ[ℂ] EuclideanSpace ℂ a := B.toEuclideanLin
  have hGramLin : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint := by
    dsimp [T₁, T₂]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_mul] using
      congrArg Matrix.toEuclideanLin hGram
  let L : LinearMap.range T₁.adjoint →ₗᵢ[ℂ] EuclideanSpace ℂ a :=
    (LinearMap.range T₂.adjoint).subtypeₗᵢ.comp (adjointRangeIsometry hGramLin)
  let V : EuclideanSpace ℂ a →ₗᵢ[ℂ] EuclideanSpace ℂ a := L.extend
  have hVadj (y : EuclideanSpace ℂ a) : V (T₁.adjoint y) = T₂.adjoint y := by
    have hext := LinearIsometry.extend_apply L
      ⟨T₁.adjoint y, LinearMap.mem_range_self T₁.adjoint y⟩
    simpa [V, L, adjointRangeIsometry_apply_adjoint] using hext
  let N : CMatrix a := Matrix.toEuclideanLin.symm V.toLinearMap
  have hNlin : N.toEuclideanLin = V.toLinearMap := by simp [N]
  have hNstarN : Nᴴ * N = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hNlin]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_one] using V.adjoint_comp_self'
  let W : Matrix.unitaryGroup a ℂ := ⟨Nᴴ, by
    rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact hNstarN⟩
  refine ⟨W, ?_⟩
  have hlinear : N.toEuclideanLin.comp T₁.adjoint = T₂.adjoint := by
    apply LinearMap.ext
    intro y
    simpa [hNlin] using hVadj y
  have hadj := congrArg LinearMap.adjoint hlinear
  apply Matrix.toEuclideanLin.injective
  simpa [W, T₁, T₂, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.toEuclideanLin, Matrix.toLpLin_mul] using hadj.symm

theorem exists_unitary_abs_trace_eq_traceNorm (M : CMatrix a) :
    ∃ U : Matrix.unitaryGroup a ℂ,
      ‖(M * (U : CMatrix a)).trace‖ = traceNorm M := by
  classical
  let P : CMatrix a := matrixSqrt (Mᴴ * M)
  have hPherm : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg (Mᴴ * M)).star_eq
  have hPsq : P * P = Mᴴ * M :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hPherm, hPsq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨U, hU⟩ := exists_unitary_right_factor P Mᴴ hGram
  refine ⟨U, ?_⟩
  have hM : M = (U : CMatrix a)ᴴ * P := by
    have h := congrArg Matrix.conjTranspose hU
    simpa [hPherm, Matrix.conjTranspose_mul] using h
  have htrace : (M * (U : CMatrix a)).trace = P.trace := by
    calc
      (M * (U : CMatrix a)).trace = ((U : CMatrix a)ᴴ * P * (U : CMatrix a)).trace := by
        rw [hM]
      _ = ((U : CMatrix a) * (U : CMatrix a)ᴴ * P).trace := by
        rw [Matrix.trace_mul_cycle]
      _ = P.trace := by
        have hUU : (U : CMatrix a) * (U : CMatrix a)ᴴ = 1 := by
          rw [← Matrix.star_eq_conjTranspose]
          exact Matrix.mem_unitaryGroup_iff.mp U.prop
        rw [hUU, Matrix.one_mul]
  rw [htrace]
  have hPnonneg : 0 ≤ P.trace :=
    Matrix.PosSemidef.trace_nonneg (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  have hnorm : ‖P.trace‖ = P.trace.re := by
    have hcoe := Complex.eq_coe_norm_of_nonneg hPnonneg
    exact (congrArg Complex.re hcoe).symm.trans (by simp)
  simpa [traceNorm, P] using hnorm

theorem abs_trace_mul_unitary_le_traceNorm
    (M : CMatrix a) (U : Matrix.unitaryGroup a ℂ) :
    ‖(M * (U : CMatrix a)).trace‖ ≤ traceNorm M := by
  classical
  let P : CMatrix a := matrixSqrt (Mᴴ * M)
  have hPherm : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (CFC.sqrt_nonneg (Mᴴ * M)).star_eq
  have hPsq : P * P = Mᴴ * M :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hGram : P * Pᴴ = Mᴴ * (Mᴴ)ᴴ := by
    rw [hPherm, hPsq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨Q, hQ⟩ := exists_unitary_right_factor P Mᴴ hGram
  have hM : M = (Q : CMatrix a)ᴴ * P := by
    have h := congrArg Matrix.conjTranspose hQ
    simpa [hPherm, Matrix.conjTranspose_mul] using h
  let Z : Matrix.unitaryGroup a ℂ := U * Q⁻¹
  have htrace : (M * (U : CMatrix a)).trace = (P * (Z : CMatrix a)).trace := by
    calc
      (M * (U : CMatrix a)).trace = ((Q : CMatrix a)ᴴ * P * (U : CMatrix a)).trace := by
        rw [hM]
      _ = (P * ((U : CMatrix a) * (Q : CMatrix a)ᴴ)).trace := by
        calc
          ((Q : CMatrix a)ᴴ * P * (U : CMatrix a)).trace =
          ((U : CMatrix a) * (Q : CMatrix a)ᴴ * P).trace :=
            Matrix.trace_mul_cycle _ _ _
          _ = (P * ((U : CMatrix a) * (Q : CMatrix a)ᴴ)).trace := by
            calc
              ((U : CMatrix a) * (Q : CMatrix a)ᴴ * P).trace =
                  (P * ((U : CMatrix a) * (Q : CMatrix a)ᴴ)).trace :=
                Matrix.trace_mul_comm _ _
      _ = (P * (Z : CMatrix a)).trace := by
        simp [Z, Matrix.star_eq_conjTranspose]
  have hPpos : P.PosSemidef := (CFC.sqrt_nonneg (Mᴴ * M)).posSemidef
  rw [htrace]
  calc
    ‖(P * (Z : CMatrix a)).trace‖ ≤ P.trace.re :=
      posSemidef_trace_mul_unitary_abs_le_trace_re P hPpos Z
    _ = traceNorm M := by rfl

theorem traceNorm_add_le (A B : CMatrix a) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  classical
  obtain ⟨U, hU⟩ := exists_unitary_abs_trace_eq_traceNorm (A + B)
  rw [← hU]
  rw [Matrix.add_mul, Matrix.trace_add]
  calc
    ‖(A * (U : CMatrix a)).trace + (B * (U : CMatrix a)).trace‖ ≤
        ‖(A * (U : CMatrix a)).trace‖ + ‖(B * (U : CMatrix a)).trace‖ :=
      norm_add_le _ _
    _ ≤ traceNorm A + traceNorm B := add_le_add
      (abs_trace_mul_unitary_le_traceNorm A U)
      (abs_trace_mul_unitary_le_traceNorm B U)

theorem traceNorm_nonneg (M : CMatrix a) : 0 ≤ traceNorm M := by
  obtain ⟨U, hU⟩ := exists_unitary_abs_trace_eq_traceNorm M
  rw [← hU]
  exact norm_nonneg _

theorem traceNorm_neg (M : CMatrix a) : traceNorm (-M) = traceNorm M := by
  unfold traceNorm
  simp

theorem traceNorm_real_smul_eq {c : ℝ} (hc : 0 ≤ c) (M : CMatrix a) :
    traceNorm (((c : ℂ) • M)) = c * traceNorm M := by
  by_cases hz : c = 0
  · subst c
    simp only [Complex.ofReal_zero, zero_smul, zero_mul]
    have hzero : traceNorm (0 : CMatrix a) = 0 := by
      unfold traceNorm matrixSqrt
      simp [CFC.sqrt_zero]
    exact hzero
  · obtain ⟨U, hU⟩ := exists_unitary_abs_trace_eq_traceNorm (((c : ℂ) • M))
    apply le_antisymm
    · rw [← hU, Matrix.smul_mul, Matrix.trace_smul]
      change ‖(c : ℂ) * (M * (U : CMatrix a)).trace‖ ≤ c * traceNorm M
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (abs_trace_mul_unitary_le_traceNorm M U) hc
    · obtain ⟨V, hV⟩ := exists_unitary_abs_trace_eq_traceNorm M
      have hbound := abs_trace_mul_unitary_le_traceNorm (((c : ℂ) • M)) V
      rw [Matrix.smul_mul, Matrix.trace_smul] at hbound
      change ‖(c : ℂ) * (M * (V : CMatrix a)).trace‖ ≤
        traceNorm (((c : ℂ) • M)) at hbound
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, hV] at hbound
      exact hbound

end

end QITBench.Fidelity
