/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Util.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

def psdSqrt (M : CMatrix a) : CMatrix a :=
  CFC.sqrt M

theorem psdSqrt_pos (M : CMatrix a) :
    (psdSqrt M).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)

theorem psdSqrt_isHermitian (M : CMatrix a) :
    (psdSqrt M).IsHermitian :=
  (psdSqrt_pos M).isHermitian

theorem psdSqrt_mul_self_of_posSemidef {M : CMatrix a} (hM : M.PosSemidef) :
    psdSqrt M * psdSqrt M = M := by
  simpa [psdSqrt, sq] using (CFC.sq_sqrt M hM.nonneg)

theorem psdSqrt_real_smul_one {a : Type u} [Fintype a] [DecidableEq a]
    {r : ℝ} (hr : 0 ≤ r) :
    psdSqrt (((r : ℂ) • (1 : CMatrix a))) =
      ((Real.sqrt r : ℝ) : ℂ) • (1 : CMatrix a) := by
  let rr : NNReal := ⟨r, hr⟩
  have hscalar : ((r : ℂ) • (1 : CMatrix a)) = algebraMap NNReal (CMatrix a) rr := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.algebraMap_matrix_apply, rr]
      rfl
    · simp [Matrix.algebraMap_matrix_apply, rr, hij]
  have hsqrt := (CFC.sqrt_algebraMap (A := CMatrix a) (r := rr))
  rw [hscalar]
  rw [show ((Real.sqrt r : ℝ) : ℂ) • (1 : CMatrix a) =
      algebraMap NNReal (CMatrix a) (NNReal.sqrt rr) by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.algebraMap_matrix_apply, rr]
      rw [Real.sqrt, Real.toNNReal_of_nonneg hr]
      rfl
    · simp [Matrix.algebraMap_matrix_apply, hij]]
  simp [psdSqrt] at hsqrt ⊢

theorem psdSqrt_real_smul {a : Type u} [Fintype a] [DecidableEq a]
    {r : ℝ} (hr : 0 ≤ r) {M : CMatrix a} (hM : M.PosSemidef) :
    psdSqrt (((r : ℂ) • M)) =
      ((Real.sqrt r : ℝ) : ℂ) • psdSqrt M := by
  let S : CMatrix a := ((Real.sqrt r : ℝ) : ℂ) • psdSqrt M
  have hSsq : S * S = ((r : ℂ) • M) := by
    dsimp [S]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hr,
      psdSqrt_mul_self_of_posSemidef hM]
  have hSpos : S.PosSemidef := by
    have hscalar : (0 : ℂ) ≤ ((Real.sqrt r : ℝ) : ℂ) := by
      exact_mod_cast Real.sqrt_nonneg r
    exact Matrix.PosSemidef.smul (psdSqrt_pos M) hscalar
  change psdSqrt (((r : ℂ) • M)) = S
  simpa [psdSqrt, S] using
    (CFC.sqrt_unique (a := ((r : ℂ) • M)) (b := S) hSsq hSpos.nonneg)

def psdInvSqrt {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) (hM : M.IsHermitian) : CMatrix a :=
  (hM.eigenvectorUnitary : CMatrix a) *
    Matrix.diagonal (fun i : a =>
      if 0 < hM.eigenvalues i
      then (↑(Real.rpow (hM.eigenvalues i) (-(1:ℝ)/2)) : ℂ)
      else (0 : ℂ)) *
      star (hM.eigenvectorUnitary : CMatrix a)

theorem psdInvSqrt_posSemidef {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) (hM : M.IsHermitian) : (psdInvSqrt M hM).PosSemidef := by
  classical
  unfold psdInvSqrt
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hM.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hM.eigenvalues i
  · simp only [hi, ↓reduceIte]
    exact_mod_cast le_of_lt (Real.rpow_pos_of_pos hi _)
  · simp only [hi, ↓reduceIte]
    exact le_refl (0 : ℂ)

theorem psdInvSqrt_isHermitian {a : Type u} [Fintype a] [DecidableEq a]
    (M : CMatrix a) (hM : M.IsHermitian) : (psdInvSqrt M hM).IsHermitian :=
  (psdInvSqrt_posSemidef M hM).isHermitian

theorem psdInvSqrt_support_eq
    {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian =
      (hM.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i : a =>
          if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0) *
          star (hM.isHermitian.eigenvectorUnitary : CMatrix a) := by
  classical
  let U : CMatrix a := hM.isHermitian.eigenvectorUnitary
  let Λ : CMatrix a := Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i : ℂ))
  let R : CMatrix a := Matrix.diagonal (fun i : a =>
    if 0 < hM.isHermitian.eigenvalues i
    then (↑(Real.rpow (hM.isHermitian.eigenvalues i) (-(1:ℝ)/2)) : ℂ)
    else (0 : ℂ))
  let P : CMatrix a := Matrix.diagonal (fun i =>
    if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0)
  have hspec : M = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hM.isHermitian.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary]
  have hRLR : R * Λ * R = P := by
    show Matrix.diagonal (fun i => if 0 < hM.isHermitian.eigenvalues i
          then ↑(Real.rpow (hM.isHermitian.eigenvalues i) (-(1:ℝ)/2)) else (0:ℂ)) *
        Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i : ℂ)) *
        Matrix.diagonal (fun i => if 0 < hM.isHermitian.eigenvalues i
          then ↑(Real.rpow (hM.isHermitian.eigenvalues i) (-(1:ℝ)/2)) else (0:ℂ)) =
      Matrix.diagonal (fun i => if 0 < hM.isHermitian.eigenvalues i then (1:ℂ) else 0)
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply]
      by_cases hi : 0 < hM.isHermitian.eigenvalues i
      ·
        simp only [hi, ↓reduceIte]
        have hprod : (↑((hM.isHermitian.eigenvalues i) ^ (-(1:ℝ)/2)) : ℂ) *
            ↑(hM.isHermitian.eigenvalues i) *
            ↑((hM.isHermitian.eigenvalues i) ^ (-(1:ℝ)/2)) = 1 := by
          have hreal : (hM.isHermitian.eigenvalues i) ^ (-(1:ℝ)/2) *
              (hM.isHermitian.eigenvalues i) *
              (hM.isHermitian.eigenvalues i) ^ (-(1:ℝ)/2) = 1 := by
            have hsum : (-(1:ℝ)/2) + -(1:ℝ)/2 = -1 := by ring
            rw [mul_right_comm, ← Real.rpow_add hi, hsum,
              Real.rpow_neg (le_of_lt hi), Real.rpow_one, inv_mul_cancel₀ (ne_of_gt hi)]
          exact_mod_cast hreal
        exact hprod
      ·
        have heig_nn : 0 ≤ hM.isHermitian.eigenvalues i := hM.eigenvalues_nonneg i
        have heig_zero : hM.isHermitian.eigenvalues i = 0 := by linarith
        rw [heig_zero]
        simp
    ·
      simp only [Matrix.diagonal_apply, hij, ↓reduceIte]

  have hInvSqrt : psdInvSqrt M hM.isHermitian = U * R * star U := by
    simp only [psdInvSqrt, U, R]

  have h1 : (U * R * star U) * (U * Λ * star U) = U * (R * Λ) * star U := by
    calc (U * R * star U) * (U * Λ * star U)
        = U * R * (star U * U) * Λ * star U := by noncomm_ring
      _ = U * R * 1 * Λ * star U := by rw [hU]
      _ = U * (R * Λ) * star U := by noncomm_ring
  have h2 : (U * (R * Λ) * star U) * (U * R * star U) = U * (R * Λ * R) * star U := by
    calc (U * (R * Λ) * star U) * (U * R * star U)
        = U * (R * Λ) * (star U * U) * R * star U := by noncomm_ring
      _ = U * (R * Λ) * 1 * R * star U := by rw [hU]
      _ = U * (R * Λ * R) * star U := by noncomm_ring

  have key : psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian
      = U * P * star U := by
    simp only [hInvSqrt, hspec, h1, h2, hRLR]
  exact key

theorem psdInvSqrt_support_posSemidef
    {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    (psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian).PosSemidef := by
  rw [psdInvSqrt_support_eq hM]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hM.isHermitian.eigenvectorUnitary : CMatrix a))]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hM.isHermitian.eigenvalues i <;> simp [hi]

theorem psdInvSqrt_support_isHermitian
    {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    (psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian).IsHermitian :=
  (psdInvSqrt_support_posSemidef hM).isHermitian

theorem psdInvSqrt_support_idempotent
    {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    (psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian) *
      (psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian) =
    psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian := by
  rw [psdInvSqrt_support_eq hM]
  let U : CMatrix a := hM.isHermitian.eigenvectorUnitary
  let P : CMatrix a := Matrix.diagonal (fun i =>
    if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0)
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary]
  have hPP : P * P = P := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < hM.isHermitian.eigenvalues i <;> simp [P, hi]
    · simp [P, hij]
  calc (U * P * star U) * (U * P * star U)
      = U * P * (star U * U) * P * star U := by noncomm_ring
    _ = U * P * 1 * P * star U := by rw [hU]
    _ = U * (P * P) * star U := by noncomm_ring
    _ = U * P * star U := by rw [hPP]

theorem psdInvSqrt_support_le_one
    {a : Type u} [Fintype a] [DecidableEq a]
    {M : CMatrix a} (hM : M.PosSemidef) :
    psdInvSqrt M hM.isHermitian * M * psdInvSqrt M hM.isHermitian ≤ 1 := by
  classical
  rw [psdInvSqrt_support_eq hM]
  rw [Matrix.le_iff]
  have hOne : (1 : CMatrix a) =
      (hM.isHermitian.eigenvectorUnitary : CMatrix a) * 1 *
        star (hM.isHermitian.eigenvectorUnitary : CMatrix a) := by
    let U : CMatrix a := hM.isHermitian.eigenvectorUnitary
    simp
  rw [hOne]
  have hsub :
      (hM.isHermitian.eigenvectorUnitary : CMatrix a) * 1 *
          star (hM.isHermitian.eigenvectorUnitary : CMatrix a) -
        (hM.isHermitian.eigenvectorUnitary : CMatrix a) *
          Matrix.diagonal (fun i => if 0 < hM.isHermitian.eigenvalues i
            then (1 : ℂ) else 0) *
          star (hM.isHermitian.eigenvectorUnitary : CMatrix a) =
        (hM.isHermitian.eigenvectorUnitary : CMatrix a) *
          (1 - Matrix.diagonal (fun i => if 0 < hM.isHermitian.eigenvalues i
            then (1 : ℂ) else 0)) *
          star (hM.isHermitian.eigenvectorUnitary : CMatrix a) := by
    noncomm_ring
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (hM.isHermitian.eigenvectorUnitary : CMatrix a))]
  have hdiag :
      (1 - Matrix.diagonal (fun i => if 0 < hM.isHermitian.eigenvalues i
          then (1 : ℂ) else 0) : CMatrix a) =
        Matrix.diagonal (fun i =>
          (1 : ℂ) - if 0 < hM.isHermitian.eigenvalues i then (1 : ℂ) else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  rw [hdiag]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases hi : 0 < hM.isHermitian.eigenvalues i <;> simp [hi]

end

end QITBench
