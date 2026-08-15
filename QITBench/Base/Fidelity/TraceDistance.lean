/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace QITBench.Fidelity

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open QITBench
open QITBench.MatrixMap

noncomputable section

private theorem re_trace_abs_eq_sum_abs_eigenvalues {d : Type*} [Fintype d] [DecidableEq d]
    {X : CMatrix d} (hX : X.IsHermitian) :
    Complex.re (Matrix.trace (CFC.sqrt (X.conjTranspose * X))) =
      ∑ i, |hX.eigenvalues i| := by
  classical
  set U := hX.eigenvectorUnitary with hU
  set e := hX.eigenvalues with he
  set D : CMatrix d := Matrix.diagonal (RCLike.ofReal ∘ e) with hD
  set Dabs : CMatrix d := Matrix.diagonal (fun i => ((|e i| : ℝ) : ℂ)) with hDabs
  have hspec : X = Unitary.conjStarAlgAut ℂ _ U D := hX.spectral_theorem
  set B : CMatrix d := Unitary.conjStarAlgAut ℂ _ U Dabs with hB
  have hB_eq : B = (U : CMatrix d) * Dabs * (star (U : CMatrix d)) :=
    Unitary.conjStarAlgAut_apply _ _
  have hDabs_pos : Dabs.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr (abs_nonneg _)
  have hB_pos : B.PosSemidef := by
    rw [hB_eq]
    have hstarU : (star (U : CMatrix d)) = ((U : CMatrix d))ᴴ :=
      Matrix.star_eq_conjTranspose _
    rw [hstarU]
    exact hDabs_pos.mul_mul_conjTranspose_same (U : CMatrix d)
  have hDD : Dabs * Dabs = D * D := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst i
      simp only [Matrix.diagonal_apply, ↓reduceIte, Function.comp_apply]
      show ((|e j| : ℝ) : ℂ) * ((|e j| : ℝ) : ℂ) = ((e j : ℝ) : ℂ) * ((e j : ℝ) : ℂ)
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, abs_mul_abs_self]
    · simp [hij]
  have hBB : B * B = X.conjTranspose * X := by
    have hsquare : B * B = Unitary.conjStarAlgAut ℂ _ U (Dabs * Dabs) :=
      (map_mul (Unitary.conjStarAlgAut ℂ (CMatrix d) U) Dabs Dabs).symm
    have hXX : X * X = Unitary.conjStarAlgAut ℂ _ U (D * D) := by
      rw [hspec]
      exact (map_mul (Unitary.conjStarAlgAut ℂ (CMatrix d) U) D D).symm
    rw [hsquare, hDD, ← hXX, hX.eq]
  have hsqrt : CFC.sqrt (X.conjTranspose * X) = B := by
    have ha : 0 ≤ X.conjTranspose * X :=
      Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self X)
    have hb : 0 ≤ B := hB_pos.nonneg
    exact (CFC.sqrt_eq_iff _ _ ha hb).mpr hBB
  have htrace : B.trace = ∑ i, ((|e i| : ℝ) : ℂ) := by
    rw [hB_eq]
    calc Matrix.trace ((U : CMatrix d) * Dabs * (star (U : CMatrix d)))
        = Matrix.trace ((star (U : CMatrix d)) * ((U : CMatrix d) * Dabs)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (((star (U : CMatrix d)) * (U : CMatrix d)) * Dabs) := by
          rw [Matrix.mul_assoc]
      _ = Matrix.trace Dabs := by
          rw [Unitary.coe_star_mul_self, Matrix.one_mul]
      _ = ∑ i, ((|e i| : ℝ) : ℂ) := Matrix.trace_diagonal _
  rw [hsqrt, htrace, ← Complex.ofReal_sum, Complex.ofReal_re]

private theorem trace_conj_unitary {d : Type*} [Fintype d] [DecidableEq d]
    (U : unitary (CMatrix d)) (Z : CMatrix d) :
    Matrix.trace ((U : CMatrix d) * Z * star (U : CMatrix d)) = Matrix.trace Z := by
  calc Matrix.trace ((U : CMatrix d) * Z * star (U : CMatrix d))
      = Matrix.trace (star (U : CMatrix d) * ((U : CMatrix d) * Z)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((star (U : CMatrix d) * (U : CMatrix d)) * Z) := by
        rw [Matrix.mul_assoc]
    _ = Matrix.trace Z := by
        rw [Unitary.coe_star_mul_self, Matrix.one_mul]

private theorem ofKraus_isHermitian {a : Type*} {b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) {X : CMatrix a} (hX : X.IsHermitian) :
    (MatrixMap.ofKraus K X).IsHermitian := by
  change (∑ k : κ, K k * X * (K k).conjTranspose).IsHermitian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

private theorem krausAdjoint_add_apply {a : Type*} {b : Type*}
    [Fintype a] [Fintype b]
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ) (E F : CMatrix b) :
    krausAdjoint K (E + F) = krausAdjoint K E + krausAdjoint K F := by
  ext i j
  simp [krausAdjoint, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

private theorem trace_mul_diagonal {d : Type*} [Fintype d] [DecidableEq d]
    (M : CMatrix d) (f : d → ℂ) :
    Matrix.trace (M * Matrix.diagonal f) = ∑ i, M i i * f i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem exists_hermitian_sign_dual {d : Type*} [Fintype d] [DecidableEq d]
    {Y : CMatrix d} (hY : Y.IsHermitian) :
    ∃ S : CMatrix d,
      (1 - S).PosSemidef ∧ (1 + S).PosSemidef ∧
        Complex.re (Matrix.trace (S * Y)) = traceNorm Y ∧
        S * Y = Y * S ∧
        ((1 + S) * Y).PosSemidef ∧ ((1 - S) * (-Y)).PosSemidef := by
  classical
  set U := hY.eigenvectorUnitary with hU
  set e := hY.eigenvalues with he
  set D : CMatrix d := Matrix.diagonal (RCLike.ofReal ∘ e) with hD
  set sr : d → ℝ := fun i => if 0 ≤ e i then (1 : ℝ) else (-1 : ℝ)
  set s : d → ℂ := fun i => (sr i : ℂ)
  set Ds : CMatrix d := Matrix.diagonal s with hDs
  set S : CMatrix d := Unitary.conjStarAlgAut ℂ (CMatrix d) U Ds with hS
  have hYaut : Y = Unitary.conjStarAlgAut ℂ (CMatrix d) U D := hY.spectral_theorem
  have htwo : (0 : ℂ) ≤ (2 : ℂ) := Complex.zero_le_real.mpr (by norm_num)
  have hD1s_pos : (Matrix.diagonal fun i => (1 : ℂ) - s i).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : 0 ≤ e i
    · simp [s, sr, hi]
    · simp only [s, sr, hi, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one]
      have : (1 : ℂ) - (-1) = 2 := by ring
      rw [this]; exact htwo
  have hD1ps_pos : (Matrix.diagonal fun i => (1 : ℂ) + s i).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : 0 ≤ e i
    · simp only [s, sr, hi, ↓reduceIte, Complex.ofReal_one]
      have : (1 : ℂ) + 1 = 2 := by ring
      rw [this]; exact htwo
    · simp [s, sr, hi]
  have hdiag1 : (1 : CMatrix d) = Matrix.diagonal fun _ : d => (1 : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h1_Ds : (1 : CMatrix d) - Ds = Matrix.diagonal fun i => (1 : ℂ) - s i := by
    rw [hdiag1, hDs, Matrix.diagonal_sub]
  have h1p_Ds : (1 : CMatrix d) + Ds = Matrix.diagonal fun i => (1 : ℂ) + s i := by
    rw [hdiag1, hDs, Matrix.diagonal_add]

  have h1S : 1 - S =
      Unitary.conjStarAlgAut ℂ (CMatrix d) U (Matrix.diagonal fun i => (1 : ℂ) - s i) := by
    have hmap1 : Unitary.conjStarAlgAut ℂ (CMatrix d) U 1 = 1 := map_one _
    calc 1 - S
        = Unitary.conjStarAlgAut ℂ (CMatrix d) U 1 - S := by rw [hmap1]
      _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U 1 -
            Unitary.conjStarAlgAut ℂ (CMatrix d) U Ds := by rw [hS]
      _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U (1 - Ds) := (map_sub _ 1 Ds).symm
      _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U
            (Matrix.diagonal fun i => (1 : ℂ) - s i) := by rw [h1_Ds]
  have h1pS : 1 + S =
      Unitary.conjStarAlgAut ℂ (CMatrix d) U (Matrix.diagonal fun i => (1 : ℂ) + s i) := by
    have hmap1 : Unitary.conjStarAlgAut ℂ (CMatrix d) U 1 = 1 := map_one _
    calc 1 + S
        = Unitary.conjStarAlgAut ℂ (CMatrix d) U 1 + S := by rw [hmap1]
      _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U 1 +
            Unitary.conjStarAlgAut ℂ (CMatrix d) U Ds := by rw [hS]
      _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U (1 + Ds) := (map_add _ 1 Ds).symm
      _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U
            (Matrix.diagonal fun i => (1 : ℂ) + s i) := by rw [h1p_Ds]
  have h1S_eq : 1 - S =
      (U : CMatrix d) * Matrix.diagonal (fun i => (1 : ℂ) - s i) * star (U : CMatrix d) := by
    rw [h1S, Unitary.conjStarAlgAut_apply]
  have h1pS_eq : 1 + S =
      (U : CMatrix d) * Matrix.diagonal (fun i => (1 : ℂ) + s i) * star (U : CMatrix d) := by
    rw [h1pS, Unitary.conjStarAlgAut_apply]
  have hstarU : star (U : CMatrix d) = ((U : CMatrix d))ᴴ :=
    Matrix.star_eq_conjTranspose _
  have h1S_pos : (1 - S).PosSemidef := by
    rw [h1S_eq, hstarU]
    exact hD1s_pos.mul_mul_conjTranspose_same (U : CMatrix d)
  have h1pS_pos : (1 + S).PosSemidef := by
    rw [h1pS_eq, hstarU]
    exact hD1ps_pos.mul_mul_conjTranspose_same (U : CMatrix d)
  have hDsD : Ds * D = Matrix.diagonal fun i => ((|e i| : ℝ) : ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst i
      simp only [Matrix.diagonal_apply, ↓reduceIte, Function.comp_apply, s, sr]
      by_cases hi : 0 ≤ e j
      · simp [hi, abs_of_nonneg hi]
      · have hneg : e j < 0 := lt_of_not_ge hi
        simp only [hi, ↓reduceIte, Complex.ofReal_neg, Complex.ofReal_one,
          abs_of_neg hneg, neg_one_mul]
        rfl
    · simp [hij]
  have hDDs : D * Ds = Ds * D := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [s, sr]
      ring
    · simp [hij]
  have hSY : S * Y =
      Unitary.conjStarAlgAut ℂ (CMatrix d) U (Ds * D) := by
    rw [hS, hYaut, ← map_mul]
  have hYS : Y * S =
      Unitary.conjStarAlgAut ℂ (CMatrix d) U (D * Ds) := by
    rw [hS, hYaut, ← map_mul]
  have hcomm : S * Y = Y * S := by
    rw [hSY, hYS, hDDs]
  have hDplus : (D + Ds * D).PosSemidef := by
    rw [hD, hDsD, Matrix.diagonal_add]
    apply Matrix.PosSemidef.diagonal
    intro i
    simp only [Pi.zero_apply, Function.comp_apply]
    have hre : 0 ≤ e i + |e i| := by linarith [neg_le_abs (e i)]
    have hc : (0 : ℂ) ≤ ((e i + |e i| : ℝ) : ℂ) := Complex.zero_le_real.mpr hre
    simpa only [Complex.ofReal_add] using hc
  have hDminus : (-D + Ds * D).PosSemidef := by
    have heq : -D + Ds * D = Matrix.diagonal (fun i => ((-e i + |e i| : ℝ) : ℂ)) := by
      rw [hD, hDsD]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Function.comp_apply]
      · simp [hij]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Complex.zero_le_real.mpr (by
      linarith [le_abs_self (e i)])
  have hplus : ((1 + S) * Y).PosSemidef := by
    have heq : (1 + S) * Y =
        Unitary.conjStarAlgAut ℂ (CMatrix d) U (D + Ds * D) := by
      calc
        (1 + S) * Y = Y + S * Y := by rw [Matrix.add_mul, Matrix.one_mul]
        _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U D +
              Unitary.conjStarAlgAut ℂ (CMatrix d) U (Ds * D) := by
                rw [hYaut]
                congr 1
                rw [← hYaut, hSY]
        _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U (D + Ds * D) := (map_add _ _ _).symm
    rw [heq, Unitary.conjStarAlgAut_apply]
    have hstarU : star (U : CMatrix d) = ((U : CMatrix d))ᴴ :=
      Matrix.star_eq_conjTranspose _
    rw [hstarU]
    exact hDplus.mul_mul_conjTranspose_same (U : CMatrix d)
  have hminus : ((1 - S) * (-Y)).PosSemidef := by
    have heq : (1 - S) * (-Y) =
        Unitary.conjStarAlgAut ℂ (CMatrix d) U (-D + Ds * D) := by
      calc
        (1 - S) * (-Y) = -Y + S * Y := by noncomm_ring
        _ = -Unitary.conjStarAlgAut ℂ (CMatrix d) U D +
              Unitary.conjStarAlgAut ℂ (CMatrix d) U (Ds * D) := by
                rw [hYaut]
                congr 1
                rw [← hYaut, hSY]
        _ = Unitary.conjStarAlgAut ℂ (CMatrix d) U (-D + Ds * D) := by
          rw [map_add, map_neg]
    rw [heq, Unitary.conjStarAlgAut_apply]
    have hstarU : star (U : CMatrix d) = ((U : CMatrix d))ᴴ :=
      Matrix.star_eq_conjTranspose _
    rw [hstarU]
    exact hDminus.mul_mul_conjTranspose_same (U : CMatrix d)
  have htr : Matrix.trace (S * Y) = ∑ i, ((|e i| : ℝ) : ℂ) := by
    rw [hSY, hDsD, Unitary.conjStarAlgAut_apply, trace_conj_unitary U _]
    exact Matrix.trace_diagonal _
  refine ⟨S, h1S_pos, h1pS_pos, ?_, hcomm, hplus, hminus⟩
  rw [htr, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact (re_trace_abs_eq_sum_abs_eigenvalues hY).symm

private theorem re_trace_mul_le_sum_abs_eigenvalues {d : Type*} [Fintype d] [DecidableEq d]
    {X T : CMatrix d} (hX : X.IsHermitian)
    (hT1 : (1 - T).PosSemidef) (hT2 : (1 + T).PosSemidef) :
    Complex.re (Matrix.trace (T * X)) ≤ ∑ i, |hX.eigenvalues i| := by
  classical
  set U := hX.eigenvectorUnitary with hU
  set e := hX.eigenvalues with he
  set D : CMatrix d := Matrix.diagonal (RCLike.ofReal ∘ e) with hD
  have hXaut : X = Unitary.conjStarAlgAut ℂ (CMatrix d) U D := hX.spectral_theorem

  set M : CMatrix d := star (U : CMatrix d) * T * (U : CMatrix d) with hM
  have hUstarU : (U : CMatrix d) * star (U : CMatrix d) = 1 :=
    Unitary.coe_mul_star_self U
  have hstarUU : star (U : CMatrix d) * (U : CMatrix d) = 1 :=
    Unitary.coe_star_mul_self U
  have hTaut : T = Unitary.conjStarAlgAut ℂ (CMatrix d) U M := by
    rw [hM, Unitary.conjStarAlgAut_apply]

    refine Eq.symm ?_
    calc (U : CMatrix d) * (star (U : CMatrix d) * T * (U : CMatrix d)) *
            star (U : CMatrix d)
        = ((U : CMatrix d) * star (U : CMatrix d)) * T *
            ((U : CMatrix d) * star (U : CMatrix d)) := by
          simp only [Matrix.mul_assoc]
      _ = (1 : CMatrix d) * T * (1 : CMatrix d) := by rw [hUstarU]
      _ = T := by simp only [Matrix.one_mul, Matrix.mul_one]
  have htr : Matrix.trace (T * X) = Matrix.trace (M * D) := by
    rw [hTaut, hXaut, ← map_mul, Unitary.conjStarAlgAut_apply, trace_conj_unitary U _]
  have htr_sum : Matrix.trace (M * D) = ∑ i, M i i * ((e i : ℝ) : ℂ) := by
    simpa [D, Function.comp_apply] using trace_mul_diagonal M (RCLike.ofReal ∘ e)
  have hstarU_mat : star (U : CMatrix d) = ((U : CMatrix d))ᴴ :=
    Matrix.star_eq_conjTranspose _
  have h1M : 1 - M = star (U : CMatrix d) * (1 - T) * (U : CMatrix d) := by
    rw [hM]

    calc (1 : CMatrix d) - star (U : CMatrix d) * T * (U : CMatrix d)
        = star (U : CMatrix d) * (U : CMatrix d) -
            star (U : CMatrix d) * T * (U : CMatrix d) := by
          rw [hstarUU]
      _ = (star (U : CMatrix d) * (1 : CMatrix d) -
            star (U : CMatrix d) * T) * (U : CMatrix d) := by
          have hL : star (U : CMatrix d) * (U : CMatrix d) =
              (star (U : CMatrix d) * (1 : CMatrix d)) * (U : CMatrix d) := by
            simp only [Matrix.mul_one]
          have hR : star (U : CMatrix d) * T * (U : CMatrix d) =
              (star (U : CMatrix d) * T) * (U : CMatrix d) := by
            simp only [Matrix.mul_assoc]
          rw [hL, hR, Matrix.sub_mul]
      _ = star (U : CMatrix d) * ((1 : CMatrix d) - T) * (U : CMatrix d) := by
          rw [← Matrix.mul_sub]
  have h1pM : 1 + M = star (U : CMatrix d) * (1 + T) * (U : CMatrix d) := by
    rw [hM]
    calc (1 : CMatrix d) + star (U : CMatrix d) * T * (U : CMatrix d)
        = star (U : CMatrix d) * (U : CMatrix d) +
            star (U : CMatrix d) * T * (U : CMatrix d) := by
          rw [hstarUU]
      _ = (star (U : CMatrix d) * (1 : CMatrix d) +
            star (U : CMatrix d) * T) * (U : CMatrix d) := by
          have hL : star (U : CMatrix d) * (U : CMatrix d) =
              (star (U : CMatrix d) * (1 : CMatrix d)) * (U : CMatrix d) := by
            simp only [Matrix.mul_one]
          have hR : star (U : CMatrix d) * T * (U : CMatrix d) =
              (star (U : CMatrix d) * T) * (U : CMatrix d) := by
            simp only [Matrix.mul_assoc]
          rw [hL, hR, Matrix.add_mul]
      _ = star (U : CMatrix d) * ((1 : CMatrix d) + T) * (U : CMatrix d) := by
          rw [← Matrix.mul_add]
  have h1M_pos : (1 - M).PosSemidef := by
    rw [h1M, hstarU_mat]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same hT1 (U : CMatrix d)
  have h1pM_pos : (1 + M).PosSemidef := by
    rw [h1pM, hstarU_mat]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same hT2 (U : CMatrix d)
  have hdiag_le : ∀ i, |Complex.re (M i i)| ≤ 1 := by
    intro i
    have hlo : 0 ≤ Complex.re ((1 - M) i i) :=
      (Complex.nonneg_iff.mp (h1M_pos.diag_nonneg (i := i))).1
    have hhi : 0 ≤ Complex.re ((1 + M) i i) :=
      (Complex.nonneg_iff.mp (h1pM_pos.diag_nonneg (i := i))).1
    have hlo' : Complex.re (M i i) ≤ 1 := by
      have : Complex.re ((1 - M) i i) = 1 - Complex.re (M i i) := by
        simp [Matrix.sub_apply]
      linarith
    have hhi' : -1 ≤ Complex.re (M i i) := by
      have : Complex.re ((1 + M) i i) = 1 + Complex.re (M i i) := by
        simp [Matrix.add_apply]
      linarith
    exact abs_le.mpr ⟨hhi', hlo'⟩
  rw [htr, htr_sum, Complex.re_sum]
  have hterm : ∀ i, Complex.re (M i i * ((e i : ℝ) : ℂ)) ≤ |e i| := by
    intro i
    have hre : Complex.re (M i i * ((e i : ℝ) : ℂ)) =
        Complex.re (M i i) * e i := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hre]
    calc Complex.re (M i i) * e i
        ≤ |Complex.re (M i i) * e i| := le_abs_self _
      _ = |Complex.re (M i i)| * |e i| := abs_mul _ _
      _ ≤ 1 * |e i| :=
          mul_le_mul_of_nonneg_right (hdiag_le i) (abs_nonneg _)
      _ = |e i| := one_mul _
  exact Finset.sum_le_sum fun i _ => hterm i

theorem re_trace_mul_le_traceNorm {d : Type*} [Fintype d] [DecidableEq d]
    {X T : CMatrix d} (hX : X.IsHermitian)
    (hT1 : (1 - T).PosSemidef) (hT2 : (1 + T).PosSemidef) :
    (T * X).trace.re ≤ traceNorm X := by
  calc
    (T * X).trace.re ≤ ∑ i, |hX.eigenvalues i| :=
      re_trace_mul_le_sum_abs_eigenvalues hX hT1 hT2
    _ = traceNorm X := (re_trace_abs_eq_sum_abs_eigenvalues hX).symm

private theorem traceNorm_ofKraus_le {a : Type*} {b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {κ : Type*} [Fintype κ]
    (K : κ → Matrix b a ℂ)
    (hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K))
    {X : CMatrix a} (hX : X.IsHermitian) :
    traceNorm (MatrixMap.ofKraus K X) ≤ traceNorm X := by
  classical
  have hNX : (MatrixMap.ofKraus K X).IsHermitian := ofKraus_isHermitian K hX
  have hL : traceNorm (MatrixMap.ofKraus K X) =
      ∑ i, |hNX.eigenvalues i| := by
    change Complex.re (Matrix.trace (CFC.sqrt
      ((MatrixMap.ofKraus K X).conjTranspose * MatrixMap.ofKraus K X))) =
      ∑ i, |hNX.eigenvalues i|
    exact re_trace_abs_eq_sum_abs_eigenvalues hNX
  have hR : traceNorm X = ∑ i, |hX.eigenvalues i| := by
    change Complex.re (Matrix.trace (CFC.sqrt (X.conjTranspose * X))) =
      ∑ i, |hX.eigenvalues i|
    exact re_trace_abs_eq_sum_abs_eigenvalues hX
  rw [hL, hR]
  obtain ⟨S, hS1, hS2, hSeq, _, _, _⟩ := exists_hermitian_sign_dual hNX

  have hdual :
      Matrix.trace (S * MatrixMap.ofKraus K X) =
        Matrix.trace (krausAdjoint K S * X) := by
    have h1 := ofKraus_trace_duality K X S

    have h2 : Matrix.trace (S * MatrixMap.ofKraus K X) =
        Matrix.trace (MatrixMap.ofKraus K X * S) := Matrix.trace_mul_comm _ _
    have h3 : Matrix.trace (X * krausAdjoint K S) =
        Matrix.trace (krausAdjoint K S * X) := Matrix.trace_mul_comm _ _
    exact h2.trans (h1.trans h3)
  have hSeq' : ∑ i, |hNX.eigenvalues i| =
      Complex.re (Matrix.trace (krausAdjoint K S * X)) := by
    rw [← hL, ← hSeq, hdual]

  have hone : krausAdjoint K (1 : CMatrix b) = 1 :=
    krausAdjoint_one_of_tracePreserving K hTP
  have hAdj1 : (1 - krausAdjoint K S).PosSemidef := by
    have h : 1 - krausAdjoint K S = krausAdjoint K (1 - S) := by
      rw [krausAdjoint_sub_apply, hone]
    rw [h]
    exact krausAdjoint_mapsPositive K (1 - S) hS1
  have hAdj2 : (1 + krausAdjoint K S).PosSemidef := by
    have h : 1 + krausAdjoint K S = krausAdjoint K (1 + S) := by
      rw [krausAdjoint_add_apply, hone]
    rw [h]
    exact krausAdjoint_mapsPositive K (1 + S) hS2
  have hle := re_trace_mul_le_sum_abs_eigenvalues hX hAdj1 hAdj2
  linarith

theorem traceDistance_channel_mono
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho sigma : State a)
    (channel : Channel a b) :
    traceDistance
        ((channel.applyState rho).matrix)
        ((channel.applyState sigma).matrix) ≤
      traceDistance rho.matrix sigma.matrix := by
  classical
  set X : CMatrix a := rho.matrix - sigma.matrix with hXdef
  have hX : X.IsHermitian :=
    Matrix.IsHermitian.sub rho.pos.isHermitian sigma.pos.isHermitian
  have hmap : channel.map rho.matrix - channel.map sigma.matrix = channel.map X := by
    rw [hXdef, map_sub]

  change (1 / 2 : ℝ) *
      traceNorm ((channel.applyState rho).matrix - (channel.applyState sigma).matrix) ≤
    (1 / 2 : ℝ) * traceNorm (rho.matrix - sigma.matrix)
  have happ :
      (channel.applyState rho).matrix - (channel.applyState sigma).matrix =
        channel.map X := by
    change channel.map rho.matrix - channel.map sigma.matrix = channel.map X
    exact hmap
  rw [happ]

  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd channel.map channel.completelyPositive
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact channel.tracePreserving
  have hNX : channel.map X = MatrixMap.ofKraus K X := by rw [hK]
  rw [hNX]
  have hle := traceNorm_ofKraus_le K hTP hX
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  exact mul_le_mul_of_nonneg_left hle hhalf

theorem exists_effect_trace_difference_eq_traceDistance
    {a : Type*} [Fintype a] [DecidableEq a]
    (rho sigma : State a) :
    ∃ E : CMatrix a, E.PosSemidef ∧ E ≤ 1 ∧
      ((E * (rho.matrix - sigma.matrix)).trace).re =
        traceDistance rho.matrix sigma.matrix := by
  classical
  let X : CMatrix a := rho.matrix - sigma.matrix
  have hX : X.IsHermitian := rho.pos.isHermitian.sub sigma.pos.isHermitian
  obtain ⟨S, hSminus, hSplus, hSscore, _, _, _⟩ := exists_hermitian_sign_dual hX
  let E : CMatrix a := (1 / 2 : ℝ) • (1 + S)
  have hEpos : E.PosSemidef := by
    exact hSplus.smul (by norm_num)
  have hEle : E ≤ 1 := by
    rw [Matrix.le_iff]
    have hcomp : (1 : CMatrix a) - E = (1 / 2 : ℝ) • (1 - S) := by
      simp [E]
      module
    rw [hcomp]
    exact hSminus.smul (by norm_num)
  refine ⟨E, hEpos, hEle, ?_⟩
  have htrX : X.trace = 0 := by
    simp [X, rho.trace_eq_one, sigma.trace_eq_one]
  change ((E * X).trace).re = (1 / 2 : ℝ) * traceNorm X
  rw [show E * X = (1 / 2 : ℝ) • (X + S * X) by
    simp [E, Matrix.add_mul]]
  rw [Matrix.trace_smul, Matrix.trace_add, htrX, zero_add, Complex.smul_re,
    hSscore]
  rfl

end

end QITBench.Fidelity
