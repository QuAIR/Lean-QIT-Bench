/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Information.Entropy.Entropy

@[expose] public section

namespace QITBench

noncomputable section

theorem log2_one_div (x : ℝ) : log2 (1 / x) = -log2 x := by
  unfold log2
  rw [one_div, Real.log_inv]
  ring

theorem log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2
  rw [Real.log_mul hx hy]
  ring

theorem log2_two_rpow (t : ℝ) : log2 (2 ^ t : ℝ) = t := by
  unfold log2
  rw [show Real.log ((2 : ℝ) ^ t) = t * Real.log 2 by
    exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) t]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem log2_rpow_two (x : ℝ) : log2 (Real.rpow 2 x) = x := by
  unfold log2
  rw [show Real.log (Real.rpow 2 x) = x * Real.log 2 by
    exact Real.log_rpow (by norm_num : (0 : ℝ) < 2) x]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem log2_rpow_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    log2 (x ^ y) = y * log2 x := by
  unfold log2
  rw [Real.log_rpow hx]
  ring

theorem log2_mono_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos one_lt_two))

theorem neg_log2_antitone_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    -log2 y ≤ -log2 x := by
  unfold log2
  exact neg_le_neg
    (div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
      (le_of_lt (Real.log_pos one_lt_two)))

theorem log2_two : log2 2 = 1 := by
  unfold log2
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp [hlog2]

theorem log2_one : log2 1 = 0 := by
  unfold log2
  simp

theorem xlog2_eq_mul_log2 (x : ℝ) : xlog2 x = x * log2 x := by
  by_cases hx : x = 0
  · simp [xlog2, hx]
  · simp [xlog2, hx]

end
end QITBench
