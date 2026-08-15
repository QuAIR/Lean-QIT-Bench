/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.OneShotEntropiesAndHypothesisTesting.AchievabilityEntanglementConcentration.Definitions

@[expose] public section

namespace QITBench.AchievabilityEntanglementConcentration

open Filter QITBench.OneShot

noncomputable section

theorem targetRankAtRate_pos
    (R : ℝ) (hR0 : 0 ≤ R) (n : ℕ) :
    0 < targetRankAtRate R n := by
  sorry

theorem tendsto_one_of_nonneg_sq_sandwich
    (f lower : ℕ → ℝ)
    (hlower : Filter.Tendsto lower Filter.atTop (nhds 1))
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hlower_sq : ∀ n, lower n ≤ f n ^ 2)
    (hsq_le_one : ∀ n, f n ^ 2 ≤ 1) :
    Filter.Tendsto f Filter.atTop (nhds 1) := by
  sorry

end

end QITBench.AchievabilityEntanglementConcentration
