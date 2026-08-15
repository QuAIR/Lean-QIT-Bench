/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.OneShot

@[expose] public section

namespace QITBench.ConverseEntanglementConcentration

open QITBench.OneShot

noncomputable def concentrationRate
    (M : ℕ → ℕ)
    (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * log2 (M n)

def AsymptoticRateAtMost
    (entropy : ℝ)
    (M : ℕ → ℕ) : Prop :=
  ∀ R : ℝ,
    entropy < R →
      ∀ᶠ n in Filter.atTop, concentrationRate M n ≤ R

end QITBench.ConverseEntanglementConcentration

namespace QITBench.ConverseEntanglementConcentration

open QITBench.OneShot

noncomputable section

end

end QITBench.ConverseEntanglementConcentration
