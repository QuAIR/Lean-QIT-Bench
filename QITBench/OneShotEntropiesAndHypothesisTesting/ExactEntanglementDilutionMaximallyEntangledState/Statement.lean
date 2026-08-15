/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.OneShotEntropiesAndHypothesisTesting.ExactEntanglementDilutionMaximallyEntangledState.Definitions
@[expose] public section

namespace QITBench.ExactEntanglementDilutionMaximallyEntangledState

open QITBench.OneShot

noncomputable section

theorem main
    {d M : ℕ}
    (hd : 0 < d)
    (mu : Fin d → ℝ)
    (hmu : IsSchmidtProbabilityVector mu)
    (hM : 0 < M) :
    CanTransformDeterministicallyBySEP mu M ↔
      largestSchmidtCoefficient mu hd ≤ (1 : ℝ) / (M : ℝ) := by
  sorry

end

end QITBench.ExactEntanglementDilutionMaximallyEntangledState
