/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.OneShotEntropiesAndHypothesisTesting.AchievabilityEntanglementConcentration.Definitions
@[expose] public section

namespace QITBench.AchievabilityEntanglementConcentration

open scoped BigOperators
open QITBench.OneShot

noncomputable section

theorem main
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ)
    (psi : PureVector (X × X))
    (hp : IsProbabilityDistribution p)
    (hpsi : HasSchmidtCoefficients psi p) :
    ∀ R : ℝ,
      0 ≤ R →
        R < schmidtEntropy p →
          ∃ M : ℕ → ℕ,
            ∃ protocols :
              (n : ℕ) →
                SEPProtocol
                  (TensorPower X n) (TensorPower X n)
                  (Fin (M n)) (Fin (M n)),
              (∀ n, 0 < M n) ∧
                (∀ n, M n = targetRankAtRate R n) ∧
                  Filter.Tendsto
                    (fun n =>
                      quantumFidelity
                        ((protocols n).channel.applyState
                          (psi.state.tensorPowerBipartite n)).matrix
                        (maximallyEntangledDensity (M n)))
                    Filter.atTop
                    (nhds 1) := by
  sorry

end

end QITBench.AchievabilityEntanglementConcentration
