module

public import QITBench.OneShotEntropiesAndHypothesisTesting.ConverseEntanglementConcentration.Definitions

@[expose] public section

namespace QITBench.ConverseEntanglementConcentration

open QITBench.OneShot

noncomputable section

theorem main
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ)
    (psi : PureVector (X × X))
    (M : ℕ → ℕ)
    (protocols :
      (n : ℕ) →
        LOCCProtocol
          (TensorPower X n) (TensorPower X n)
          (Fin (M n)) (Fin (M n)))
    (hp : IsProbabilityDistribution p)
    (hpsi : HasSchmidtCoefficients psi p)
    (hM_pos : ∀ n, 0 < M n)
    (hfid :
      Filter.Tendsto
        (fun n =>
          quantumFidelity
            ((protocols n).channel.applyState
              (psi.state.tensorPowerBipartite n)).matrix
            (maximallyEntangledDensity (M n)))
        Filter.atTop
        (nhds 1)) :
    AsymptoticRateAtMost (schmidtEntropy p) M := by
  sorry

end

end QITBench.ConverseEntanglementConcentration
