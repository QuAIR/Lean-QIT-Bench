module

public import QITBench.NormFidelityAndContinuityTools.AlbertiSTheoremCommutingCase.Definitions
@[expose] public section

namespace QITBench.AlbertiSTheoremCommutingCase

open scoped BigOperators

noncomputable section

theorem main
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (rhoWeights sigmaWeights : ι → ℝ)
    (hrho_nonneg : ∀ i, 0 ≤ rhoWeights i)
    (hsigma_nonneg : ∀ i, 0 ≤ sigmaWeights i)
    (hrho_sum : (∑ i, rhoWeights i) = 1)
    (hsigma_sum : (∑ i, sigmaWeights i) = 1)
    (F : ℝ)
    (hF : HasAlbertiVariationalFidelity F rhoWeights sigmaWeights) :
    IsGLB (albertiDiagonalValues rhoWeights sigmaWeights)
      ((classicalFidelity rhoWeights sigmaWeights) ^ 2) ∧
      F = classicalFidelity rhoWeights sigmaWeights := by
  sorry

end

end QITBench.AlbertiSTheoremCommutingCase
