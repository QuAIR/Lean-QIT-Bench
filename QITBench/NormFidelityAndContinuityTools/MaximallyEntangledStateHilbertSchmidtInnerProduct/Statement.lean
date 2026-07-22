module

public import QITBench.NormFidelityAndContinuityTools.MaximallyEntangledStateHilbertSchmidtInnerProduct.Definitions
@[expose] public section

namespace QITBench.MaximallyEntangledStateHilbertSchmidtInnerProduct

open scoped BigOperators

noncomputable section

theorem main
    {d : ℕ}
    (A B : CMatrix (Fin d)) :
    maximallyEntangledExpectation A B =
      Matrix.trace (A.transpose * B) ∧
      maximallyEntangledExpectation (entrywiseConj A) B =
        Matrix.trace (A.conjTranspose * B) := by
  sorry

end

end QITBench.MaximallyEntangledStateHilbertSchmidtInnerProduct
