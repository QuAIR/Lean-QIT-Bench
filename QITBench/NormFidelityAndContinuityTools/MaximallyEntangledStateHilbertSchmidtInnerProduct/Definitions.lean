/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.MaximallyEntangledStateHilbertSchmidtInnerProduct

open scoped BigOperators

noncomputable section

noncomputable def maximallyEntangledExpectation
    {d : ℕ}
    (A B : CMatrix (Fin d)) : ℂ :=
  ∑ i, ∑ j, A j i * B j i

noncomputable def entrywiseConj
    {d : ℕ}
    (A : CMatrix (Fin d)) : CMatrix (Fin d) :=
  fun i j => star (A i j)

end

end QITBench.MaximallyEntangledStateHilbertSchmidtInnerProduct
