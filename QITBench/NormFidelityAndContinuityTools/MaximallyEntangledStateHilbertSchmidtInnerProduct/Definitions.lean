module

public import QITBench.Base

/-!
# Maximally Entangled State Hilbert--Schmidt Inner Product

The maximally entangled expectation is represented as the finite basis double
sum and related to the usual trace pairings.
-/

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
