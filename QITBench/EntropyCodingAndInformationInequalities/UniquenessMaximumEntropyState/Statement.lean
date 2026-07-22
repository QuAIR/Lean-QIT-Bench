module

public import QITBench.EntropyCodingAndInformationInequalities.UniquenessMaximumEntropyState.Definitions
@[expose] public section

namespace QITBench.UniquenessMaximumEntropyState

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ)
    (_hD : Fintype.card d = D)
    (rho : State d)
    (hneq : rho.matrix ≠ maximallyMixed D)
    (h_random :
      ∃ U : Fin (D ^ 2) → CMatrix d,
        RandomUnitaryIdentity D U) :
    vonNeumannEntropyMatrix rho.matrix < log2 (D : ℝ) ∧
      EntropyUniquelyMaximizedAtMixed (d := d) D := by
  sorry

end

end QITBench.UniquenessMaximumEntropyState
