module

public import QITBench.EntropyCodingAndInformationInequalities.QuantumFanoInequality.Definitions

@[expose] public section

namespace QITBench.QuantumFanoInequality

open scoped BigOperators

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ)
    (hD : Fintype.card d = D)
    (rhoA : State d)
    (psi : PureVector (d × d))
    (E : Channel d d)
    (_hpsi : IsPurification rhoA psi) :
    exchangeEntropy E psi ≤
      binaryEntropy (entanglementFidelity E psi) +
        (1 - entanglementFidelity E psi) * log2 ((D : ℝ) ^ 2 - 1) := by
  sorry

end

end QITBench.QuantumFanoInequality
