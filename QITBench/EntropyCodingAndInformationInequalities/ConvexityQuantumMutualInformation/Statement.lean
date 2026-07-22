module

public import QITBench.EntropyCodingAndInformationInequalities.ConvexityQuantumMutualInformation.Definitions
@[expose] public section

namespace QITBench.ConvexityQuantumMutualInformation

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (hA : 2 ≤ Fintype.card a)
    (hB : 2 ≤ Fintype.card b) :
    ¬ ConvexOnDensity (mutualInformation (a := a) (b := b)) ∧
      ¬ ConcaveOnDensity (mutualInformation (a := a) (b := b)) := by
  sorry

end

end QITBench.ConvexityQuantumMutualInformation
