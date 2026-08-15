/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.EntropyCodingAndInformationInequalities.HolevoBoundClassicalCapacityNQubits.Definitions
@[expose] public section

namespace QITBench.HolevoBoundClassicalCapacityNQubits

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {ι y : Type*} [Fintype ι] [Fintype y] [DecidableEq y]
    (n : ℕ)
    (p : ι → ℝ)
    (rho : ι → State (NQubitBasis n))
    (average : State (NQubitBasis n))
    (M : POVM y (NQubitBasis n))
    (hprob : IsProbabilityDistribution p)
    (haverage : average.matrix = averageStateMatrix p rho) :
    HolevoBoundForMeasurement p rho average M ∧
      vonNeumannEntropyMatrix average.matrix ≤ n ∧
        classicalMutualInformation p rho M ≤ n := by
  sorry

end

end QITBench.HolevoBoundClassicalCapacityNQubits
