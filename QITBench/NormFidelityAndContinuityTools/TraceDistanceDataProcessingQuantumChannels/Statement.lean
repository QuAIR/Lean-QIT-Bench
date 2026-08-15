/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.NormFidelityAndContinuityTools.TraceDistanceDataProcessingQuantumChannels.Definitions
@[expose] public section

namespace QITBench.TraceDistanceDataProcessingQuantumChannels

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n m : ℕ}
    (rho sigma : State (Fin n))
    (channel : Channel (Fin n) (Fin m)) :
    traceDistance
        ((channel.applyState rho).matrix)
        ((channel.applyState sigma).matrix) ≤
      traceDistance rho.matrix sigma.matrix := by
  sorry

end

end QITBench.TraceDistanceDataProcessingQuantumChannels
