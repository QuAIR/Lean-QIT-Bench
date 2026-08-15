/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.TracePreservationUnitalityWernerHolevoChannel.Definitions
@[expose] public section

namespace QITBench.TracePreservationUnitalityWernerHolevoChannel

noncomputable section

theorem main :
    MatrixMap.IsTracePreserving wernerHolevoChannel ∧
      wernerHolevoChannel (1 : CMatrix (Fin 3)) =
        (1 : CMatrix (Fin 3)) := by
  sorry

end

end QITBench.TracePreservationUnitalityWernerHolevoChannel
