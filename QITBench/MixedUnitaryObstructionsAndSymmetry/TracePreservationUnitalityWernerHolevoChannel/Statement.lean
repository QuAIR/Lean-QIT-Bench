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
