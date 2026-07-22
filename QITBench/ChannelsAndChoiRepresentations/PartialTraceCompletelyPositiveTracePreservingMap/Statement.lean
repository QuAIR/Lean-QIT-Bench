module

public import QITBench.ChannelsAndChoiRepresentations.PartialTraceCompletelyPositiveTracePreservingMap.Definitions
@[expose] public section

namespace QITBench.PartialTraceCompletelyPositiveTracePreservingMap

noncomputable section

theorem main
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    partialTraceBMap (a := a) (b := b) =
        MatrixMap.ofKraus (partialTraceBKraus (a := a) (b := b)) ∧
      MatrixMap.IsTracePreserving (partialTraceBMap (a := a) (b := b)) := by
  sorry

end

end QITBench.PartialTraceCompletelyPositiveTracePreservingMap
