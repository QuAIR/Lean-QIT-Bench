module

public import QITBench.Base

/-!
# Partial Trace as a Completely Positive Trace-Preserving Map

The partial trace is bundled as a `MatrixMap`; the Kraus representation uses
`MatrixMap.ofKraus`, and trace preservation uses Base's predicate.
-/

@[expose] public section

namespace QITBench.PartialTraceCompletelyPositiveTracePreservingMap

noncomputable section

noncomputable def partialTraceBMap {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    MatrixMap (a × b) a where
  toFun := partialTraceB (a := a) (b := b)
  map_add' X Y := partialTraceB_add X Y
  map_smul' c X := partialTraceB_smul c X

noncomputable def partialTraceBKraus {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (k : b) :
    Matrix a (a × b) ℂ :=
  fun i p => if p.1 = i ∧ p.2 = k then 1 else 0

end

end QITBench.PartialTraceCompletelyPositiveTracePreservingMap
