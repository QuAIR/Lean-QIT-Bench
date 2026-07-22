module

public import QITBench.NormFidelityAndContinuityTools.TraceDistanceLowerBoundPureState.Definitions
@[expose] public section

namespace QITBench.TraceDistanceLowerBoundPureState

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n : ℕ}
    (psi : PureVector (Fin n))
    (sigma : State (Fin n)) :
    1 - pureStateFidelity psi sigma ^ 2 ≤
      traceDistance psi.state.matrix sigma.matrix := by
  sorry

end

end QITBench.TraceDistanceLowerBoundPureState
