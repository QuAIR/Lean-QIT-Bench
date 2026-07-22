module

public import QITBench.NormFidelityAndContinuityTools.ChannelFidelityGateFidelityPureInputState.Definitions
@[expose] public section

namespace QITBench.ChannelFidelityGateFidelityPureInputState

open scoped BigOperators

noncomputable section

theorem main
    {m n : ℕ}
    (psi : PureVector (Fin n))
    (U : CMatrix (Fin n))
    (E : Fin (m + 1) → CMatrix (Fin n))
    (htrace : MatrixMap.IsTracePreserving (krausChannel E))
    (hU : IsUnitaryMatrix U) :
    entanglementFidelity psi.state (effectiveKraus U E) =
      pureStateGateFidelity psi U E := by
  sorry

end

end QITBench.ChannelFidelityGateFidelityPureInputState
