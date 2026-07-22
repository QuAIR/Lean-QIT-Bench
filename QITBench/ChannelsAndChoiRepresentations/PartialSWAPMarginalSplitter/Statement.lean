module

public import QITBench.ChannelsAndChoiRepresentations.PartialSWAPMarginalSplitter.Definitions
@[expose] public section

namespace QITBench.PartialSWAPMarginalSplitter

noncomputable section

theorem main :
    IsUnitaryMatrix partialSWAP ∧
      ∀ rho : State (Fin 2),
        let sigma := evolve partialSWAP (inputState rho)
        partialTraceA (a := Fin 2) (b := Fin 2) sigma = splitterMarginal rho ∧
          partialTraceB (a := Fin 2) (b := Fin 2) sigma = splitterMarginal rho := by
  sorry

end

end QITBench.PartialSWAPMarginalSplitter
