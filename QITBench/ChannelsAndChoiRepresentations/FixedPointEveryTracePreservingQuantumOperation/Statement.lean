/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.ChannelsAndChoiRepresentations.FixedPointEveryTracePreservingQuantumOperation.Definitions
@[expose] public section

namespace QITBench.FixedPointEveryTracePreservingQuantumOperation

noncomputable section

theorem main
    {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
    (E : Channel H H) :
    ∃ rhoStar : State H,
      E.applyState rhoStar = rhoStar := by
  sorry

end

end QITBench.FixedPointEveryTracePreservingQuantumOperation
