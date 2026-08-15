/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.ChannelsAndChoiRepresentations.TracePreservationChoiRepresentation.Definitions
@[expose] public section

namespace QITBench.TracePreservationChoiRepresentation

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (Phi : MatrixMap d d) :
    MatrixMap.IsTracePreserving Phi ↔
      partialTraceB (a := d) (b := d) (MatrixMap.choi Phi) = (1 : CMatrix d) := by
  sorry

end

end QITBench.TracePreservationChoiRepresentation
