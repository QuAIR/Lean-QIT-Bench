module

public import QITBench.ChannelsAndChoiRepresentations.UnitalityChoiRepresentation.Definitions
@[expose] public section

namespace QITBench.UnitalityChoiRepresentation

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (Phi : MatrixMap d d) :
    IsUnital Phi ↔
      partialTraceA (a := d) (b := d) (MatrixMap.choi Phi) = (1 : CMatrix d) := by
  sorry

end

end QITBench.UnitalityChoiRepresentation
