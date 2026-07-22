module

public import QITBench.Base

/-!
# Unitality in the Choi Representation

The Choi matrix is `MatrixMap.choi`; the subsystem trace is Base
`partialTraceA`.
-/

@[expose] public section

namespace QITBench.UnitalityChoiRepresentation

noncomputable section

def IsUnital {d : Type*} [Fintype d] [DecidableEq d]
    (Phi : MatrixMap d d) : Prop :=
  Phi (1 : CMatrix d) = 1

end

end QITBench.UnitalityChoiRepresentation
