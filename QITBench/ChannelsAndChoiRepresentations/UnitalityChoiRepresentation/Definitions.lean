/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.UnitalityChoiRepresentation

noncomputable section

def IsUnital {d : Type*} [Fintype d] [DecidableEq d]
    (Phi : MatrixMap d d) : Prop :=
  Phi (1 : CMatrix d) = 1

end

end QITBench.UnitalityChoiRepresentation
