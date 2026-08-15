/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.UnitaritySystemEnvironmentEvolution

noncomputable section

def IsUnitaryMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (U : CMatrix d) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

noncomputable def X : CMatrix (Fin 2) :=
  !![0, 1; 1, 0]

noncomputable def Y : CMatrix (Fin 2) :=
  !![0, -Complex.I; Complex.I, 0]

noncomputable def U : CMatrix (Fin 2 × Fin 2) :=
  let c : ℂ := (1 : ℂ) / (Real.sqrt 2 : ℂ)
  c • Matrix.kronecker X (1 : CMatrix (Fin 2)) +
    c • Matrix.kronecker Y X

end

end QITBench.UnitaritySystemEnvironmentEvolution
