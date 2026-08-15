/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.NoMaximallyEntangledVectorQutritAntisymmetricSubspace

noncomputable section

noncomputable def coefficientMatrix
    (psi : PureVector (Fin 3 × Fin 3)) :
    CMatrix (Fin 3) :=
  fun i j => psi.amp (i, j)

noncomputable def transposeMatrix
    (C : CMatrix (Fin 3)) :
    CMatrix (Fin 3) :=
  fun i j => C j i

def IsSkewSymmetric
    (C : CMatrix (Fin 3)) : Prop :=
  transposeMatrix C = -C

def LiesInQutritAntisymmetricSubspace
    (psi : PureVector (Fin 3 × Fin 3)) : Prop :=
  IsSkewSymmetric (coefficientMatrix psi)

def IsInvertibleMatrix
    (C : CMatrix (Fin 3)) : Prop :=
  ∃ Cinv : CMatrix (Fin 3),
    C * Cinv = 1 ∧ Cinv * C = 1

def IsMaximallyEntangledVector
    (psi : PureVector (Fin 3 × Fin 3)) : Prop :=
  psi.state.marginalA.matrix = (1 / 3 : ℂ) • (1 : CMatrix (Fin 3))

end

end QITBench.NoMaximallyEntangledVectorQutritAntisymmetricSubspace
