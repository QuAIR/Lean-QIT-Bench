module

public import QITBench.Base

/-!
# No Maximally Entangled Vector in the Qutrit Antisymmetric Subspace

Bipartite qutrit pure vectors are represented by `PureVector (Fin 3 × Fin 3)`;
the coefficient matrix is read from the vector amplitudes.
-/

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
  IsInvertibleMatrix (coefficientMatrix psi)

end

end QITBench.NoMaximallyEntangledVectorQutritAntisymmetricSubspace
