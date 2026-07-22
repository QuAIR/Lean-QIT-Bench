module

public import QITBench.Base

/-!
# Kraus Representation from a System--Environment Unitary

The reduced channel uses Base partial trace, and the Kraus channel is
`MatrixMap.ofKraus`.
-/

@[expose] public section

namespace QITBench.KrausRepresentationSystemEnvironmentUnitary

open scoped BigOperators

noncomputable section

noncomputable def X : CMatrix (Fin 2) :=
  !![0, 1; 1, 0]

noncomputable def Y : CMatrix (Fin 2) :=
  !![0, -Complex.I; Complex.I, 0]

noncomputable def U : CMatrix (Fin 2 × Fin 2) :=
  let c : ℂ := (1 : ℂ) / (Real.sqrt 2 : ℂ)
  c • Matrix.kronecker X (1 : CMatrix (Fin 2)) +
    c • Matrix.kronecker Y X

noncomputable def envZeroProjector : CMatrix (Fin 2) :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

noncomputable def reducedChannel
    (rho : CMatrix (Fin 2)) :
    CMatrix (Fin 2) :=
  partialTraceB (a := Fin 2) (b := Fin 2)
    (U * Matrix.kronecker rho envZeroProjector * U.conjTranspose)

noncomputable def krausOperator (k : Fin 2) :
    CMatrix (Fin 2) :=
  fun i j => U (i, k) (j, 0)

noncomputable def krausChannel : MatrixMap (Fin 2) (Fin 2) :=
  MatrixMap.ofKraus krausOperator

end

end QITBench.KrausRepresentationSystemEnvironmentUnitary
