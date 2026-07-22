module

public import QITBench.Base

/-!
# Trace-Norm Unitary Optimization

The trace norm is the concrete finite-dimensional `Tr |A|`, with `|A|` defined
by matrix CFC square root of `A†A`; unitarity is kept as a problem-local matrix
predicate.
-/

@[expose] public section

namespace QITBench.TraceNormUnitaryOptimization

open scoped ComplexOrder MatrixOrder

noncomputable section

def IsUnitaryMatrix
    {n : ℕ}
    (U : CMatrix (Fin n)) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  CFC.sqrt A

noncomputable def matrixAbs
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  matrixSqrt (A.conjTranspose * A)

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixAbs A))

end

end QITBench.TraceNormUnitaryOptimization
