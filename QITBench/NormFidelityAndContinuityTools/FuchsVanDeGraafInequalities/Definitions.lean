module

public import QITBench.Base

/-!
# Fuchs--van de Graaf Inequalities

The density-operator assumptions are represented by `State`. The trace norm
and square root are the concrete matrix-CFC versions used in finite dimension,
not arbitrary functions supplied by the theorem caller.
-/

@[expose] public section

namespace QITBench.FuchsVanDeGraafInequalities

open scoped ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  CFC.sqrt A

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (A.conjTranspose * A)))

noncomputable def traceDistance
    {n : ℕ}
    (rho sigma : CMatrix (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (rho - sigma)

noncomputable def unsquaredFidelity
    {n : ℕ}
    (rho sigma : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (matrixSqrt rho * sigma * matrixSqrt rho)))

end

end QITBench.FuchsVanDeGraafInequalities
