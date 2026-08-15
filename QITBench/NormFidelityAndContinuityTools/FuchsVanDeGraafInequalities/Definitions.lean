/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity

@[expose] public section

namespace QITBench.FuchsVanDeGraafInequalities

open scoped ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  Fidelity.matrixSqrt A

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Fidelity.traceNorm A

noncomputable def traceDistance
    {n : ℕ}
    (rho sigma : CMatrix (Fin n)) : ℝ :=
  Fidelity.traceDistance rho sigma

noncomputable def unsquaredFidelity
    {n : ℕ}
    (rho sigma : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (matrixSqrt rho * sigma * matrixSqrt rho)))

end

end QITBench.FuchsVanDeGraafInequalities
