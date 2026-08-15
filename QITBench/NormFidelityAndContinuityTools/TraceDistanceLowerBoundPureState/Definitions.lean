/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity

@[expose] public section

namespace QITBench.TraceDistanceLowerBoundPureState

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  Fidelity.matrixSqrt A

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Fidelity.traceNorm A

noncomputable def quadraticForm
    {n : ℕ}
    (A : CMatrix (Fin n))
    (x : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (x i) * A i j * x j

noncomputable def traceDistance
    {n : ℕ}
    (rho sigma : CMatrix (Fin n)) : ℝ :=
  Fidelity.traceDistance rho sigma

noncomputable def pureStateFidelity
    {n : ℕ}
    (psi : PureVector (Fin n))
    (sigma : State (Fin n)) : ℝ :=
  Real.sqrt (Complex.re (quadraticForm sigma.matrix psi.amp))

end

end QITBench.TraceDistanceLowerBoundPureState
