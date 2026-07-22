module

public import QITBench.Base

/-!
# Trace-Distance Lower Bound for a Pure State

The pure state is represented by `PureVector`; the density matrix `|ψ⟩⟨ψ|` is
`psi.state.matrix`, backed by the Base `rankOneMatrix` construction. Trace
distance uses the concrete finite-dimensional trace norm.
-/

@[expose] public section

namespace QITBench.TraceDistanceLowerBoundPureState

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {n : ℕ}
    (A : CMatrix (Fin n)) : CMatrix (Fin n) :=
  CFC.sqrt A

noncomputable def traceNorm
    {n : ℕ}
    (A : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (A.conjTranspose * A)))

noncomputable def quadraticForm
    {n : ℕ}
    (A : CMatrix (Fin n))
    (x : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (x i) * A i j * x j

noncomputable def traceDistance
    {n : ℕ}
    (rho sigma : CMatrix (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (rho - sigma)

noncomputable def pureStateFidelity
    {n : ℕ}
    (psi : PureVector (Fin n))
    (sigma : State (Fin n)) : ℝ :=
  Real.sqrt (Complex.re (quadraticForm sigma.matrix psi.amp))

end

end QITBench.TraceDistanceLowerBoundPureState
