module

public import QITBench.Base

/-!
# Trace-Distance Data Processing for Quantum Channels

Complete positivity and trace preservation are carried by the `Channel` type.
Trace distance uses the concrete finite-dimensional trace norm.
-/

@[expose] public section

namespace QITBench.TraceDistanceDataProcessingQuantumChannels

open scoped ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : CMatrix d :=
  CFC.sqrt A

noncomputable def traceNorm
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (d := d) (A.conjTranspose * A)))

noncomputable def traceDistance
    {d : Type*} [Fintype d] [DecidableEq d]
    (rho sigma : CMatrix d) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (rho - sigma)

end

end QITBench.TraceDistanceDataProcessingQuantumChannels
