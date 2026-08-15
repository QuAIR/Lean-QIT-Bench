/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity

@[expose] public section

namespace QITBench.TraceDistanceDataProcessingQuantumChannels

open scoped ComplexOrder MatrixOrder

noncomputable section

noncomputable def matrixSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : CMatrix d :=
  Fidelity.matrixSqrt A

noncomputable def traceNorm
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : ℝ :=
  Fidelity.traceNorm A

noncomputable def traceDistance
    {d : Type*} [Fintype d] [DecidableEq d]
    (rho sigma : CMatrix d) : ℝ :=
  Fidelity.traceDistance rho sigma

end

end QITBench.TraceDistanceDataProcessingQuantumChannels
