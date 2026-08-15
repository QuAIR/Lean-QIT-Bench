/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder

namespace QITBench.Fidelity

noncomputable section

noncomputable def matrixSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : CMatrix d :=
  CFC.sqrt A

noncomputable def traceNorm
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : CMatrix d) : ℝ :=
  Complex.re (Matrix.trace (matrixSqrt (A.conjTranspose * A)))

noncomputable def traceDistance
    {d : Type*} [Fintype d] [DecidableEq d]
    (rho sigma : CMatrix d) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (rho - sigma)

noncomputable def quadraticForm
    {d : Type*} [Fintype d]
    (A : CMatrix d) (x : d → ℂ) : ℂ :=
  ∑ i, ∑ j, star (x i) * A i j * x j

noncomputable def pureStateFidelity
    {n : ℕ}
    (psi : PureVector (Fin n)) (sigma : State (Fin n)) : ℝ :=
  Real.sqrt (Complex.re (quadraticForm sigma.matrix psi.amp))

end

end QITBench.Fidelity
