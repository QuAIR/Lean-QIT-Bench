/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.UniversalUpperBoundAlbertiSTheorem

open scoped ComplexOrder MatrixOrder

noncomputable section

def IsPositiveOperator
    {n : ℕ}
    (A : CMatrix (Fin n)) : Prop :=
  A.PosSemidef

def IsMatrixInverse
    {n : ℕ}
    (P Pinv : CMatrix (Fin n)) : Prop :=
  P * Pinv = 1 ∧ Pinv * P = 1

def IsPositiveInvertibleOperator
    {n : ℕ}
    (P Pinv : CMatrix (Fin n)) : Prop :=
  IsPositiveOperator P ∧ IsMatrixInverse P Pinv

noncomputable def albertiObjective
    {n : ℕ}
    (rho sigma : State (Fin n))
    (P Pinv : CMatrix (Fin n)) : ℝ :=
  Complex.re (Matrix.trace (rho.matrix * P)) *
    Complex.re (Matrix.trace (sigma.matrix * Pinv))

noncomputable def albertiValues
    {n : ℕ}
    (rho sigma : State (Fin n)) : Set ℝ :=
  {x | ∃ P Pinv : CMatrix (Fin n),
    IsPositiveInvertibleOperator P Pinv ∧
      x = albertiObjective rho sigma P Pinv}

end

end QITBench.UniversalUpperBoundAlbertiSTheorem
