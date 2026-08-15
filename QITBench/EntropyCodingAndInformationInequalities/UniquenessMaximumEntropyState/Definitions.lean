/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.UniquenessMaximumEntropyState

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

noncomputable def maximallyMixed {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ) : CMatrix d :=
  ((1 / (D : ℂ)) • (1 : CMatrix d))

noncomputable def vonNeumannEntropyMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (rho : CMatrix d) : ℝ := by
  classical
  exact if h : rho.PosSemidef then
    -∑ i : d, h.1.eigenvalues i * log2 (h.1.eigenvalues i)
  else
    0

def IsUnitaryMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (U : CMatrix d) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

def RandomUnitaryIdentity
    {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ)
    (U : Fin (D ^ 2) → CMatrix d) : Prop :=
  (∀ i : Fin (D ^ 2), IsUnitaryMatrix (U i)) ∧
    ∀ rho : State d,
      ((1 / ((D ^ 2 : ℕ) : ℂ)) •
          (∑ i : Fin (D ^ 2), U i * rho.matrix * (U i).conjTranspose)) =
        maximallyMixed D

def EntropyUniquelyMaximizedAtMixed
    {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ) : Prop :=
  vonNeumannEntropyMatrix (maximallyMixed (d := d) D) = log2 (D : ℝ) ∧
    ∀ rho : State d,
      vonNeumannEntropyMatrix rho.matrix = log2 (D : ℝ) →
        rho.matrix = maximallyMixed D

end

end QITBench.UniquenessMaximumEntropyState
