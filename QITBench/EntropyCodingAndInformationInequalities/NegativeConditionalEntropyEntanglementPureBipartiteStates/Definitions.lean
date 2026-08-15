/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.NegativeConditionalEntropyEntanglementPureBipartiteStates

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

noncomputable def vonNeumannEntropyMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (rho : CMatrix d) : ℝ := by
  classical
  exact if h : rho.PosSemidef then
    -∑ i : d, h.1.eigenvalues i * log2 (h.1.eigenvalues i)
  else
    0

def IsProductVector {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (psi : PureVector (a × b)) : Prop :=
  ∃ (alpha : a → ℂ) (beta : b → ℂ),
    ∀ p : a × b, psi.amp p = alpha p.1 * beta p.2

def IsEntangledPureState {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (psi : PureVector (a × b)) : Prop :=
  ¬ IsProductVector psi

noncomputable def conditionalEntropyBGivenA
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : CMatrix (a × b)) : ℝ :=
  vonNeumannEntropyMatrix rhoAB - vonNeumannEntropyMatrix (partialTraceB rhoAB)

end

end QITBench.NegativeConditionalEntropyEntanglementPureBipartiteStates
