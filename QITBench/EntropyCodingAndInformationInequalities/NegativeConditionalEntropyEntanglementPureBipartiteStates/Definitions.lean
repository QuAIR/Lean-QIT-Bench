module

public import QITBench.Base

/-!
# Negative Conditional Entropy and Pure-State Entanglement

The entropy terms are concrete spectral von Neumann entropies.  The previous
statement assumed the two physical facts that make the equivalence true; those
facts are now part of the proof obligation.
-/

@[expose] public section

namespace QITBench.NegativeConditionalEntropyEntanglementPureBipartiteStates

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Spectral von Neumann entropy, zero outside the PSD cone. -/
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
