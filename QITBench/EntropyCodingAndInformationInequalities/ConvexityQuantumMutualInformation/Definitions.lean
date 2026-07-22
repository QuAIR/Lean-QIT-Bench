module

public import QITBench.Base

/-!
# Convexity of Quantum Mutual Information

Partial traces are taken from `QITBench.Base`. Entropy is the concrete spectral
von Neumann entropy on positive semidefinite matrices, so the theorem no longer
takes witness hypotheses that simply assert non-convexity/non-concavity.
-/

@[expose] public section

namespace QITBench.ConvexityQuantumMutualInformation

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

noncomputable def convexCombination {d : Type*}
    (t : ℝ) (rho sigma : CMatrix d) : CMatrix d :=
  ((t : ℂ) • rho) + (((1 - t : ℝ) : ℂ) • sigma)

def ConvexOnDensity {d : Type*} [Fintype d] [DecidableEq d]
    (F : CMatrix d → ℝ) : Prop :=
  ∀ (rho sigma : State d) (t : ℝ),
    0 ≤ t →
      t ≤ 1 →
        F (convexCombination t rho.matrix sigma.matrix) ≤
          t * F rho.matrix + (1 - t) * F sigma.matrix

def ConcaveOnDensity {d : Type*} [Fintype d] [DecidableEq d]
    (F : CMatrix d → ℝ) : Prop :=
  ∀ (rho sigma : State d) (t : ℝ),
    0 ≤ t →
      t ≤ 1 →
        t * F rho.matrix + (1 - t) * F sigma.matrix ≤
          F (convexCombination t rho.matrix sigma.matrix)

noncomputable def conditionalEntropy
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : CMatrix (a × b)) : ℝ :=
  vonNeumannEntropyMatrix rhoAB - vonNeumannEntropyMatrix (partialTraceA rhoAB)

noncomputable def mutualInformation
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rhoAB : CMatrix (a × b)) : ℝ :=
  vonNeumannEntropyMatrix (partialTraceB rhoAB) +
    vonNeumannEntropyMatrix (partialTraceA rhoAB) -
      vonNeumannEntropyMatrix rhoAB

end

end QITBench.ConvexityQuantumMutualInformation
