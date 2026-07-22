module

public import QITBench.Base

/-!
# Spectrum and Entropy of a Single-Qubit Source

The entropy claim is now about the concrete spectral von Neumann entropy of the
matrix `rho`; it is no longer an `rfl` unfolding of a function that already
contains the desired formula.
-/

@[expose] public section

namespace QITBench.SpectrumEntropySingleQubitSource

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def rho : CMatrix (Fin 2) :=
  ((1 / 4 : ℂ) • !![3, 1; 1, 1])

noncomputable def lambdaPlus : ℝ :=
  (2 + Real.sqrt 2) / 4

noncomputable def lambdaMinus : ℝ :=
  (2 - Real.sqrt 2) / 4

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

noncomputable def matrixVectorMul
    (M : CMatrix (Fin 2)) (v : Fin 2 → ℂ) :
    Fin 2 → ℂ :=
  fun i => ∑ j : Fin 2, M i j * v j

def HasEigenvalue
    (M : CMatrix (Fin 2)) (lam : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ,
    v ≠ 0 ∧ matrixVectorMul M v = fun i => lam * v i

/-- Spectral von Neumann entropy for a positive semidefinite two-by-two matrix. -/
noncomputable def vonNeumannEntropy (M : CMatrix (Fin 2)) : ℝ := by
  classical
  exact if h : M.PosSemidef then
    -∑ i : Fin 2, h.1.eigenvalues i * log2 (h.1.eigenvalues i)
  else
    0

end

end QITBench.SpectrumEntropySingleQubitSource
