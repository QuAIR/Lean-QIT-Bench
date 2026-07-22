module

public import QITBench.Base

/-!
# Alberti's Theorem, Commuting Case

For commuting states, Alberti's variational fidelity reduces to the classical
fidelity of their common diagonal probability weights.
-/

@[expose] public section

namespace QITBench.AlbertiSTheoremCommutingCase

open scoped BigOperators

noncomputable section

noncomputable def albertiDiagonalObjective
    {ι : Type*} [Fintype ι]
    (rhoWeights sigmaWeights p : ι → ℝ) : ℝ :=
  (∑ i, rhoWeights i * p i) *
    (∑ i, sigmaWeights i * (p i)⁻¹)

noncomputable def albertiDiagonalValues
    {ι : Type*} [Fintype ι]
    (rhoWeights sigmaWeights : ι → ℝ) : Set ℝ :=
  {x | ∃ p : ι → ℝ,
    (∀ i, 0 < p i) ∧
      x = albertiDiagonalObjective rhoWeights sigmaWeights p}

noncomputable def classicalFidelity
    {ι : Type*} [Fintype ι]
    (rhoWeights sigmaWeights : ι → ℝ) : ℝ :=
  ∑ i, Real.sqrt (rhoWeights i * sigmaWeights i)

def HasAlbertiVariationalFidelity
    {ι : Type*} [Fintype ι]
    (F : ℝ)
    (rhoWeights sigmaWeights : ι → ℝ) : Prop :=
  0 ≤ F ∧ F ^ 2 = sInf (albertiDiagonalValues rhoWeights sigmaWeights)

end

end QITBench.AlbertiSTheoremCommutingCase
