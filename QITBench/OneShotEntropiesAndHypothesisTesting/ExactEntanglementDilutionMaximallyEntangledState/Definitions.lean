/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.OneShot

@[expose] public section

namespace QITBench.ExactEntanglementDilutionMaximallyEntangledState

def SchmidtCoefficientsSorted
    {d : ℕ}
    (mu : Fin d → ℝ) : Prop :=
  ∀ i j : Fin d, (i : ℕ) ≤ (j : ℕ) → mu j ≤ mu i

def IsSchmidtProbabilityVector
    {d : ℕ}
    (mu : Fin d → ℝ) : Prop :=
  SchmidtCoefficientsSorted mu ∧
    (∀ i, 0 < mu i) ∧
      (∑ i, mu i) = 1

def largestSchmidtCoefficient
    {d : ℕ}
    (mu : Fin d → ℝ) (hd : 0 < d) : ℝ :=
  mu ⟨0, hd⟩

noncomputable def maximallyEntangledSchmidtCoefficients
    {d : ℕ}
    (M : ℕ) : Fin d → ℝ :=
  fun i => if (i : ℕ) < M then (1 : ℝ) / (M : ℝ) else 0

noncomputable def sumFirst
    {d : ℕ}
    (k : ℕ) (v : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, if (i : ℕ) < k then v i else 0

def MajorizedBy
    {d : ℕ}
    (p q : Fin d → ℝ) : Prop :=
  (∀ k : ℕ, k ≤ d → sumFirst k p ≤ sumFirst k q) ∧
    (∑ i, p i) = ∑ i, q i

noncomputable def CanTransformDeterministicallyBySEP
    {d : ℕ}
    (mu : Fin d → ℝ) (M : ℕ) : Prop :=
  IsSchmidtProbabilityVector mu ∧
    0 < M ∧
      M ≤ d ∧
        MajorizedBy mu (maximallyEntangledSchmidtCoefficients (d := d) M)

end QITBench.ExactEntanglementDilutionMaximallyEntangledState

namespace QITBench.ExactEntanglementDilutionMaximallyEntangledState

open QITBench.OneShot

noncomputable section

end

end QITBench.ExactEntanglementDilutionMaximallyEntangledState
