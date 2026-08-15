/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Information.Renyi.Renyi

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QITBench

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace State

def conditionalSandwichedRenyiCandidate (ρ : State (Prod a b)) (_hρ : ρ.matrix.PosDef)
    (σ : State b) (_hσ : σ.matrix.PosDef) (α : ℝ) (_hα_pos : 0 < α)
    (_hα_ne_one : α ≠ 1) : ℝ :=
  let r := -(1 / (α - 1))
  let s := (1 - α) / (2 * α)
  let τ : CMatrix (Prod a b) := identityTensorStateMatrix (a := a) σ
  let M := CFC.rpow (CFC.rpow τ s * ρ.matrix * CFC.rpow τ s) α
  r * log2 M.trace.re

def conditionalSandwichedRenyiValueSet (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Set ℝ :=
  {h | ∃ σ : State b, ∃ hσ : σ.matrix.PosDef,
    h = conditionalSandwichedRenyiCandidate ρ hρ σ hσ α (by linarith) hα_ne_one}

@[simp]
theorem conditionalSandwichedRenyiValueSet_eq
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one =
      {h | ∃ σ : State b, ∃ hσ : σ.matrix.PosDef,
        h = conditionalSandwichedRenyiCandidate ρ hρ σ hσ α
          (by linarith) hα_ne_one} :=
  rfl

def conditionalSandwichedRenyi (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : ℝ :=
  sSup (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one)

@[simp]
theorem conditionalSandwichedRenyi_eq (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one =
      sSup (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one) :=
  rfl

theorem conditionalSandwichedRenyiCandidate_mem_valueSet
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ∈
      ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one :=
  ⟨σ, hσ, rfl⟩

theorem conditionalSandwichedRenyiValueSet_nonempty [Nonempty b]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) :
    (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one).Nonempty := by
  classical
  let u : b → ℝ≥0 := fun _ => (Fintype.card b : ℝ≥0)⁻¹
  have husum : ∑ i, u i = 1 := by
    simp [u, Finset.sum_const, Fintype.card_ne_zero]
  have hupos : ∀ i, 0 < (u i : ℝ) := by
    intro i
    have hcard_pos : 0 < (Fintype.card b : ℝ≥0) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
    exact_mod_cast inv_pos.mpr hcard_pos
  let σ : State b := Classical.diagonalState u husum
  have hσ : σ.matrix.PosDef := by
    simpa [σ] using Classical.diagonalState_posDef u husum hupos
  exact ⟨ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one,
    ρ.conditionalSandwichedRenyiCandidate_mem_valueSet hρ σ hσ α hα hα_ne_one⟩

theorem conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    {C : ℝ}
    (hC : ∀ σ : State b, ∀ hσ : σ.matrix.PosDef,
      ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ≤ C) :
    BddAbove (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one) := by
  refine ⟨C, ?_⟩
  intro x hx
  rcases hx with ⟨σ, hσ, rfl⟩
  exact hC σ hσ

theorem conditionalSandwichedRenyiCandidate_le_conditionalSandwichedRenyi_of_bddAbove
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hbdd : BddAbove (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one)) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ≤
      ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one := by
  rw [conditionalSandwichedRenyi_eq]
  exact le_csSup hbdd
    (ρ.conditionalSandwichedRenyiCandidate_mem_valueSet hρ σ hσ α hα hα_ne_one)

theorem conditionalSandwichedRenyi_le_of_forall_candidate_le [Nonempty b]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    {C : ℝ}
    (hC : ∀ σ : State b, ∀ hσ : σ.matrix.PosDef,
      ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α (by linarith) hα_ne_one ≤ C) :
    ρ.conditionalSandwichedRenyi hρ α hα hα_ne_one ≤ C := by
  rw [conditionalSandwichedRenyi_eq]
  refine csSup_le (ρ.conditionalSandwichedRenyiValueSet_nonempty hρ α hα hα_ne_one) ?_
  intro x hx
  rcases hx with ⟨σ, hσ, rfl⟩
  exact hC σ hσ

end State

end

end QITBench
