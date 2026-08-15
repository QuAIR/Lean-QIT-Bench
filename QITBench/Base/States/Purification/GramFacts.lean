/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

namespace QITBench

noncomputable section

namespace LinearMap

variable {E₁ E₂ F : Type*}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₂]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

theorem adjoint_inner_adjoint_of_comp_adjoint_eq
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) (y z : F) :
    inner ℂ (T₁.adjoint y) (T₁.adjoint z) =
      inner ℂ (T₂.adjoint y) (T₂.adjoint z) := by
  calc
    inner ℂ (T₁.adjoint y) (T₁.adjoint z) = inner ℂ y (T₁ (T₁.adjoint z)) := by
      rw [LinearMap.adjoint_inner_left]
    _ = inner ℂ y ((T₁.comp T₁.adjoint) z) := rfl
    _ = inner ℂ y ((T₂.comp T₂.adjoint) z) := by rw [hGram]
    _ = inner ℂ y (T₂ (T₂.adjoint z)) := rfl
    _ = inner ℂ (T₂.adjoint y) (T₂.adjoint z) := by
      rw [LinearMap.adjoint_inner_left]

theorem ker_adjoint_eq_of_comp_adjoint_eq
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.ker T₁.adjoint = LinearMap.ker T₂.adjoint := by
  calc
    LinearMap.ker T₁.adjoint = LinearMap.ker (T₁.comp T₁.adjoint) := by
      rw [LinearMap.ker_self_comp_adjoint]
    _ = LinearMap.ker (T₂.comp T₂.adjoint) := by rw [hGram]
    _ = LinearMap.ker T₂.adjoint := by
      rw [LinearMap.ker_self_comp_adjoint]

theorem range_eq_of_comp_adjoint_eq
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint) :
    LinearMap.range T₁ = LinearMap.range T₂ := by
  calc
    LinearMap.range T₁ = LinearMap.range (T₁.comp T₁.adjoint) := by
      rw [LinearMap.range_self_comp_adjoint]
    _ = LinearMap.range (T₂.comp T₂.adjoint) := by rw [hGram]
    _ = LinearMap.range T₂ := by
      rw [LinearMap.range_self_comp_adjoint]

end LinearMap

end

end QITBench
