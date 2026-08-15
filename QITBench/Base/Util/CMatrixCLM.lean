/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Util.Matrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

open scoped ComplexOrder
open Matrix

namespace QITBench

universe u

noncomputable section

noncomputable def cMatrixEntryCLM {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℝ] ℂ)

noncomputable def cMatrixEntryCLM_complex {ι : Type u} [Fintype ι] [DecidableEq ι]
    (i j : ι) : CMatrix ι →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A i j
       map_add' := by
        intro A B
        rfl
       map_smul' := by
        intro c A
        simp [Matrix.smul_apply] } :
      CMatrix ι →ₗ[ℂ] ℂ)

noncomputable def cMatrixConjTransposeCLM {ι : Type u} [Fintype ι] [DecidableEq ι] :
    CMatrix ι →L[ℝ] CMatrix ι :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun A => A.conjTranspose
       map_add' := by
        intro A B
        rw [Matrix.conjTranspose_add]
       map_smul' := by
        intro c A
        rw [Matrix.conjTranspose_smul]
        simp } :
      CMatrix ι →ₗ[ℝ] CMatrix ι)

noncomputable def cMatrixQuadraticCLM {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) : CMatrix ι →L[ℂ] ℂ :=
  ∑ i, ∑ j, (star (x i) * x j) • cMatrixEntryCLM_complex (ι := ι) i j

theorem cMatrixQuadraticCLM_apply {ι : Type u} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (A : CMatrix ι) :
    cMatrixQuadraticCLM x A = dotProduct (star x) (Matrix.mulVec A x) := by
  simp [cMatrixQuadraticCLM, cMatrixEntryCLM_complex, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

end

end QITBench
