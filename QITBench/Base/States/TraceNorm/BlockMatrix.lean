/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.States.TraceNorm.Distance
public import QITBench.Base.Util.BlockMatrix

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

universe u v

noncomputable section

variable {α : Type u} {β : Type v}

theorem fromBlocks_diagonal_psdSqrt [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {D : Matrix β β ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    QITBench.psdSqrt (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ) =
      Matrix.fromBlocks (QITBench.psdSqrt A) 0 0 (QITBench.psdSqrt D) := by
  classical
  let S : Matrix (Sum α β) (Sum α β) ℂ :=
    Matrix.fromBlocks (QITBench.psdSqrt A) 0 0 (QITBench.psdSqrt D)
  have hSpos : S.PosSemidef := by
    dsimp [S]
    exact fromBlocks_diagonal_posSemidef (QITBench.psdSqrt_pos A) (QITBench.psdSqrt_pos D)
  have hSsq : S * S = (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ) := by
    dsimp [S]
    rw [Matrix.fromBlocks_multiply]
    simp [QITBench.psdSqrt_mul_self_of_posSemidef hA,
      QITBench.psdSqrt_mul_self_of_posSemidef hD]
  simpa [QITBench.psdSqrt, S] using
    (CFC.sqrt_unique (a := (Matrix.fromBlocks A 0 0 D : Matrix (Sum α β) (Sum α β) ℂ))
      (b := S) hSsq hSpos.nonneg)

theorem traceNorm_fromBlocks_diagonal [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    QITBench.traceNorm (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ) =
      QITBench.traceNorm X + QITBench.traceNorm Y := by
  classical
  have hgram :
      (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ)ᴴ *
          (Matrix.fromBlocks X 0 0 Y : Matrix (Sum α β) (Sum α β) ℂ) =
        Matrix.fromBlocks (Xᴴ * X) 0 0 (Yᴴ * Y) := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp
  rw [QITBench.traceNorm, hgram,
    fromBlocks_diagonal_psdSqrt (Matrix.posSemidef_conjTranspose_mul_self X)
      (Matrix.posSemidef_conjTranspose_mul_self Y),
    trace_fromBlocks_diagonal]
  simp [QITBench.traceNorm]

end

end Matrix
