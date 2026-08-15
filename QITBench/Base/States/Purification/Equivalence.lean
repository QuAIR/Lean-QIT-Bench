/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.States.Purification.Gram
public import QITBench.Base.States.Purification.GramFactorization

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u v w

noncomputable section

namespace PureVector

variable {a : Type u}
variable [Fintype a] [DecidableEq a]

theorem ext_amp {Ψ Φ : PureVector a} (h : Ψ.amp = Φ.amp) : Ψ = Φ := by
  cases Ψ
  cases Φ
  simp only at h
  subst h
  simp

variable {r₁ : Type u} {r₂ : Type v} {a : Type w}
variable [Fintype r₁] [DecidableEq r₁]
variable [Fintype r₂] [DecidableEq r₂]
variable [Fintype a] [DecidableEq a]

theorem exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
    {Ψ : PureVector (Prod r₁ a)} {Φ : PureVector (Prod r₂ a)} {ρ : State a}
    (hΨ : Ψ.Purifies ρ) (hΦ : Φ.Purifies ρ)
    (hcard : Fintype.card r₁ ≤ Fintype.card r₂) :
    ∃ V : ReferenceIsometry r₁ r₂, Φ = V.applyPureVector Ψ := by
  have hGram :=
    amplitudeMatrix_mul_conjTranspose_eq_of_purifies_same_state hΨ hΦ
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      Ψ.amplitudeMatrix Φ.amplitudeMatrix hGram hcard
  refine ⟨V, ?_⟩
  apply ext_amp
  funext p
  have hp := congrFun (congrFun hV p.2) p.1
  simpa [amplitudeMatrix, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mul_apply, Matrix.transpose,
    Matrix.mulVec, dotProduct, mul_comm] using hp

end PureVector

end

end QITBench
