/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.States.Purification.ReferenceIsometry
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u v

noncomputable section

structure ReferenceUnitary (r : Type u) [Fintype r] [DecidableEq r] where
  matrix : Matrix.unitaryGroup r Complex

namespace ReferenceUnitary

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r]

variable (U : ReferenceUnitary r)

def matrixCoe : Matrix r r Complex :=
  U.matrix

def toReferenceIsometry : ReferenceIsometry r r where
  matrix := U.matrix
  isometry := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U.matrix

variable [Fintype a] [DecidableEq a]

def applyPureVector (Ψ : PureVector (Prod r a)) : PureVector (Prod r a) :=
  U.toReferenceIsometry.applyPureVector Ψ

theorem applyPureVector_eq_referenceIsometry (Ψ : PureVector (Prod r a)) :
    U.applyPureVector Ψ = U.toReferenceIsometry.applyPureVector Ψ :=
  rfl

theorem applyPureVector_amp (Ψ : PureVector (Prod r a)) :
    (U.applyPureVector Ψ).amp = U.toReferenceIsometry.applyAmp Ψ.amp :=
  rfl

end ReferenceUnitary

namespace PureVector

variable {a : Type u}
variable [Fintype a] [DecidableEq a]

def overlap (Ψ Φ : PureVector a) : ℂ :=
  ∑ i, star (Ψ.amp i) * Φ.amp i

def overlapSq (Ψ Φ : PureVector a) : ℝ :=
  Complex.normSq (Ψ.overlap Φ)

theorem overlap_eq_sum (Ψ Φ : PureVector a) :
    Ψ.overlap Φ = ∑ i, star (Ψ.amp i) * Φ.amp i :=
  rfl

theorem overlapSq_eq_normSq (Ψ Φ : PureVector a) :
    Ψ.overlapSq Φ = Complex.normSq (Ψ.overlap Φ) :=
  rfl

theorem overlapSq_nonneg (Ψ Φ : PureVector a) :
    0 ≤ Ψ.overlapSq Φ :=
  Complex.normSq_nonneg _

end PureVector

end

end QITBench
