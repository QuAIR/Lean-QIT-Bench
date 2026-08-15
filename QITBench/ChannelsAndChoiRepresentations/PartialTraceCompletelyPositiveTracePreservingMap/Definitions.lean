/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.PartialTraceCompletelyPositiveTracePreservingMap

noncomputable section

noncomputable def partialTraceBMap {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    MatrixMap (a × b) a where
  toFun := partialTraceB (a := a) (b := b)
  map_add' X Y := by
    ext i i'
    simp [partialTraceB, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i i'
    simp only [partialTraceB, Matrix.smul_apply, smul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm

noncomputable def partialTraceBKraus {a b : Type*}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (k : b) :
    Matrix a (a × b) ℂ :=
  fun i p => if p.1 = i ∧ p.2 = k then 1 else 0

end

end QITBench.PartialTraceCompletelyPositiveTracePreservingMap
