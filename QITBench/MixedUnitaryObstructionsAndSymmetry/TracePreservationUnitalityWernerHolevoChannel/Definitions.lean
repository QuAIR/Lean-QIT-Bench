/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.TracePreservationUnitalityWernerHolevoChannel

noncomputable section

noncomputable def wernerHolevoFormula
    (X : CMatrix (Fin 3)) : CMatrix (Fin 3) :=
  ((1 / 2 : ℂ) • ((Matrix.trace X) • (1 : CMatrix (Fin 3)) - X.transpose))

noncomputable def wernerHolevoChannel : MatrixMap (Fin 3) (Fin 3) where
  toFun := wernerHolevoFormula
  map_add' X Y := by
    ext i j
    simp [wernerHolevoFormula, Matrix.trace_add, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm]
  map_smul' c X := by
    ext i j
    simp [wernerHolevoFormula, Matrix.trace_smul, sub_eq_add_neg,
      mul_comm, mul_assoc]
    ring

end

end QITBench.TracePreservationUnitalityWernerHolevoChannel
