/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.NormFidelityAndContinuityTools.UniversalUpperBoundAlbertiSTheorem.Definitions
@[expose] public section

namespace QITBench.UniversalUpperBoundAlbertiSTheorem

open scoped ComplexOrder MatrixOrder

noncomputable section

theorem main
    {n : ℕ}
    (rho sigma : State (Fin n))
    (P Pinv : CMatrix (Fin n))
    (F : ℝ)
    (hF_nonneg : 0 ≤ F)
    (hAlberti : F ^ 2 = sInf (albertiValues rho sigma))
    (hP : IsPositiveInvertibleOperator P Pinv) :
    F ^ 2 ≤ albertiObjective rho sigma P Pinv ∧
      F ≤ Real.sqrt (albertiObjective rho sigma P Pinv) := by
  sorry

end

end QITBench.UniversalUpperBoundAlbertiSTheorem
