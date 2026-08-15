/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.EntropyCodingAndInformationInequalities.RandomUnitaryRealizationCompletelyDepolarizingChannel.Definitions
@[expose] public section

namespace QITBench.RandomUnitaryRealizationCompletelyDepolarizingChannel

open scoped BigOperators

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ)
    (_hD : Fintype.card d = D) :
    ∃ U : Fin (D ^ 2) → CMatrix d,
      UniformRandomUnitaryDepolarizes D U := by
  sorry

end

end QITBench.RandomUnitaryRealizationCompletelyDepolarizingChannel
