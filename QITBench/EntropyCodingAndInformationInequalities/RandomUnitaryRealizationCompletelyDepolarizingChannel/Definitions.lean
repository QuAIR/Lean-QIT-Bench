/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.RandomUnitaryRealizationCompletelyDepolarizingChannel

open scoped BigOperators

noncomputable section

def IsUnitaryMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (U : CMatrix d) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

def IsUnital {d : Type*} [Fintype d] [DecidableEq d]
    (E : CMatrix d → CMatrix d) : Prop :=
  E (1 : CMatrix d) = 1

def UniformRandomUnitaryDepolarizes
    {d : Type*} [Fintype d] [DecidableEq d]
    (D : ℕ)
    (U : Fin (D ^ 2) → CMatrix d) : Prop :=
  (∀ i : Fin (D ^ 2), IsUnitaryMatrix (U i)) ∧
    ∀ A : CMatrix d,
      ((1 / ((D ^ 2 : ℕ) : ℂ)) •
          (∑ i : Fin (D ^ 2), U i * A * (U i).conjTranspose)) =
        Matrix.trace A •
          ((1 / (D : ℂ)) • (1 : CMatrix d))

end

end QITBench.RandomUnitaryRealizationCompletelyDepolarizingChannel
