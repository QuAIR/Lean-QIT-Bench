/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Pure

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u v

noncomputable section

namespace PureVector

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

def Purifies (Ψ : PureVector (Prod r a)) (ρ : State a) : Prop :=
  partialTraceA (a := r) (b := a) Ψ.state.matrix = ρ.matrix

@[simp]
theorem purifies_iff (Ψ : PureVector (Prod r a)) (ρ : State a) :
    Ψ.Purifies ρ ↔
      partialTraceA (a := r) (b := a) Ψ.state.matrix = ρ.matrix :=
  Iff.rfl

theorem partialTraceA_state_matrix_eq_of_purifies
    {Ψ : PureVector (Prod r a)} {ρ : State a} (h : Ψ.Purifies ρ) :
    partialTraceA (a := r) (b := a) Ψ.state.matrix = ρ.matrix :=
  h

theorem reindex_prodComm_purifies_marginalA (Ψ : PureVector (Prod r a)) :
    (Ψ.reindex (Equiv.prodComm r a)).Purifies Ψ.state.marginalA := by
  rw [purifies_iff]
  ext i j
  simp [PureVector.reindex_state, State.reindex, State.marginalA, partialTraceA,
    partialTraceB, PureVector.state_matrix, rankOneMatrix_apply]

end PureVector

end

end QITBench
