/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Channel

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix

namespace QITBench

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {x : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype x] [DecidableEq x]

def measureSubsystemState (M : POVM x a) (ρ : State (Prod a b)) :
    State (Prod x b) :=
  (Channel.prod (Channel.measure M) (Channel.idChannel b)).applyState ρ

def measurementMapDoesNotEnlargeUnit (M : POVM x a) : Prop :=
  (Channel.measure M).map (1 : CMatrix a) ≤ (1 : CMatrix x)

end

end QITBench
