/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Information.Renyi.ConditionalRenyi

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QITBench

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State
namespace RenyiDPI
namespace Statement

def sandwichedRenyi_dataProcessing_channel_statement (ρ σ : State a) (Φ : Channel a b)
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (hρΦ : (Φ.applyState ρ).matrix.PosDef) (hσΦ : (Φ.applyState σ).matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1) : Prop :=
  sandwichedRenyi (Φ.applyState ρ) (Φ.applyState σ) hρΦ hσΦ α (by linarith) hα_ne_one ≤
    sandwichedRenyi ρ σ hρ hσ α (by linarith) hα_ne_one

end Statement
end RenyiDPI
end State

end

end QITBench
