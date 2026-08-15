/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.OneShot

@[expose] public section

namespace QITBench.AchievabilityEntanglementConcentration

noncomputable def targetRankAtRate (R : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.rpow (2 : ℝ) ((n : ℝ) * R))

end QITBench.AchievabilityEntanglementConcentration

namespace QITBench.AchievabilityEntanglementConcentration

open scoped BigOperators
open QITBench.OneShot

noncomputable section

end

end QITBench.AchievabilityEntanglementConcentration
