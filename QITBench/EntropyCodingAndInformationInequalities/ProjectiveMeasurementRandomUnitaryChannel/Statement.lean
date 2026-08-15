/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.EntropyCodingAndInformationInequalities.ProjectiveMeasurementRandomUnitaryChannel.Definitions
@[expose] public section

namespace QITBench.ProjectiveMeasurementRandomUnitaryChannel

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d)
    (_hP : IsOrthogonalProjector P) :
    HasTwoUnitaryRandomRepresentation P := by
  sorry

end

end QITBench.ProjectiveMeasurementRandomUnitaryChannel
