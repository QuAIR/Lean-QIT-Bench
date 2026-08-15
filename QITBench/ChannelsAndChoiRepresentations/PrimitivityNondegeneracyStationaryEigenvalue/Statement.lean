/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.ChannelsAndChoiRepresentations.PrimitivityNondegeneracyStationaryEigenvalue.Definitions
@[expose] public section

namespace QITBench.PrimitivityNondegeneracyStationaryEigenvalue

open scoped BigOperators ComplexOrder MatrixOrder ComplexStarModule

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (E : Channel d d) :
    IsPrimitive E →
      EigenvalueOneNondegenerate E := by
  sorry

end

end QITBench.PrimitivityNondegeneracyStationaryEigenvalue
