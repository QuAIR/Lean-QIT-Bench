module

public import QITBench.EntropyCodingAndInformationInequalities.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement.Definitions

@[expose] public section

namespace QITBench.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d)
    (hP : IsOrthogonalProjector P)
    (h_random : HasRandomUnitaryRepresentation P) :
    ∀ rho : State d,
      vonNeumannEntropyMatrix rho.matrix ≤
        vonNeumannEntropyMatrix (nonSelectiveProjectiveMeasurement P rho.matrix) := by
  sorry

end

end QITBench.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement
