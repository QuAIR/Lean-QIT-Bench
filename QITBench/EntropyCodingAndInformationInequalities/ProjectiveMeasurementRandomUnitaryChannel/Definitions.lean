module

public import QITBench.Base

/-!
# Projective Measurement as a Random Unitary Channel

The random-unitary representation is quantified over bundled density `State`s.
-/

@[expose] public section

namespace QITBench.ProjectiveMeasurementRandomUnitaryChannel

noncomputable section

def IsOrthogonalProjector {d : Type*} [Fintype d]
    (P : CMatrix d) : Prop :=
  P.conjTranspose = P ∧ P * P = P

def IsUnitaryMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (U : CMatrix d) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

noncomputable def complementProjector {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d) : CMatrix d :=
  (1 : CMatrix d) - P

noncomputable def nonSelectiveProjectiveMeasurement
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d) (rho : CMatrix d) : CMatrix d :=
  let Q := complementProjector P
  P * rho * P + Q * rho * Q

noncomputable def phaseFlipUnitaryFromProjector
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d) : CMatrix d :=
  P - complementProjector P

def HasTwoUnitaryRandomRepresentation
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d) : Prop :=
  ∃ (U₁ U₂ : CMatrix d) (p : ℝ),
    IsUnitaryMatrix U₁ ∧
      IsUnitaryMatrix U₂ ∧
        0 ≤ p ∧
          p ≤ 1 ∧
            ∀ rho : State d,
              nonSelectiveProjectiveMeasurement P rho.matrix =
                ((p : ℂ) • (U₁ * rho.matrix * U₁.conjTranspose)) +
                  (((1 - p : ℝ) : ℂ) • (U₂ * rho.matrix * U₂.conjTranspose))

end

end QITBench.ProjectiveMeasurementRandomUnitaryChannel
