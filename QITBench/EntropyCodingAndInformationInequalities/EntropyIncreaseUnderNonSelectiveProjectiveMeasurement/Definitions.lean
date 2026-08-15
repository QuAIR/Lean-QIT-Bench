/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

noncomputable def vonNeumannEntropyMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (rho : CMatrix d) : ℝ := by
  classical
  exact if h : rho.PosSemidef then
    -∑ i : d, h.1.eigenvalues i * log2 (h.1.eigenvalues i)
  else
    0

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

noncomputable def convexCombination {d : Type*}
    (t : ℝ) (rho sigma : CMatrix d) : CMatrix d :=
  ((t : ℂ) • rho) + (((1 - t : ℝ) : ℂ) • sigma)

def HasRandomUnitaryRepresentation
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : CMatrix d) : Prop :=
  IsUnitaryMatrix (phaseFlipUnitaryFromProjector P) ∧
    ∀ rho : State d,
      nonSelectiveProjectiveMeasurement P rho.matrix =
        convexCombination (1 / 2) rho.matrix
          (phaseFlipUnitaryFromProjector P * rho.matrix *
            (phaseFlipUnitaryFromProjector P).conjTranspose)

end

end QITBench.EntropyIncreaseUnderNonSelectiveProjectiveMeasurement
