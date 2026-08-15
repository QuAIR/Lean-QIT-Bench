/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base
public import QITBench.Base.Util.SDP.HermitianPSDTraceDuality

@[expose] public section

namespace QITBench.HolevoBoundClassicalCapacityNQubits

universe u v

open scoped ComplexOrder NNReal

structure POVM (x : Type u) (a : Type v) [Fintype x] [Fintype a] [DecidableEq a] where
  effects : x → CMatrix a
  pos : ∀ y, (effects y).PosSemidef
  sum_eq_one : ∑ y, effects y = 1

namespace POVM

variable {x : Type u} {a : Type v}
variable [Fintype x] [Fintype a] [DecidableEq a]

noncomputable def prob (M : POVM x a) (rho : State a) (outcome : x) : ℝ≥0 :=
  ⟨Complex.re ((rho.matrix * M.effects outcome).trace),
    cMatrix_trace_mul_posSemidef_re_nonneg rho.pos (M.pos outcome)⟩

end POVM

end QITBench.HolevoBoundClassicalCapacityNQubits

namespace QITBench.HolevoBoundClassicalCapacityNQubits

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

abbrev NQubitBasis (n : ℕ) : Type :=
  Fin n → Fin 2

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

def IsProbabilityDistribution {ι : Type*} [Fintype ι]
    (p : ι → ℝ) : Prop :=
  (∀ x : ι, 0 ≤ p x) ∧ ∑ x : ι, p x = 1

noncomputable def vonNeumannEntropyMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (rho : CMatrix d) : ℝ := by
  classical
  exact if h : rho.PosSemidef then
    -∑ i : d, h.1.eigenvalues i * log2 (h.1.eigenvalues i)
  else
    0

noncomputable def averageStateMatrix {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (p : ι → ℝ) (rho : ι → State d) :
    CMatrix d :=
  ∑ x : ι, (p x : ℂ) • (rho x).matrix

noncomputable def jointProbability {ι y d : Type*}
    [Fintype ι] [Fintype y] [DecidableEq y] [Fintype d] [DecidableEq d]
    (p : ι → ℝ) (rho : ι → State d) (M : POVM y d) (x : ι) (outcome : y) : ℝ :=
  p x * (M.prob (rho x) outcome : ℝ)

noncomputable def outcomeProbability {ι y d : Type*}
    [Fintype ι] [Fintype y] [DecidableEq y] [Fintype d] [DecidableEq d]
    (p : ι → ℝ) (rho : ι → State d) (M : POVM y d) (outcome : y) : ℝ :=
  ∑ x : ι, jointProbability p rho M x outcome

noncomputable def classicalMutualInformation {ι y d : Type*}
    [Fintype ι] [Fintype y] [DecidableEq y] [Fintype d] [DecidableEq d]
    (p : ι → ℝ) (rho : ι → State d) (M : POVM y d) : ℝ :=
  ∑ x : ι, ∑ outcome : y,
    let joint := jointProbability p rho M x outcome
    if joint = 0 then
      0
    else
      joint * log2 (joint / (p x * outcomeProbability p rho M outcome))

def HolevoBoundForMeasurement {ι y d : Type*}
    [Fintype ι] [Fintype y] [DecidableEq y] [Fintype d] [DecidableEq d]
    (p : ι → ℝ) (rho : ι → State d) (average : State d) (M : POVM y d) : Prop :=
  classicalMutualInformation p rho M ≤
    vonNeumannEntropyMatrix average.matrix -
      ∑ x : ι, p x * vonNeumannEntropyMatrix (rho x).matrix

end

end QITBench.HolevoBoundClassicalCapacityNQubits
