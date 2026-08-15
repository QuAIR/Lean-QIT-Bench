/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Fidelity.TraceDistance

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace QITBench.Fidelity

universe u v

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]
variable {b : Type v} [Fintype b] [DecidableEq b]

def IsPurification (psi : PureVector (a × b)) (rho : State a) : Prop :=
  psi.state.marginalA = rho

def canonicalPurificationAmp (rho : State a) : a × a → ℂ :=
  fun ij => matrixSqrt rho.matrix ij.1 ij.2

private theorem matrixSqrt_conjTranspose (rho : State a) :
    (matrixSqrt rho.matrix).conjTranspose = matrixSqrt rho.matrix := by
  rw [← Matrix.star_eq_conjTranspose]
  exact (CFC.sqrt_nonneg rho.matrix).star_eq

theorem partialTraceB_rankOne_canonicalPurificationAmp (rho : State a) :
    partialTraceB (rankOneMatrix (canonicalPurificationAmp rho)) = rho.matrix := by
  let S : CMatrix a := matrixSqrt rho.matrix
  have hSstar : S.conjTranspose = S := matrixSqrt_conjTranspose rho
  have hsquare : S * S = rho.matrix := by
    exact CFC.sqrt_mul_sqrt_self rho.matrix rho.pos.nonneg
  ext i i'
  calc
    partialTraceB (rankOneMatrix (canonicalPurificationAmp rho)) i i' =
        ∑ j, S i j * star (S i' j) := by
      rfl
    _ = ∑ j, S i j * S j i' := by
      apply Finset.sum_congr rfl
      intro j _
      have hentry := congr_fun (congr_fun hSstar j) i'
      simpa [Matrix.conjTranspose_apply] using congrArg (fun z => S i j * z) hentry
    _ = (S * S) i i' := by rw [Matrix.mul_apply]
    _ = rho.matrix i i' := by rw [hsquare]

def canonicalPurification (rho : State a) : PureVector (a × a) where
  amp := canonicalPurificationAmp rho
  trace_rankOne_eq_one := by
    calc
      (rankOneMatrix (canonicalPurificationAmp rho)).trace =
          (partialTraceB (rankOneMatrix (canonicalPurificationAmp rho))).trace :=
        (partialTraceB_trace
          (a := a) (b := a) (rankOneMatrix (canonicalPurificationAmp rho))).symm
      _ = rho.matrix.trace := by
        rw [partialTraceB_rankOne_canonicalPurificationAmp]
      _ = 1 := rho.trace_eq_one

@[simp]
theorem canonicalPurification_marginalA (rho : State a) :
    (canonicalPurification rho).state.marginalA = rho := by
  apply State.ext
  exact partialTraceB_rankOne_canonicalPurificationAmp rho

theorem canonicalPurification_isPurification (rho : State a) :
    IsPurification (canonicalPurification rho) rho :=
  canonicalPurification_marginalA rho

theorem exists_purification (rho : State a) :
    ∃ psi : PureVector (a × a), IsPurification psi rho :=
  ⟨canonicalPurification rho, canonicalPurification_isPurification rho⟩

def partialTraceBKraus (j : b) : Matrix a (a × b) ℂ :=
  fun i x => if x = (i, j) then 1 else 0

theorem ofKraus_partialTraceBKraus (X : CMatrix (a × b)) :
    MatrixMap.ofKraus (partialTraceBKraus (a := a) (b := b)) X = partialTraceB X := by
  ext i i'
  change ((∑ j, partialTraceBKraus j * X * (partialTraceBKraus j).conjTranspose) :
      CMatrix a) i i' = ∑ j, X (i, j) (i', j)
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [partialTraceBKraus, Matrix.mul_apply]

def partialTraceBChannel : Channel (a × b) a where
  map := MatrixMap.ofKraus (partialTraceBKraus (a := a) (b := b))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := by
    intro X
    rw [ofKraus_partialTraceBKraus, partialTraceB_trace]
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

@[simp]
theorem partialTraceBChannel_apply (X : CMatrix (a × b)) :
    partialTraceBChannel.map X = partialTraceB X :=
  ofKraus_partialTraceBKraus X

theorem traceDistance_partialTraceB_mono (rho sigma : State (a × b)) :
    traceDistance rho.marginalA.matrix sigma.marginalA.matrix ≤
      traceDistance rho.matrix sigma.matrix := by
  change traceDistance (partialTraceB rho.matrix) (partialTraceB sigma.matrix) ≤
    traceDistance rho.matrix sigma.matrix
  rw [← partialTraceBChannel_apply, ← partialTraceBChannel_apply]
  exact traceDistance_channel_mono rho sigma (partialTraceBChannel (a := a) (b := b))

end

end QITBench.Fidelity
