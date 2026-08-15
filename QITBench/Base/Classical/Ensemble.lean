/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.State
public import QITBench.Base.Util.Matrix
public import Mathlib.Data.NNReal.Basic

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QITBench

universe u v w

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

structure Ensemble (ι : Type u) (a : Type v) [Fintype ι] [Fintype a] [DecidableEq a] where

  probs : ι → ℝ≥0

  weights_sum : (∑ i, probs i) = 1

  states : ι → State a

namespace Ensemble

variable {E : Ensemble ι a}

def relabelIndex {κ : Type w} [Fintype κ]
    (E : Ensemble ι a) (e : κ ≃ ι) : Ensemble κ a where
  probs k := E.probs (e k)
  weights_sum := by
    calc
      ∑ k, E.probs (e k) = ∑ i, E.probs i :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := E.weights_sum
  states k := E.states (e k)

@[simp]
theorem relabelIndex_probs {κ : Type w} [Fintype κ]
    (E : Ensemble ι a) (e : κ ≃ ι) (k : κ) :
    (E.relabelIndex e).probs k = E.probs (e k) :=
  rfl

@[simp]
theorem relabelIndex_states {κ : Type w} [Fintype κ]
    (E : Ensemble ι a) (e : κ ≃ ι) (k : κ) :
    (E.relabelIndex e).states k = E.states (e k) :=
  rfl

theorem prob_nonneg (E : Ensemble ι a) (i : ι) : 0 ≤ (E.probs i : ℝ) :=
  NNReal.coe_nonneg (E.probs i)

theorem prob_le_one [DecidableEq ι] (E : Ensemble ι a) (i : ι) :
    (E.probs i : ℝ) ≤ 1 := by
  have hleNN : E.probs i ≤ 1 := by
    calc
      E.probs i ≤ ∑ j : ι, E.probs j :=
        Finset.single_le_sum (fun _ _ => by exact bot_le) (Finset.mem_univ i)
      _ = 1 := E.weights_sum
  exact_mod_cast hleNN

def averageState (E : Ensemble ι a) : State a where
  matrix := ∑ i, (E.probs i) • (E.states i).matrix
  pos := by
    exact Matrix.posSemidef_sum Finset.univ fun i _ =>
      (E.states i).pos.smul (NNReal.coe_nonneg (E.probs i))
  trace_eq_one := by
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    rw [show (∑ i, E.probs i • ((E.states i).matrix.trace)) =
          (∑ i, E.probs i • (1 : ℂ)) from by
          congr 1; ext i; rw [(E.states i).trace_eq_one]]
    rw [Finset.sum_congr rfl fun i _ => (Algebra.algebraMap_eq_smul_one _).symm]
    rw [← map_sum (algebraMap ℝ≥0 ℂ) E.probs Finset.univ, E.weights_sum, map_one]

@[simp]
theorem averageState_matrix (E : Ensemble ι a) :
    E.averageState.matrix = ∑ i, (E.probs i) • (E.states i).matrix := by
  rfl

@[simp]
theorem relabelIndex_averageState {κ : Type w} [Fintype κ]
    (E : Ensemble ι a) (e : κ ≃ ι) :
    (E.relabelIndex e).averageState = E.averageState := by
  apply State.ext
  rw [averageState_matrix, averageState_matrix]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem averageState_of_constant (E : Ensemble ι a) (σ : State a)
    (h : ∀ i, E.states i = σ) : E.averageState = σ := by
  apply State.ext
  rw [averageState_matrix,
      Finset.sum_congr rfl fun i _ => by rw [h i],
      ← Finset.sum_smul,
      E.weights_sum, one_smul]

theorem averageState_singleton [DecidableEq ι]
    (E : Ensemble ι a) (hcard : Fintype.card ι = 1) (i : ι) :
    E.averageState = E.states i := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
  have hxi : x = i := (hx i).symm
  have hunique : ∀ j, j = i := fun j => (hx j).trans hxi
  have huniv : (Finset.univ : Finset ι) = {i} := by
    ext j; simp [hunique j]
  have hwt : E.probs i = 1 := by
    have hsum : ∑ j, E.probs j = E.probs i := by
      rw [huniv]; simp
    exact hsum.symm.trans E.weights_sum
  apply State.ext
  rw [averageState_matrix, huniv, Finset.sum_singleton, hwt, one_smul]

end Ensemble

end

end QITBench
