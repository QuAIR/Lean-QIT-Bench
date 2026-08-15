/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base.Pure
public import QITBench.Base.States.MaximallyEntangled
public import QITBench.Base.States.MaximallyMixed
public import QITBench.Base.States.Purification.Equivalence
public import QITBench.Base.States.Purification.Predicate
public import QITBench.Base.States.PosSqrt

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QITBench

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace State

def canonicalPurificationAmp (ρ : State a) : Prod a a → ℂ :=
  fun (i, j) => ρ.sqrtMatrix j i

theorem canonicalPurification_matrix (ρ : State a) :
    partialTraceA (rankOneMatrix ρ.canonicalPurificationAmp) = ρ.matrix := by
  ext j j'
  simp only [partialTraceA, rankOneMatrix_apply, State.canonicalPurificationAmp]
  rw [← ρ.sqrtMatrix_mul_self, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ρ.sqrtMatrix_isHermitian.apply i j']

def canonicalPurification (ρ : State a) : PureVector (Prod a a) where
  amp := ρ.canonicalPurificationAmp
  trace_rankOne_eq_one := by
    rw [← partialTraceA_trace (rankOneMatrix ρ.canonicalPurificationAmp),
        canonicalPurification_matrix]
    exact ρ.trace_eq_one

theorem canonicalPurification_purifies (ρ : State a) :
    ρ.canonicalPurification.Purifies ρ := by
  rw [PureVector.purifies_iff, PureVector.state_matrix]
  exact canonicalPurification_matrix ρ

theorem canonicalPurification_maximallyMixed [Nonempty a] :
    canonicalPurification (maximallyMixed a) =
      PureVector.maximallyEntangled (Equiv.refl a) := by
  apply PureVector.ext_amp
  funext x
  rcases x with ⟨i, j⟩
  by_cases h : i = j
  · subst j
    simp [canonicalPurification, canonicalPurificationAmp,
      State.maximallyMixed_sqrtMatrix, PureVector.maximallyEntangled_amp]
  · have h' : ¬ j = i := by
      intro hji
      exact h hji.symm
    simp [canonicalPurification, canonicalPurificationAmp,
      State.maximallyMixed_sqrtMatrix, PureVector.maximallyEntangled_amp, h, h']

end State

end

end QITBench
