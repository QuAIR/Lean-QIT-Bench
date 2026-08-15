/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.QuantumFanoInequality

open scoped BigOperators

noncomputable section

noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

def IsPurification {d : Type*} [Fintype d] [DecidableEq d]
    (rhoA : State d) (psi : PureVector (d × d)) : Prop :=
  partialTraceA psi.state.matrix = rhoA.matrix

noncomputable def exchangeState {d : Type*} [Fintype d] [DecidableEq d]
    (E : Channel d d)
    (psi : PureVector (d × d)) : State (d × d) :=
  ((Channel.idChannel d).prod E).applyState psi.state

noncomputable def vectorExpectation {d : Type*} [Fintype d]
    (psi : d → ℂ) (rho : CMatrix d) : ℂ :=
  ∑ i : d, ∑ j : d, star (psi i) * rho i j * psi j

noncomputable def entanglementFidelity {d : Type*} [Fintype d] [DecidableEq d]
    (E : Channel d d)
    (psi : PureVector (d × d)) : ℝ :=
  Complex.re (vectorExpectation psi.amp (exchangeState E psi).matrix)

noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  -x * log2 x - (1 - x) * log2 (1 - x)

noncomputable def vonNeumannEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (rho : State d) : ℝ :=
  -∑ i : d, rho.pos.1.eigenvalues i * log2 (rho.pos.1.eigenvalues i)

noncomputable def exchangeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (E : Channel d d)
    (psi : PureVector (d × d)) : ℝ :=
  vonNeumannEntropy (exchangeState E psi)

end

end QITBench.QuantumFanoInequality
