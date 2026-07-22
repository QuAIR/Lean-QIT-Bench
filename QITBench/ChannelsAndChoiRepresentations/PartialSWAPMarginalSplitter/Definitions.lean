module

public import QITBench.Base

/-!
# Partial-SWAP Marginal Splitter

The input qubit density operator is a `State`; the two output marginals use Base
partial traces.
-/

@[expose] public section

namespace QITBench.PartialSWAPMarginalSplitter

noncomputable section

def IsUnitaryMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (U : CMatrix d) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

noncomputable def maximallyMixedQubit : CMatrix (Fin 2) :=
  ((1 / 2 : ℂ) • (1 : CMatrix (Fin 2)))

noncomputable def inputState (rho : State (Fin 2)) :
    CMatrix (Fin 2 × Fin 2) :=
  Matrix.kronecker maximallyMixedQubit rho.matrix

noncomputable def swapQubits :
    CMatrix (Fin 2 × Fin 2) :=
  fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

noncomputable def partialSWAP :
    CMatrix (Fin 2 × Fin 2) :=
  let c : ℂ := (1 : ℂ) / (Real.sqrt 2 : ℂ)
  c • (1 : CMatrix (Fin 2 × Fin 2)) +
    (c * Complex.I) • swapQubits

noncomputable def evolve
    (V : CMatrix (Fin 2 × Fin 2))
    (omega : CMatrix (Fin 2 × Fin 2)) :
    CMatrix (Fin 2 × Fin 2) :=
  V * omega * V.conjTranspose

noncomputable def splitterMarginal
    (rho : State (Fin 2)) :
    CMatrix (Fin 2) :=
  ((1 / 2 : ℂ) • rho.matrix) +
    ((1 / 4 : ℂ) • (1 : CMatrix (Fin 2)))

end

end QITBench.PartialSWAPMarginalSplitter
