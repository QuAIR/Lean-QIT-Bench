module

public import QITBench.Base

/-!
# Channel Fidelity and Gate Fidelity for a Pure Input State

The Kraus channel and pure input are expressed through the QITBench Base
primitives `MatrixMap.ofKraus`, `PureVector`, and `rankOneMatrix`.  The equality
for pure inputs does not require selecting a preferred Kraus representation.
-/

@[expose] public section

namespace QITBench.ChannelFidelityGateFidelityPureInputState

open scoped BigOperators

noncomputable section

noncomputable def krausChannel
    {m n : ℕ}
    (E : Fin (m + 1) → CMatrix (Fin n)) : MatrixMap (Fin n) (Fin n) :=
  MatrixMap.ofKraus E

noncomputable def entanglementFidelity
    {m n : ℕ}
    (rho : State (Fin n))
    (E : Fin (m + 1) → CMatrix (Fin n)) : ℂ :=
  ∑ i, Matrix.trace (rho.matrix * E i) * star (Matrix.trace (rho.matrix * E i))

noncomputable def effectiveKraus
    {m n : ℕ}
    (U : CMatrix (Fin n))
    (E : Fin (m + 1) → CMatrix (Fin n))
    (i : Fin (m + 1)) : CMatrix (Fin n) :=
  U.conjTranspose * E i

noncomputable def pureStateGateFidelity
    {m n : ℕ}
    (psi : PureVector (Fin n))
    (U : CMatrix (Fin n))
    (E : Fin (m + 1) → CMatrix (Fin n)) : ℂ :=
  let M := U.conjTranspose * (krausChannel E) psi.state.matrix * U
  ∑ i, ∑ j, star (psi.amp i) * M i j * psi.amp j

def IsUnitaryMatrix
    {n : ℕ}
    (U : CMatrix (Fin n)) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

end

end QITBench.ChannelFidelityGateFidelityPureInputState
