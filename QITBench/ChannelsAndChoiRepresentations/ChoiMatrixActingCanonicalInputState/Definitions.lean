/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.ChoiMatrixActingCanonicalInputState

noncomputable section

noncomputable def canonicalGammaKet {A Ap : Type*} [DecidableEq Ap]
    (e : A ≃ Ap) : A × Ap → ℂ :=
  fun x => if e x.1 = x.2 then 1 else 0

noncomputable def canonicalGamma {A Ap : Type*} [DecidableEq Ap]
    (e : A ≃ Ap) : CMatrix (A × Ap) :=
  rankOneMatrix (canonicalGammaKet e)

noncomputable def choiMatrix {A Ap B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype Ap] [DecidableEq Ap]
    [Fintype B] [DecidableEq B]
    (e : A ≃ Ap)
    (N : Channel Ap B) :
    CMatrix (A × B) :=
  (MatrixMap.choi N.map).submatrix
    (fun x : A × B => (e x.1, x.2))
    (fun x : A × B => (e x.1, x.2))

noncomputable def canonicalInputState {A Ap : Type*}
    [Fintype A] [Fintype Ap] [DecidableEq Ap]
    (e : A ≃ Ap)
    (rhoSqrt : CMatrix A) :
    CMatrix (A × Ap) :=
  let left := Matrix.kronecker rhoSqrt (1 : CMatrix Ap)
  left * canonicalGamma e * left

end

end QITBench.ChoiMatrixActingCanonicalInputState
