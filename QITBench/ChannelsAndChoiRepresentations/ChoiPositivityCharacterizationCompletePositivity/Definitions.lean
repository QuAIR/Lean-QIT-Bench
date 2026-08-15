/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.ChoiPositivityCharacterizationCompletePositivity

open scoped ComplexOrder MatrixOrder

noncomputable section

def IsPositiveMap {A B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (Phi : MatrixMap A B) : Prop :=
  ∀ X : CMatrix A, X.PosSemidef → (Phi X).PosSemidef

def IsCompletelyPositiveOnAllReferences {A B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (Phi : MatrixMap A B) : Prop :=
  ∀ (R : Type*) [Fintype R] [DecidableEq R],
    IsPositiveMap (MatrixMap.kron (Channel.idChannel R).map Phi)

noncomputable def relabeledChoiMatrix {A Ap B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype Ap] [DecidableEq Ap]
    [Fintype B] [DecidableEq B]
    (e : A ≃ Ap)
    (Phi : MatrixMap Ap B) :
    CMatrix (A × B) :=
  (MatrixMap.choi Phi).submatrix
    (fun x : A × B => (e x.1, x.2))
    (fun x : A × B => (e x.1, x.2))

end

end QITBench.ChoiPositivityCharacterizationCompletePositivity
