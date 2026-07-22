module

public import QITBench.Base

/-!
# Choi Positivity Characterizes Complete Positivity

Complete positivity is stated in the source sense: `id_R ⊗ Φ` is positive for
every finite reference system `R`.  This is deliberately separate from
`MatrixMap.IsCompletelyPositive`, whose Base definition is Choi-positivity and
would make the benchmark theorem circular.
-/

@[expose] public section

namespace QITBench.ChoiPositivityCharacterizationCompletePositivity

open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Positivity of a finite-dimensional matrix map. -/
def IsPositiveMap {A B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (Phi : MatrixMap A B) : Prop :=
  ∀ X : CMatrix A, X.PosSemidef → (Phi X).PosSemidef

/-- Complete positivity by tensoring with every finite reference identity map. -/
def IsCompletelyPositiveOnAllReferences {A B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (Phi : MatrixMap A B) : Prop :=
  ∀ (R : Type*) [Fintype R] [DecidableEq R],
    IsPositiveMap (MatrixMap.kron (Channel.idChannel R).map Phi)

/-- Choi matrix after relabeling the input copy `A'` back to `A`. -/
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
