module

public import QITBench.Base

/-!
# Antisymmetric Projector

The antisymmetric projector is the signed average of a unitary permutation
representation.
-/

@[expose] public section

namespace QITBench.AntisymmetricProjector

open scoped BigOperators

noncomputable section

def IsUnitaryMatrix {d : Type*} [Fintype d] [DecidableEq d]
    (U : CMatrix d) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

def IsOrthogonalProjector {d : Type*} [Fintype d]
    (P : CMatrix d) : Prop :=
  P.conjTranspose = P ∧ P * P = P

def IsSignedPermutationRepresentation
    {d : Type*} [Fintype d] [DecidableEq d] (n : ℕ)
    (W : Equiv.Perm (Fin n) → CMatrix d)
    (sgn : Equiv.Perm (Fin n) → ℂ) : Prop :=
  (∀ pi : Equiv.Perm (Fin n), IsUnitaryMatrix (W pi)) ∧
    (∀ pi sigma : Equiv.Perm (Fin n),
      W (pi * sigma) = W pi * W sigma) ∧
      (∀ pi sigma : Equiv.Perm (Fin n),
        sgn (pi * sigma) = sgn pi * sgn sigma) ∧
        (∀ pi : Equiv.Perm (Fin n), sgn pi = 1 ∨ sgn pi = -1)

noncomputable def antisymmetricProjector
    {d : Type*} [Fintype d] [DecidableEq d] (n : ℕ)
    (W : Equiv.Perm (Fin n) → CMatrix d)
    (sgn : Equiv.Perm (Fin n) → ℂ) :
    CMatrix d :=
  (1 / (Nat.factorial n : ℂ)) •
    (∑ pi : Equiv.Perm (Fin n), sgn pi • W pi)

end

end QITBench.AntisymmetricProjector
