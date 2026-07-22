module

public import QITBench.Base

/-!
# Dimension of the Three-Copy Antisymmetric Subspace

The antisymmetric subspace is the alternating submodule for the `S₃` action on
basis labels of `H^{⊗3}`.  Its dimension is now the finrank of that submodule,
not a definition set equal to the desired binomial coefficient.
-/

@[expose] public section

namespace QITBench.DimensionAntisymmetricSubspaceThreeCopies

noncomputable section

/-- Basis labels for `H^{⊗3}`. -/
abbrev TensorCube (H : Type*) := H × H × H

/-- Read the `i`th component of a three-tensor basis label. -/
def tensorCubeGet {H : Type*} (x : TensorCube H) : Fin 3 → H
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2

/-- Assemble a three-tensor basis label from its three components. -/
def tensorCubeOfGet {H : Type*} (f : Fin 3 → H) : TensorCube H :=
  (f 0, f 1, f 2)

/-- Permutation action of `S₃` on basis labels of `H^{⊗3}`. -/
def permuteTensorCube {H : Type*} (π : Equiv.Perm (Fin 3)) (x : TensorCube H) :
    TensorCube H :=
  tensorCubeOfGet fun i => tensorCubeGet x (π i)

/-- The sign of a permutation of the three tensor factors, as a complex scalar. -/
noncomputable def permutationSignThree (π : Equiv.Perm (Fin 3)) : ℂ :=
  (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ)

/-- A vector transforming by the sign representation of `S₃`. -/
def IsAntisymmetricTensorThree {H : Type*} (v : TensorCube H → ℂ) : Prop :=
  ∀ π : Equiv.Perm (Fin 3), ∀ x : TensorCube H,
    v (permuteTensorCube π x) = permutationSignThree π * v x

/-- The antisymmetric subspace of `H^{⊗3}`. -/
noncomputable def antisymmetricSubspaceThreeCopies (H : Type*) :
    Submodule ℂ (TensorCube H → ℂ) where
  carrier := {v | IsAntisymmetricTensorThree v}
  zero_mem' := by
    intro π x
    simp [permutationSignThree]
  add_mem' := by
    intro v w hv hw π x
    simp [Pi.add_apply, hv π x, hw π x, mul_add]
  smul_mem' := by
    intro c v hv π x
    simp [Pi.smul_apply, hv π x, mul_assoc, mul_comm]

/-- Dimension of the alternating subspace. -/
noncomputable def antisymmetricSubspaceDimensionThreeCopies
    (H : Type*) [Fintype H] : ℕ :=
  Module.finrank ℂ (antisymmetricSubspaceThreeCopies H)

end

end QITBench.DimensionAntisymmetricSubspaceThreeCopies
