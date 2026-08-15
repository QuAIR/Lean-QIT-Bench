/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.Base

@[expose] public section

namespace QITBench.DimensionAntisymmetricSubspaceThreeCopies

noncomputable section

abbrev TensorCube (H : Type*) := H × H × H

def tensorCubeGet {H : Type*} (x : TensorCube H) : Fin 3 → H
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2

def tensorCubeOfGet {H : Type*} (f : Fin 3 → H) : TensorCube H :=
  (f 0, f 1, f 2)

def permuteTensorCube {H : Type*} (π : Equiv.Perm (Fin 3)) (x : TensorCube H) :
    TensorCube H :=
  tensorCubeOfGet fun i => tensorCubeGet x (π i)

noncomputable def permutationSignThree (π : Equiv.Perm (Fin 3)) : ℂ :=
  (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ)

def IsAntisymmetricTensorThree {H : Type*} (v : TensorCube H → ℂ) : Prop :=
  ∀ π : Equiv.Perm (Fin 3), ∀ x : TensorCube H,
    v (permuteTensorCube π x) = permutationSignThree π * v x

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

noncomputable def antisymmetricSubspaceDimensionThreeCopies
    (H : Type*) [Fintype H] : ℕ :=
  Module.finrank ℂ (antisymmetricSubspaceThreeCopies H)

end

end QITBench.DimensionAntisymmetricSubspaceThreeCopies
