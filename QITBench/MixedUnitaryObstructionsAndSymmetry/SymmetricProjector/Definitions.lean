module

public import QITBench.Base

/-!
# Symmetric Projector

The symmetric projector is the average of a unitary permutation representation
on an abstract tensor-power carrier.
-/

@[expose] public section

namespace QITBench.SymmetricProjector

open scoped BigOperators

noncomputable section

def IsPermutationRepresentation
    {n : ℕ}
    {H V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (simpleTensor : (Fin n → H) → V)
    (W : Equiv.Perm (Fin n) → V →ₗ[ℂ] V) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (ψ : Fin n → H),
    W π (simpleTensor ψ) = simpleTensor (fun i => ψ (π.symm i))

def IsUnitaryRepresentation
    {n : ℕ}
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (W : Equiv.Perm (Fin n) → V →ₗ[ℂ] V) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x y : V),
    inner ℂ (W π x) (W π y) = inner ℂ x y

def IsGroupRepresentation
    {n : ℕ}
    {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (W : Equiv.Perm (Fin n) → V →ₗ[ℂ] V) : Prop :=
  W 1 = LinearMap.id ∧
    ∀ π σ : Equiv.Perm (Fin n), W (π * σ) = (W π).comp (W σ)

noncomputable def symmetricProjector
    (n : ℕ)
    (V : Type*)
    [AddCommMonoid V] [Module ℂ V]
    (W : Equiv.Perm (Fin n) → V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  ((Nat.factorial n : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin n), W π

def IsOrthogonalProjector
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (P : V →ₗ[ℂ] V) : Prop :=
  P.comp P = P ∧ ∀ x y : V, inner ℂ (P x) y = inner ℂ x (P y)

end

end QITBench.SymmetricProjector
