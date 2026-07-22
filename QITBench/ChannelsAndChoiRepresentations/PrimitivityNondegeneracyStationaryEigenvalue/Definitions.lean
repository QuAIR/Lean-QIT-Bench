module

public import QITBench.Base

/-!
# Primitivity and Nondegeneracy of the Stationary Eigenvalue

The CPTP hypothesis is carried by `Channel`; primitivity is stated over iterated
application to bundled states.
-/

@[expose] public section

namespace QITBench.PrimitivityNondegeneracyStationaryEigenvalue

open scoped BigOperators ComplexOrder MatrixOrder ComplexStarModule

noncomputable section

noncomputable def quadraticForm {d : Type*} [Fintype d]
    (M : CMatrix d) (x : d → ℂ) : ℂ :=
  ∑ i : d, star (x i) * ∑ j : d, M i j * x j

def IsPositiveDefiniteMatrix {d : Type*} [Fintype d]
    (M : CMatrix d) : Prop :=
  M.conjTranspose = M ∧
    ∀ x : d → ℂ, x ≠ 0 → 0 < Complex.re (quadraticForm M x)

def iterateChannel {d : Type*} [Fintype d] [DecidableEq d]
    (E : Channel d d) :
    ℕ → State d → State d
  | 0 => fun rho => rho
  | n + 1 => fun rho => E.applyState (iterateChannel E n rho)

def IsPrimitive {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (E : Channel d d) : Prop :=
  ∃ n : ℕ, 0 < n ∧
    ∀ rho : State d,
      IsPositiveDefiniteMatrix (iterateChannel E n rho).matrix

def EigenvalueOneNondegenerate {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (E : Channel d d) : Prop :=
  ∃ sigma : CMatrix d,
    sigma ≠ 0 ∧ E.map sigma = sigma ∧
      ∀ tau : CMatrix d, E.map tau = tau → ∃ c : ℂ, tau = c • sigma

end

end QITBench.PrimitivityNondegeneracyStationaryEigenvalue
