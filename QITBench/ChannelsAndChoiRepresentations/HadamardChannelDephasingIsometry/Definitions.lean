module

public import QITBench.Base

/-!
# Hadamard Channel from a Dephasing Isometry

The environment trace is the Base `partialTraceB`; positivity of the Hadamard
matrix is expressed by `Matrix.PosSemidef`.
-/

@[expose] public section

namespace QITBench.HadamardChannelDephasingIsometry

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

noncomputable def dephasingIsometry {d : ℕ} {E : Type*}
    (eta : Fin d → E → ℂ) :
    Matrix (Fin d × E) (Fin d) ℂ :=
  fun x j => if x.1 = j then eta j x.2 else 0

noncomputable def dephasingChannel {d : ℕ} {E : Type*} [Fintype E]
    (eta : Fin d → E → ℂ)
    (rho : CMatrix (Fin d)) :
    CMatrix (Fin d) :=
  let U := dephasingIsometry eta
  partialTraceB (a := Fin d) (b := E) (U * rho * U.conjTranspose)

noncomputable def environmentGram {d : ℕ} {E : Type*} [Fintype E]
    (eta : Fin d → E → ℂ) :
    CMatrix (Fin d) :=
  fun i j => ∑ e : E, eta i e * star (eta j e)

noncomputable def schurProduct {d : ℕ}
    (H rho : CMatrix (Fin d)) :
    CMatrix (Fin d) :=
  fun i j => H i j * rho i j

end

end QITBench.HadamardChannelDephasingIsometry
