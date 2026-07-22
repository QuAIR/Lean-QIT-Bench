module

public import QITBench.ChannelsAndChoiRepresentations.HadamardChannelDephasingIsometry.Definitions
@[expose] public section

namespace QITBench.HadamardChannelDephasingIsometry

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {d : ℕ} {E : Type*} [Fintype E]
    (eta : Fin d → E → ℂ)
    (hη_unit : ∀ i : Fin d, (∑ e : E, Complex.normSq (eta i e)) = 1) :
    ∃ H : CMatrix (Fin d),
      H.PosSemidef ∧
        (∀ i : Fin d, H i i = 1) ∧
        (∀ rho : CMatrix (Fin d),
          dephasingChannel eta rho = schurProduct H rho) := by
  sorry

end

end QITBench.HadamardChannelDephasingIsometry
