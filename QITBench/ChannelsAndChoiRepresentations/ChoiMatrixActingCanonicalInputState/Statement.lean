module

public import QITBench.ChannelsAndChoiRepresentations.ChoiMatrixActingCanonicalInputState.Definitions
@[expose] public section

namespace QITBench.ChoiMatrixActingCanonicalInputState

noncomputable section

theorem main
    {A Ap B : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype Ap] [DecidableEq Ap]
    [Fintype B] [DecidableEq B]
    (e : A ≃ Ap)
    (N : Channel Ap B)
    (_rho : State A)
    (rhoSqrt : CMatrix A)
    (_h_sqrt : rhoSqrt * rhoSqrt = _rho.matrix) :
    ((Channel.idChannel A).prod N).map (canonicalInputState e rhoSqrt) =
      (Matrix.kronecker rhoSqrt (1 : CMatrix B)) *
        choiMatrix e N *
        (Matrix.kronecker rhoSqrt (1 : CMatrix B)) := by
  sorry

end

end QITBench.ChoiMatrixActingCanonicalInputState
