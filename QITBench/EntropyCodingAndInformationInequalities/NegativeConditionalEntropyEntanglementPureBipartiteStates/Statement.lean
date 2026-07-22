module

public import QITBench.EntropyCodingAndInformationInequalities.NegativeConditionalEntropyEntanglementPureBipartiteStates.Definitions
@[expose] public section

namespace QITBench.NegativeConditionalEntropyEntanglementPureBipartiteStates

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (psi : PureVector (a × b)) :
    IsEntangledPureState psi ↔
      conditionalEntropyBGivenA psi.state.matrix < 0 := by
  sorry

end

end QITBench.NegativeConditionalEntropyEntanglementPureBipartiteStates
