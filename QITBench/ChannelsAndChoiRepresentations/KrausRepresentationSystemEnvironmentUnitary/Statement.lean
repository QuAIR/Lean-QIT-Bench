module

public import QITBench.ChannelsAndChoiRepresentations.KrausRepresentationSystemEnvironmentUnitary.Definitions
@[expose] public section

namespace QITBench.KrausRepresentationSystemEnvironmentUnitary

open scoped BigOperators

noncomputable section

theorem main :
    (∀ rho : CMatrix (Fin 2),
      reducedChannel rho = krausChannel rho) ∧
      (∀ k : Fin 2,
        krausOperator k =
          fun i j => U (i, k) (j, 0)) ∧
      (∑ k : Fin 2,
        (krausOperator k).conjTranspose * krausOperator k) =
          (1 : CMatrix (Fin 2)) := by
  sorry

end

end QITBench.KrausRepresentationSystemEnvironmentUnitary
