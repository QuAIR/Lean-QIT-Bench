module

public import QITBench.MixedUnitaryObstructionsAndSymmetry.NoMaximallyEntangledVectorQutritAntisymmetricSubspace.Definitions
@[expose] public section

namespace QITBench.NoMaximallyEntangledVectorQutritAntisymmetricSubspace

noncomputable section

theorem main :
    (∀ psi : PureVector (Fin 3 × Fin 3),
      LiesInQutritAntisymmetricSubspace psi ↔
        transposeMatrix (coefficientMatrix psi) =
          -(coefficientMatrix psi)) ∧
      ¬ ∃ psi : PureVector (Fin 3 × Fin 3),
        LiesInQutritAntisymmetricSubspace psi ∧
          IsMaximallyEntangledVector psi := by
  sorry

end

end QITBench.NoMaximallyEntangledVectorQutritAntisymmetricSubspace
