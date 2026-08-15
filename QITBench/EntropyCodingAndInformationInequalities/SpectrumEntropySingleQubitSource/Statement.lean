/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QITBench.EntropyCodingAndInformationInequalities.SpectrumEntropySingleQubitSource.Definitions
@[expose] public section

namespace QITBench.SpectrumEntropySingleQubitSource

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

theorem main :
    HasEigenvalue rho (lambdaPlus : ℂ) ∧
      HasEigenvalue rho (lambdaMinus : ℂ) ∧
        vonNeumannEntropy rho =
          -lambdaPlus * log2 lambdaPlus - lambdaMinus * log2 lambdaMinus := by
  sorry

end

end QITBench.SpectrumEntropySingleQubitSource
