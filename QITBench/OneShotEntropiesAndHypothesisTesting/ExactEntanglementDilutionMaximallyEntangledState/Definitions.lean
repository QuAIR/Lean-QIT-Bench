module

public import QITBench.Base.OneShot

/-!
# Exact Entanglement Dilution to a Maximally Entangled State

Nielsen's deterministic pure-state LOCC criterion is encoded directly as
majorization of Schmidt vectors.  This removes the previous unconstrained
`CanTransformDeterministicallyByLOCC` predicate while keeping the theorem's
mathematical content: for a rank-`M` maximally entangled target, majorization is
equivalent to bounding the largest Schmidt coefficient by `1/M`.
-/

@[expose] public section

namespace QITBench.ExactEntanglementDilutionMaximallyEntangledState

open QITBench.OneShot

noncomputable section

end

end QITBench.ExactEntanglementDilutionMaximallyEntangledState
