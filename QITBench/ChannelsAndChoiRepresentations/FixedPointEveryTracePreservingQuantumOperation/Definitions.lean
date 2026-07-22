module

public import QITBench.Base

/-!
# Fixed Point of a Trace-Preserving Quantum Operation

Every CPTP channel `E` on a finite-dimensional system admits a density-matrix
fixed point, by the Krylov--Bogolyubov (Cesàro-average) argument: form the orbit
under `E`, average it, extract a convergent subsequence from the bounded
density-matrix set, and conclude the limit is fixed via the telescoping identity
and continuity of `E`.
-/

@[expose] public section

namespace QITBench.FixedPointEveryTracePreservingQuantumOperation

noncomputable section

end

end QITBench.FixedPointEveryTracePreservingQuantumOperation
