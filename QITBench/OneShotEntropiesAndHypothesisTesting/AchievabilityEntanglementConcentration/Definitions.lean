module

public import QITBench.Base.OneShot

/-!
# Achievability of Entanglement Concentration

The statement is over concrete bipartite pure states, tensor powers, CPTP
channels, the standard maximally entangled density, and matrix fidelity.  The old
version quantified over arbitrary channel application and fidelity functions,
which made the theorem false under universal instantiation.
-/

@[expose] public section

namespace QITBench.AchievabilityEntanglementConcentration

open scoped BigOperators
open QITBench.OneShot

noncomputable section

end

end QITBench.AchievabilityEntanglementConcentration
