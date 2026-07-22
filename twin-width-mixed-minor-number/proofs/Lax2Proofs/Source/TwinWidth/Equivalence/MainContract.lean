import Lax2Proofs.Source.TwinWidth.Equivalence.Main

/-!
# Contract statement for the main equivalence theorem

This file exposes the final graph-parameter statement: twin-width and mixed
minor number are functionally equivalent for finite simple graphs.
-/

namespace Lax2Proofs.TwinWidth
namespace MainContract

/-- Twin-width and mixed minor number are functionally equivalent finite-graph
parameters. -/
theorem twin_width_functionally_equivalent_mixed_minor_number :
    FunctionallyEquivalent SimpleGraph.twinWidth SimpleGraph.mixedMinorNumber := by
  exact TwinWidth.twinWidth_functionallyEquivalent_mixedMinorNumber

end MainContract
end Lax2Proofs.TwinWidth
